open Fjava

exception NotImplemented
exception TypeError
exception Stuck

(* Return list of supertypes of c specified by ct.
 * supertype : Fjava.classDecl list -> Fjava.typ -> Fjava.typ list *)
let rec supertype ct c =
    c ::
    try
        let c, d, _, _, _ = List.find (fun (c', _, _, _, _) -> c' = c) ct
        in supertype ct d
    with Not_found -> []

(* Return list of fields of c specified by ct.
 * field : Fjava.classDecl list -> Fjava.typ -> (Fjava.typ * string) list *)
let rec field ct c =
    try
        let c, d, fs, _, _ = List.find (fun (c', _, _, _, _) -> c' = c) ct
        in fs @ field ct d
    with Not_found -> []

(* Return type of m in c specified by ct.
 * mtype : Fjava.classDecl list -> string -> Fjava.typ -> Fjava.typ list * Fjava.typ *)
let rec mtype ct m c =
    try
        let c, d, _, _, ms = List.find (fun (c', _, _, _, _) -> c' = c) ct in
        try
            let c0, m, p, _ = List.find (fun (_, m', _, _) -> m' = m) ms in
            (List.map (fun (x, _) -> x) p), c0
        with Not_found -> mtype ct m d
    with Not_found -> raise TypeError

(* Return true if m is overridden well from d.
 * override : Fjava.classDecl list -> string -> Fjava.typ -> Fjava.typ list -> Fjava.typ -> bool *)
let override ct m d cs c0 =
    let ds, d0 = try mtype ct m d with TypeError -> cs, c0
    in try List.for_all2 (fun x1 x2 -> x1 = x2) (c0 :: cs) (d0 :: ds) with Invalid_argument _ -> raise TypeError

(* Return type of e.
 * Raise TypeError if e has no type.
 * typeOf2 : Fjava.classDecl list -> (string * Fjava.typ) list -> Fjava.exp -> Fjava.typ *)
let rec typeOf2 ct cxt e =
    match e with
    | Var v -> (try List.assoc v cxt with Not_found -> raise TypeError)
    | Field (e, f) ->
        let c0 = typeOf2 ct cxt e in
        let c, _ = try List.find (fun (_, f') -> f' = f) (field ct c0) with Not_found -> raise TypeError in
        c
    | Method (e, m, es) ->
        let c0 = typeOf2 ct cxt e in
        let ds, c = mtype ct m c0 in
        if (try List.for_all2 (fun e' d -> List.mem d (supertype ct (typeOf2 ct cxt e'))) es ds
            with Invalid_argument _ -> raise TypeError)
        then c else raise TypeError
    | New (t, es) ->
        if (try List.for_all2 (fun e (d, _) -> List.mem d (supertype ct (typeOf2 ct cxt e))) es (field ct t)
            with Invalid_argument _ -> raise TypeError)
        then t else raise TypeError
    | Cast (t, e) ->
        let d = typeOf2 ct cxt e in
        if (List.mem t (supertype ct d)) || (List.mem d (supertype ct t)) then t
        else let _ = Printf.printf "Stupid Warning\n" in t

(* Return true if k (constructor declaration) is okay.
 * checkConstructor : Fjava.classDecl list -> Fjava.typ -> Fjava.typ -> (Fjava.typ * string) list -> Fjava.constructorDecl -> bool *)
let checkConstructor ct c d fs k =
    let c', p, s, a = k in
    let fieldD = field ct d in
    let checkName = c = c' in
    let checkLength = List.length fieldD = List.length s && List.length fs = List.length a in
    let checkParameters = try List.for_all2 (fun x1 x2 -> x1 = x2) p (fieldD @ fs) with Invalid_argument _ -> false in
    let getSnd l = List.map (fun (_, x) -> x) l in
    let checkAssignments = List.for_all (fun (x1, x2) -> x1 = x2) a in
    let checkBody = List.for_all (fun (x1, x2) -> x1 = x2) a &&
                    (try List.for_all2 (fun x1 x2 -> x1 = x2) (getSnd p) (s @ (getSnd a)) with Invalid_argument _ -> false) in
    checkName && checkLength && checkParameters && checkAssignments && checkBody

(* Return true if all method declarations in ms is okay.
 * checkMethods : Fjava.classDecl list -> Fjava.type -> Fjava.typ -> Fjava.methodDecl list -> bool *)
let rec checkMethods ct c d ms =
    match ms with
    | [] -> true
    | (c0, m, p, b) :: t ->
        let e = typeOf2 ct (("this", c) :: List.map (fun (x1, x2) -> (x2, x1)) p) b in
        (List.mem c0 (supertype ct e)) &&
        (override ct m d (List.map (fun (x, y) -> x) p) c0) &&
        (checkMethods ct c d t)

(* Return type of p.
 * Raise TypeError if some class declaration is not okay or expression has no type.
 * typeOf : Fjava.program -> Fjava.typ *)
let typeOf p =
    let ct, e = p in
    let checkClasses = List.for_all (fun (c, d, fs, k, ms) -> (checkConstructor ct c d fs k) && (checkMethods ct c d ms)) ct in
    if checkClasses then typeOf2 ct [] e else raise TypeError

(* Substitute parameters and this in e.
 * substitute : (string * Fjava.exp) list -> Fjava.exp *)
let rec substitute cxt e =
    match e with
    | Var v -> (try List.assoc v cxt with Not_found -> raise Stuck)
    | Field (e, f) -> Field (substitute cxt e, f)
    | Method (e, m, es) -> Method (substitute cxt e, m, List.map (fun e' -> substitute cxt e') es)
    | New (t, es) -> New (t, List.map (fun e' -> substitute cxt e') es)
    | Cast (t, e) -> Cast (t, substitute cxt e)

(* Return arguments and body of m in c specified by ct.
 * mbody : Fjava.classDecl list -> string -> Fjava.typ -> string list * Fjava.typ *)
let rec mbody ct m c =
    try
        let c, d, _, _, ms = List.find (fun (c', _, _, _, _) -> c' = c) ct in
        try
            let _, m, p, b = List.find (fun (_, m', _, _) -> m' = m) ms in
            (List.map (fun (_, x) -> x) p), b
        with Not_found -> mbody ct m d
    with Not_found -> raise Stuck

(* Reduce p by one step.
 * Raise Stuck if p is not reducible.
 * step : Fjava.program -> Fjava.program *)
let step p =
    let ct, e = p
    in let rec findi x l =
        match l with
        | [] -> raise Stuck
        | h :: t -> if x = h then 0 else (findi x t) + 1
    in let rec is_reducible e =
        match e with
        | Var v -> false
        | New (t, es) -> List.exists (fun x -> is_reducible x) es
        | _ -> true
    in let rec reduciblei es =
        match es with
        | [] -> raise Stuck
        | h :: t -> if is_reducible h then 0 else (reduciblei t) + 1
    in let rec step_aux e =
        match e with
        | Var v -> raise Stuck
        | Field (New (t, es), f) ->
            (try Field (step_aux (New (t, es)), f)
            with Stuck ->
                let fs = List.map (fun (_, x) -> x) (field ct t)
                in List.nth es (findi f fs))
        | Field (e, f) -> Field (step_aux e, f)
        | Method (New (t, es), m, es') ->
            (try Method (step_aux (New (t, es)), m, es')
            with Stuck ->
                (try
                    let i = reduciblei es' in
                    Method (New (t, es), m, List.mapi (fun i' e' -> if i' = i then step_aux e' else e') es')
                with Stuck ->
                    let xs, e0 = mbody ct m t
                    in substitute (("this", New (t, es)) :: try List.combine xs es' with Invalid_argument _ -> raise Stuck) e0))
        | Method (e, m, es) -> Method (step_aux e, m, es)
        | New (t, es) ->
            let i = reduciblei es
            in New (t, List.mapi (fun i' e' -> if i' = i then step_aux e' else e') es)
        | Cast (t, New (t', es)) ->
            (try Cast (t, step_aux (New (t', es)))
            with Stuck ->
                if List.mem t (supertype ct t')
                then New (t', es) else raise Stuck)
        | Cast (t, e) -> Cast (t, step_aux e)
    in ct, step_aux e

let typeOpt p = try Some (typeOf p) with TypeError -> None
let stepOpt p = try Some (step p) with Stuck -> None
let rec multiStep p = try multiStep (step p) with Stuck -> p

let rec stepStream e =
    let rec steps e =
        match stepOpt e with
            | None -> Stream.from (fun _ -> None)
            | Some e' -> Stream.icons e' (steps e')
    in Stream.icons e (steps e)
