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

let typeOf p = raise NotImplemented

let step p = raise NotImplemented

let typeOpt p = try Some (typeOf p) with TypeError -> None
let stepOpt p = try Some (step p) with Stuck -> None
let rec multiStep p = try multiStep (step p) with Stuck -> p

let rec stepStream e =
    let rec steps e =
        match stepOpt e with
            | None -> Stream.from (fun _ -> None)
            | Some e' -> Stream.icons e' (steps e')
    in Stream.icons e (steps e)
