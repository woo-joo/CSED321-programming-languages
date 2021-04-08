module type HW4 =
sig
  exception NotImplemented
  exception Stuck

  (* one-step reduction using the call-by-value strategy, raises Stuck if impossible *)
  val stepv : Uml.exp -> Uml.exp

  (* one-step reduction using the call-by-name strategy, raises Stuck if impossible *)
  val stepn : Uml.exp -> Uml.exp

  (* ... returns NONE if impossible *)
  val stepOpt : (Uml.exp -> Uml.exp) -> Uml.exp -> Uml.exp option

  (* repeats step as many times as possible *)
  val multiStep : (Uml.exp -> Uml.exp) -> Uml.exp -> Uml.exp

  (* a stream of all steps *)
  val stepStream : (Uml.exp -> Uml.exp) -> Uml.exp -> Uml.exp Stream.t
end

module S = (Evalsol : HW4)

module F (P : HW4)
  (ST : sig val name : string end) =
struct
  let _ = prerr_endline (ST.name ^ " --- ")

  open Uml
  open Loop

  exception Pass
  exception Fail

  (*******************************************)
  (* Control running time and memory:        *)
  (* - Check non-terminated functions        *)
  (* - Check stack over flow                 *)
  (*******************************************)   
  type 'a result =
  | Init
  | NonTerminated
  | StackOverflow
  | WrongImplementation
  | Stuck
  | OK of 'a
      
  let delayed_fun f x timeout =
    let ret = ref Init in
    let _ = Sys.set_signal Sys.sigalrm (Sys.Signal_handle (fun _ -> failwith "timeout")) in
    ignore (Unix.alarm timeout);
    let _ =
      try
        let r = f x in
        ignore (Unix.alarm 0); ret := OK r
      with
      | Failure "timeout" -> ret := NonTerminated
      | Stack_overflow    -> ignore (Unix.alarm 0); ret := StackOverflow
      | P.Stuck -> ret := Stuck
      | _                 -> ignore (Unix.alarm 0); ret := WrongImplementation
    in
    !ret
      
  let wrap_fun f x =
    let f' x =
      try
        let r = f x in
        OK r
      with
        Stack_overflow -> StackOverflow
      | S.Stuck -> Stuck
      | _ -> WrongImplementation
    in f' x


  (*******************)
  (* Compare results *)
  (*******************)
  let union l1 l2 = List.fold_left (fun l x -> if List.mem x l then l else x :: l)
    l1 l2

  (* the set with free variables in e *)
  let rec freeVar e =
    match e with
      Var x -> [x]
    | Lam (x, e') -> List.filter (fun y -> x <> y) (freeVar e')
    | App (e1, e2) -> union (freeVar e1) (freeVar e2)

  (* the set with bound variables in e *)
  let rec boundVar e =
    match e with
      Var x -> []
    | Lam (x, e') -> x :: boundVar e'
    | App (e1, e2) -> union (boundVar e1) (boundVar e2)


  (* variable swapping *)
  let rec swap e x y =
    match e with
      Var z -> if z = x then Var y
        else if z = y then Var x
        else Var z
    | Lam (z, e') -> let boundVar = if z = x then y
      else if z = y then x
      else z
                     in
                     Lam (boundVar, swap e' x y)
    | App (e1, e2) -> App (swap e1 x y, swap e2 x y)

  (* alpha conversion *)
  let rec alphaConv lam e' oy x =
    match lam with
      Lam (y, e'') -> let z = y ^ "'" in
                      if (z <> x && List.mem z (freeVar e')) = false && (List.mem z (boundVar e'')) = false && (List.mem z (freeVar e'')) = false
                      then Lam (z, swap e'' oy z)
                      else alphaConv (Lam (z, e'')) e' oy x
    | _ -> raise S.Stuck

  let rec is_equal e1 e2 =
    try
      match (e1, e2) with
        (Var x, Var y) -> x = y
      | (Lam (x, e), Lam (y, e')) ->
        if x = y then is_equal e e'
        else if (List.mem y (freeVar e)) = false then is_equal (swap e y x) e'
        else is_equal e1 (alphaConv e2 e y x)
      | (App (e1, e2), App (e1', e2')) -> is_equal e1 e1' && is_equal e2 e2'
      | (_, _) -> false
    with _ -> false

  let rec is_equal_stream s1 s2 =
    try
      let e1 = Stream.next s1 in
      try let e2 = Stream.next s2 in
          if is_equal e1 e2
          then is_equal_stream s1 s2
          else raise Fail
      with _ -> raise Fail
    with Stream.Failure -> (try let _ = Stream.next s2 in false
      with Stream.Failure -> true)
    | Fail -> false

  let gen_check_msg f g =
    match (f,g) with
    | (OK f', OK g') -> if is_equal_stream f' g' then (true,"OK") else (false,"Fail - Wrong result")
    | (OK _, Stuck) -> (false,"Fail - Wrong implementation")
    | (Stuck, Stuck) -> (true,"OK")
    | (OK _, StackOverflow) -> (false,"Fail - Stack overflow")
    | (StackOverflow, StackOverflow) -> (true,"OK")
    | (StackOverflow, OK _) -> (true,"OK")
    | (NonTerminated,NonTerminated) -> (false,"Alert - Both program are non-terminated, please increase running time")
    | (_,NonTerminated) -> (false,"Fail - Infinite loop")
    | (NonTerminated,_) -> (false,"Alert - Please increase running time")
    | (_,WrongImplementation) -> (false,"Fail - Wrong implementation")
    | (_,_) -> (false,"Alert - Can't happen")


  (****************)
  (* Test program *)
  (****************)

  let score = ref 0.0
  let total_score = ref 0.0
  let count = ref 0.0

  let curry2 f (x,y) = f x y	

  let n_loop = ref 0    

  let test_stepv e =
    try
      let e1 = wrap_fun (curry2 S.stepStream) (S.stepv, e) in
      let e2 = if !count < 19.0
        then delayed_fun (curry2 P.stepStream) (P.stepv, e) 1
        else delayed_fun (curry2 P.stepStream) (P.stepv, e) 3
      in
      let (r, m) = gen_check_msg e1 e2 in
      if r then raise Pass
      else prerr_endline m; raise Fail
    with Pass -> score := 1.0
    | _ -> score := 0.0

  let test_stepn e =
    try
      let e1 = wrap_fun (curry2 S.stepStream) (S.stepn, e) in
      let e2 = if !count < 39.0
        then delayed_fun (curry2 P.stepStream) (P.stepn, e) 1
        else delayed_fun (curry2 P.stepStream) (P.stepn, e) 3
      in
      let (r, m) = gen_check_msg e1 e2 in
      if r then raise Pass
      else prerr_endline m; raise Fail
    with Pass -> score := 1.0
    | _ -> score := 0.0

  let test_run action e =
    let _ = prerr_string ("test " ^ (string_of_float (!count +. 1.0)) ^ " ");
      action e in
    let _ = total_score := !total_score +. !score;
      count := !count +. 1.0
    in
    if !score = 0.0 then ()
    else prerr_endline ": pass"

  let _ = prerr_endline ("Test call-by-value")
  let _ = loopFile "testCBV.uml" (test_run test_stepv)

  let _ = prerr_endline ("Test call-by-name")
  let _ = loopFile "testCBN.uml" (test_run test_stepn)

  let _ = print_endline (ST.name ^ " " ^ (string_of_int (int_of_float (!total_score *. 100.0 /. !count))))

end;;

module Hfoo = F (Eval) (struct let name = "Test score" end);;
