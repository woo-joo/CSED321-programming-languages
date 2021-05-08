module type HW6 =
sig
  exception NotImplemented
  exception Stuck
  exception NotConvertible

  type env
  type value
  type frame

  type stoval = Computed of value | Delayed of Tml.exp * env
  and stack = Hole_SK | Frame_SK of stack * frame
  and state =
    Anal_ST of stoval Heap.heap * stack * Tml.exp * env
  | Return_ST of stoval Heap.heap * stack * value

  val emptyEnv : env
  val value2exp : value -> Tml.exp

  (* translate TML expressions into expressions with de Bruijn's index *)
  val texp2exp : Tml.texp -> Tml.exp

  (* one-step reduction, raises Stuck if impossible *)
  val step1 : Tml.exp -> Tml.exp
  val step2 : state -> state

  val exp2string : Tml.exp -> string
  val state2string : state -> string

  (* ... returns NONE if impossible *)
  val stepOpt1 : Tml.exp -> Tml.exp option
  val stepOpt2 : state -> state option

  (* repeats step as many times as possible *)
  val multiStep1 : Tml.exp -> Tml.exp
  val multiStep2 : state -> state

  (* a stream of all steps *)
  val stepStream1 : Tml.exp -> Tml.exp Stream.t
  val stepStream2 : state -> state Stream.t
end

module S = (Evalsol : HW6)

module F (P : HW6)
  (ST : sig val name : string end) =
struct
  let _ = prerr_endline (ST.name ^ " --- ")

  open Tml
  open Loop

  exception Pass
  exception Fail

  let score_total = ref 0.0
  let score_index = ref 0.0
  let score_step = ref 0.0
  let score_step2 = ref 0.0
  let score = ref 0.0
  let count = ref 0.0
  let n_loop = ref 0

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
  let rec is_equal e1 e2 =
    try
      match (e1, e2) with
        (Ind x, Ind y) -> x = y
      | (Lam e, Lam e') -> is_equal e e'
      | (App (e1, e2), App (e1', e2')) -> is_equal e1 e1' && is_equal e2 e2'
      | (Pair (e1, e2), Pair (e1', e2')) -> is_equal e1 e1' && is_equal e2 e2'
      | (Fst e, Fst e') -> is_equal e e'
      | (Snd e, Snd e') -> is_equal e e'
      | (Eunit, Eunit) -> true
      | (Inl e, Inl e') -> is_equal e e'
      | (Inr e, Inr e') -> is_equal e e'
      | (Case (e1, e2, e3), Case (e1', e2', e3')) -> is_equal e1 e1' && is_equal e2 e2' && is_equal e3 e3'
      | (Fix e, Fix e') -> is_equal e e'
      | (True, True) -> true
      | (False, False) -> true
      | (Ifthenelse (e1, e2, e3), Ifthenelse (e1', e2', e3')) -> is_equal e1 e1' && is_equal e2 e2' && is_equal e3 e3'
      | (Num x, Num y) -> x = y
      | (Plus, Plus) -> true
      | (Minus, Minus) -> true
      | (Eq, Eq) -> true
      | (_, _) -> false
    with _ -> false

  let is_equal2 e1 e2 =
    try match (e1, e2) with
      (S.Anal_ST (_, _, _, _), P.Anal_ST (_, _, _, _)) -> true
    | (S.Return_ST (_, _, v1), P.Return_ST (_, _, v2)) ->
      let e1' = try S.value2exp v1
        with S.NotConvertible -> try let _ = P.value2exp v2 in raise Fail
          with P.NotConvertible -> raise Pass in
      let e2' = try P.value2exp v2
        with P.NotConvertible -> raise Fail in
      is_equal e1' e2'
    | (_, _) -> let _ = prerr_endline "1" in false
    with Pass -> true
    | _ -> false

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

  let list_of_stream stream =
    let result = ref [] in
    Stream.iter (fun value -> result := value :: !result) stream;
    List.rev !result

  let rec is_equal_stream2 s1 s2 =
    let l1 = List.filter (function S.Return_ST (_, _, v) -> (try let _ = S.value2exp v in true with _ -> false) | _ -> false) (list_of_stream s1) in
    let l2 = List.filter (function P.Return_ST (_, _, v) -> (try let _ = P.value2exp v in true with _ -> false) | _ -> false) (list_of_stream s2) in
    let rec is_equal2_list l1 l2 =
      match (l1, l2) with
        ([], []) -> true
      | (a :: t1, b :: t2) -> if is_equal2 a b then is_equal2_list t1 t2 else false
      | (_, _) -> false
    in is_equal2_list l1 l2

  let gen_check_msg_index e1 e2 = match (e1, e2) with
      (OK e1', OK e2') -> if is_equal e1' e2' then (true,"OK") else (false,"Fail - Wrong result")
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

  let gen_check_msg e1 e2 = match (e1, e2) with
      (OK e1', OK e2') -> if is_equal_stream e1' e2' then (true,"OK") else (false,"Fail - Wrong result")
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

  let gen_check_msg2 e1 e2 = match (e1, e2) with
      (OK e1', OK e2') -> if is_equal_stream2 e1' e2' then (true,"OK") else (false,"Fail - Wrong result")
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

  let test_index e =
    let _ = count := !count +. 1.0 in
    let e1 = delayed_fun S.texp2exp e 1 in
    let e2 = delayed_fun P.texp2exp e 1 in
    let (r, m) = gen_check_msg_index e1 e2 in
    if r then let _ = score := 1.0 in prerr_endline ("test " ^ (string_of_float !count) ^ ": pass");
																			score_index := !score_index +. !score
    else prerr_endline ("test " ^ (string_of_float !count) ^ " " ^ m ^ " : fail");
		     score := 0.0

  let test_step e =
		let _ = count := !count +. 1.0 in
    let e1 = delayed_fun S.texp2exp e 1 in
    let e2 = delayed_fun P.texp2exp e 1 in
    let (r, m) = gen_check_msg_index e1 e2 in
    if r then
			let e1 = delayed_fun S.stepStream1 (S.texp2exp e) 1 in
			let e2 = delayed_fun P.stepStream1 (P.texp2exp e) 1 in
			let (r, m) = gen_check_msg e1 e2 in
			if r then
				let _ = score := 1.0 in
				prerr_endline ("test " ^ (string_of_float !count) ^ ": pass");
				score_step := !score_step +. !score
			else prerr_endline ("test " ^ (string_of_float !count) ^ " " ^ m ^ " : fail"); score := 0.0
    else prerr_endline ("test " ^ (string_of_float !count) ^ " " ^ m ^ " : fail"); score := 0.0

  let test_step2 e =
		let _ = count := !count +. 1.0 in
		let e1 = delayed_fun S.texp2exp e 1 in
    let e2 = delayed_fun P.texp2exp e 1 in
    let (r, m) = gen_check_msg_index e1 e2 in
		if r then
			let e1 = delayed_fun S.stepStream2 (S.Anal_ST (Heap.empty, S.Hole_SK, (S.texp2exp e), S.emptyEnv)) 2 in
			let e2 = delayed_fun P.stepStream2 (P.Anal_ST (Heap.empty, P.Hole_SK, (P.texp2exp e), P.emptyEnv)) 2 in
			let (r, m) = gen_check_msg2 e1 e2 in
			if r then  let _ = score := 1.0 in
								 prerr_endline ("test " ^ (string_of_float !count) ^ ": pass");
								 score_step2 := !score_step2 +. !score
			else prerr_endline ("test " ^ (string_of_float !count) ^ " " ^ m ^ " : fail"); score := 0.0
		else prerr_endline ("test " ^ (string_of_float !count) ^ " " ^ m ^ " : fail"); score := 0.0

  let _ = loopFile "part1test.tml" test_index
  let _ = let s = ceil (!score_index /. !count *. 20.0) in
          prerr_endline ("part1 score: " ^ (string_of_float s) ^ "/20");
          count := 0.0;
          score_total := !score_total +. s

  let _ = loopFile "part2test.tml" test_step
  let _ = let s = ceil (!score_step /. !count *. 30.0) in
          prerr_endline ("part2 score: " ^ (string_of_float s) ^ "/30");
          count := 0.0;
          score_total := !score_total +. s

  let _ = loopFile "part3test.tml" test_step2
  let _ = let s = ceil (!score_step2 /. !count *. 50.0) in
          prerr_endline ("part3 score: " ^ (string_of_float s) ^ "/50");
          count := 0.0;
          score_total := !score_total +. s

  let _ = print_endline (ST.name ^ " " ^ (string_of_float !score_total))
end

module Hkcs9301 = F (Eval) (struct let name = "Test score" end);;
