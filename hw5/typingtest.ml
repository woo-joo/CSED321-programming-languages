module type HW5 =
sig
  exception TypeError
  type context
  val createEmptyContext : unit -> context
  val typing : context -> Tml.exp -> Tml.tp
  val typeOf : Tml.exp -> Tml.tp
  val typeOpt : Tml.exp -> Tml.tp option
end

module S = (Typingsol : HW5)

module F (P : HW5)
  (ST : sig val name : string end) =
struct
  let _ = prerr_endline (ST.name ^ " --- ")

  open P
  open Tml
  open Loop

  let score = ref 0
  let total_score = ref 0
  let count = ref 0

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
  | Type_Error
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
      | TypeError -> ret := Type_Error
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
      | S.TypeError -> Type_Error
      | _ -> WrongImplementation
    in f' x


  (*******************)
  (* Compare results *)
  (*******************)
  let gen_check_msg f g =
    match (f,g) with
    | (OK f', OK g') -> if f' = g' then (true,"OK") else (false,"Fail - Wrong result")
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

  exception Pass
  exception Fail

  let test_type e =
    let _ = score := 5 in
    let rec test_type' e =
      let t1 = match delayed_fun typeOf e 1 with
          OK k -> Some k
        | Type_Error -> None
        | _ -> raise Fail in
      let t2 = match wrap_fun S.typeOf e with
          OK k -> Some k
        | Type_Error -> None
        | _ -> raise Fail in
      match (t1, t2) with
        (Some k1, Some k2) -> if k1 = k2 then raise Pass
      | (None, None) -> raise Pass
      | _ -> raise Fail
    in
    try test_type' e
    with Pass -> score := 10
    | _ -> score := 0

  let test_run action e =
    let _ = action e in
    let _ = total_score := !total_score + !score;
      count := !count + 1
    in
    if !score = 0 then prerr_endline ("test " ^ (string_of_int !count) ^ ": fail")
    else prerr_endline ("test " ^ (string_of_int !count) ^ ": pass")

  let _ = loopFile "test.tml" (test_run test_type)

  let _ = print_endline (ST.name ^ " " ^ (string_of_int !total_score))

end;;

module Hfoo = F (Typing) (struct let name = "Test score" end);;
