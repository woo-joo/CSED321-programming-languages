(*
 * Call-by-value reduction   
 *)

open Uml

exception NotImplemented 
exception Stuck

let freshVarCounter = ref 0
                          
(*   getFreshVariable : string -> string 
 *   use this function if you need to generate a fresh variable from s. 
 *)
let getFreshVariable s = 
    let _ = freshVarCounter := !freshVarCounter + 1
    in
    s ^ "__" ^ (string_of_int (!freshVarCounter))

(*
 * get an union of sets s1 and s2 : 'a list -> 'a list -> 'a list
 *)
let rec union s1 s2 =
    match s1 with
    | [] -> s2
    | h :: t -> union t (h :: List.filter (fun x -> x <> h) s2)

(*
 * get a set of fresh variables from e : exp -> var list
 *)
let rec getFV e =
    match e with
    | Var v -> [v]
    | Lam (v, e1) -> List.filter (fun s -> s <> v) (getFV e1)
    | App (e1, e2) -> union (getFV e1) (getFV e2)

(*
 * implement a single step with reduction using the call-by-value strategy.
 *)
let rec stepv e = raise NotImplemented

(*
 * implement a single step with reduction using the call-by-name strategy.
 *)
let rec stepn e = raise NotImplemented

let stepOpt stepf e = try Some (stepf e) with Stuck -> None

let rec multiStep stepf e = try multiStep stepf (stepf e) with Stuck -> e

let stepStream stepf e =
    let rec steps e = 
        match (stepOpt stepf e) with 
          None -> Stream.from (fun _ -> None)
        | Some e' -> Stream.icons e' (steps e')
    in 
    Stream.icons e (steps e)
