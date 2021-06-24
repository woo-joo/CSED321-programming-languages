(*
 * Call-by-value reduction   
 *)

exception NotImplemented 
exception Stuck

open Uml
       
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
  | _ -> raise Stuck

(* substitution [e'/x]e *)
let rec substitution e e' x = 
  match e with
    Var y -> if y = x then e'
             else e
  | Lam (y, e'') -> if x = y then e
                    else if (List.mem x (freeVar e)) = false then e
                    else if (List.mem y (freeVar e')) = false 
                    then Lam (y, substitution e'' e' x)
                    else substitution (alphaConv e e' y x) e' x   
  | App (e1, e2) -> App (substitution e1 e' x, substitution e2 e' x)           

(*
 * implement a single step with reduction using the call-by-value strategy.
 *)
(*
let rec stepv e = 
  match e with
    Var x -> raise Stuck
  | Lam (x, e') -> raise Stuck
  | App (e1, e2) -> match e1 with 
                      Var y -> raise Stuck
                    | Lam (y, e'') -> (match e2 with
                                         Lam _ -> substitution e'' e2 y
				                               | _ -> App (e1, stepv e2)) 
                    | _ -> App (stepv e1, e2)             
 *)

let rec stepv e = 
  match e with
  | App (Lam (x, e'), Lam (y, e2)) -> substitution e' (Lam (y, e2)) x
  | App (Lam (x, e'), e2) -> App (Lam (x, e'), stepv e2)
  | App (e1, e2) -> App (stepv e1, e2)             
  | _ -> raise Stuck

(*
 * implement a single step with reduction using the call-by-name strategy.
 *)
(*
let rec stepn e = 
  match e with
    Var x -> raise Stuck
  | Lam (x, e') -> raise Stuck
  | App (e1, e2) -> match e1 with 
                      Var y -> raise Stuck
                    | Lam (y, e'') -> substitution e'' e2 y
                    | _ -> App (stepn e1, e2)             
 *)

let rec stepn e = 
  match e with
  | App (Lam (x, e'), e2) -> substitution e' e2 x
  | App (e1, e2) -> App (stepn e1, e2)             
  | _ -> raise Stuck

let stepOpt stepf e = try Some (stepf e) with Stuck -> None

let rec multiStep stepf e = try multiStep stepf (stepf e) with Stuck -> e

let stepStream stepf e =
  let rec steps e = 
    match (stepOpt stepf e) with 
      None -> Stream.from (fun _ -> None)
    | Some e' -> Stream.icons e' (steps e')
  in 
  Stream.icons e (steps e)

