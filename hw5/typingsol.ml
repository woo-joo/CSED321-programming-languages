open Tml

exception TypeError

(***************************************************** 
 * replace unit by your own type for typing contexts *
 *****************************************************)
type context = var -> tp 

(*
 * For each function you introduce, 
 * write its type, specification, and invariant. 
 *)

(* unit -> context *)
let createEmptyContext () = fun _ -> raise TypeError 

(* context -> var -> tp -> context *)
let updateContext cxt x t = fun x' -> if x' = x then t else cxt x'

(* context -> exp -> tp *)
let rec typing cxt e = match e with
    Var x -> cxt x
  | Lam (x, t, e') -> Fun (t, typing (updateContext cxt x t) e')
  | App (e1, e2) -> (match typing cxt e1 with 
                       Fun (a, b) -> if typing cxt e2 = a then b else raise TypeError
                     | _ -> raise TypeError)
  | Pair (e1, e2) -> Prod (typing cxt e1, typing cxt e2)
  | Fst e' -> (match typing cxt e' with
                 Prod (a, b) -> a
               | _ -> raise TypeError)
  | Snd e' -> (match typing cxt e' with
                 Prod (a, b) -> b
               | _ -> raise TypeError)
  | Eunit -> Unit
  | Inl (e', t) -> Sum (typing cxt e', t)
  | Inr (e', t) -> Sum (t, typing cxt e')
  | Case (e', v1, e1, v2, e2) -> 
     (match typing cxt e' with 
        Sum (t1, t2) -> let c1 = typing (updateContext cxt v1 t1) e1 in
                        let c2 = typing (updateContext cxt v2 t2) e2 in
                        if c1 = c2 then c1 else raise TypeError
      | _ -> raise TypeError)
  | Fix (x, t, e') -> if t = typing (updateContext cxt x t) e' then t
                      else raise TypeError
  | True -> Bool
  | False -> Bool
  | Ifthenelse (e', e1, e2) -> if typing cxt e' = Bool 
                               then let t1 = typing cxt e1 in 
                                    let t2 = typing cxt e2 in
                                    if t1 = t2 then t1 else raise TypeError
                               else raise TypeError     
  | Num i -> Int
  | Plus -> Fun (Prod (Int, Int), Int)
  | Minus -> Fun (Prod (Int, Int), Int)
  | Eq -> Fun (Prod (Int, Int), Bool)    

let typeOf e = typing (createEmptyContext ()) e 
let typeOpt e = try Some (typeOf e) 
                with TypeError -> None



