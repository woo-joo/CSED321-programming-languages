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

let createEmptyContext () = fun _ -> raise TypeError

(* val typing : context -> Tml.exp -> Tml.tp *)
let rec typing cxt e =
    match e with
    | Var v -> cxt v
    | Lam (v, t, e') -> Fun (t, typing (fun v_ -> if v_ = v then t else cxt v_) e')
    | App (e1, e2) ->
        (match typing cxt e1 with
        | Fun (t1, t2) -> if t1 = typing cxt e2 then t2 else raise TypeError
        | _ -> raise TypeError)
    | Pair (e1, e2) -> Prod (typing cxt e1, typing cxt e2)
    | Fst e' ->
        (match typing cxt e' with
        | Prod (t, _) -> t
        | _ -> raise TypeError)
    | Snd e' ->
        (match typing cxt e' with
        | Prod (_, t) -> t
        | _ -> raise TypeError)
    | Eunit -> Unit
    | Inl (e', t) -> Sum (typing cxt e', t)
    | Inr (e', t) -> Sum (t, typing cxt e')
    | Case (e', v1, e1, v2, e2) ->
        (match typing cxt e' with
        | Sum (t1, t2) ->
            let v1_t = typing (fun v_ -> if v_ = v1 then t1 else cxt v_) e1 in
            let v2_t = typing (fun v_ -> if v_ = v2 then t2 else cxt v_) e2 in
            if v1_t = v2_t then v1_t else raise TypeError
        | _ -> raise TypeError)
    | Fix (v, t, e') -> if t = typing (fun v_ -> if v_ = v then t else cxt v_) e' then t else raise TypeError
    | True | False -> Bool
    | Ifthenelse (e', e1, e2) ->
        (match typing cxt e' with
        | Bool ->
            let e1_t = typing cxt e1 in
            let e2_t = typing cxt e2 in
            if e1_t = e2_t then e1_t else raise TypeError
        | _ -> raise TypeError)
    | Num _ -> Int
    | Plus | Minus -> Fun (Prod (Int, Int), Int)
    | Eq -> Fun (Prod (Int, Int), Bool)

let typeOf e = typing (createEmptyContext ()) e 
let typeOpt e = try Some (typeOf e) 
                with TypeError -> None



