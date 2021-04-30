open Tml
exception NotImplemented 
exception Stuck
exception NotConvertible

type stoval = 
	  Computed of value 
	| Delayed of exp * env

 and stack =
	  Hole_SK
	| Frame_SK of stack * frame

 and state =
	  Anal_ST of (stoval Heap.heap) * stack * exp * env
	| Return_ST of (stoval Heap.heap) * stack * value 

 (* Define your own datatypes *)
 and env = NOT_IMPLEMENT_ENV
 and value = NOT_IMPLEMENT_VALUE
 and frame = NOT_IMPLEMENT_FRAME

(* Define your own empty environment *)
let emptyEnv = NOT_IMPLEMENT_ENV

(* Implement the function value2exp : value -> Tml.exp
 * Warning : If you give wrong implementation of this function,
 *           you wiil receive no credit for the entire third part!  *)
let value2exp _ = raise NotImplemented

(* Return the index of x in l.
 * If there is no x in l, raise Stuck.
 * memi : a' -> a' list -> int *)
let rec memi x l =
	match l with
	| [] -> raise Stuck
	| h :: t -> if x = h then 0 else (memi x t) + 1

(* Problem 1. 
 * texp2exp : Tml.texp -> Tml.exp *)
let texp2exp te =
	let rec texp2exp_aux n te =
		match te with
		| Tvar x -> let n_ = if List.mem x n then n else n @ [x] in (n_, Ind (memi x n_))
		| Tlam (x, _, te) -> let n, e = texp2exp_aux (x :: n) te in (List.tl n, Lam e)
		| Tapp (te1, te2) ->
			let n2, e2 = texp2exp_aux n te2 in
			let n1, e1 = texp2exp_aux n2 te1 in
			(n1, App (e1, e2))
		| Tpair (te1, te2) ->
			let n2, e2 = texp2exp_aux n te2 in
			let n1, e1 = texp2exp_aux n2 te1 in
			(n1, Pair (e1, e2))
		| Tfst te -> let n, e = texp2exp_aux n te in (n, Fst e)
		| Tsnd te -> let n, e = texp2exp_aux n te in (n, Snd e)
		| Teunit -> (n, Eunit)
		| Tinl (te, _) -> let n, e = texp2exp_aux n te in (n, Inl e)
		| Tinr (te, _) -> let n, e = texp2exp_aux n te in (n, Inr e)
		| Tcase (te, x1, te1, x2, te2) ->
			let n2, e2 = texp2exp_aux (x2 :: n) te2 in
			let n1, e1 = texp2exp_aux (x1 :: List.tl n2) te1 in
			let n, e = texp2exp_aux (List.tl n1) te in
			(n, Case (e, e1, e2))
		| Tfix (x, _, te) -> let n, e = texp2exp_aux (x :: n) te in (List.tl n, Fix e)
		| Ttrue -> (n, True)
		| Tfalse -> (n, False)
		| Tifthenelse (te, te1, te2) ->
			let n2, e2 = texp2exp_aux n te2 in
			let n1, e1 = texp2exp_aux n2 te1 in
			let n, e = texp2exp_aux n1 te in
			(n, Ifthenelse (e, e1, e2))
		| Tnum i -> (n, Num i)
		| Tplus -> (n, Plus)
		| Tminus -> (n, Minus)
		| Teq -> (n, Eq)
	in let _, e = texp2exp_aux [] te in e 

(* Problem 2. 
 * step1 : Tml.exp -> Tml.exp *)   
let rec step1 _ = raise NotImplemented

(* Problem 3. 
 * step2 : state -> state *)
let step2 _ = raise NotImplemented
                    
(* exp2string : Tml.exp -> string *)
let rec exp2string exp = 
	match exp with 
	  Ind x -> string_of_int x
	| Lam e -> "(lam. " ^ (exp2string e) ^ ")"
	| App (e1, e2) -> "(" ^ (exp2string e1) ^ " " ^ (exp2string e2) ^ ")"
	| Pair (e1, e2) -> "(" ^ (exp2string e1) ^ "," ^ (exp2string e2) ^ ")"
	| Fst e -> "(fst " ^ (exp2string e) ^ ")"
	| Snd e -> "(snd " ^ (exp2string e) ^ ")"
	| Eunit -> "()"
	| Inl e -> "(inl " ^ (exp2string e) ^ ")"
	| Inr e -> "(inr " ^ (exp2string e) ^ ")"
	| Case (e, e1, e2) -> "(case " ^ (exp2string e) ^" of " ^ (exp2string e1) ^
						  " | " ^ (exp2string e2) ^ ")"
	| Fix e -> "fix. "  ^ (exp2string e) ^ ")"
	| Ifthenelse (e, e1, e2) -> 
		"(if " ^ (exp2string e) ^ " then " ^ (exp2string e1) ^ 
		" else " ^ (exp2string e2) ^ ")"
	| True -> "true"  | False -> "false"
	| Num n -> "<" ^ (string_of_int n) ^ ">"
	| Plus -> "+"  | Minus -> "-" | Eq -> "="

(* state2string : state -> string 
 * you may modify this function for debugging your code *)
let state2string st = match st with
	  Anal_ST(_,_,exp,_) -> "Analysis : ???"
	| Return_ST(_,_,_) -> "Return : ??? "

(* ------------------------------------------------------------- *)     
let stepOpt1 e = try Some (step1 e) with Stuck -> None
let stepOpt2 st = try Some (step2 st) with Stuck -> None

let rec multiStep1 e = try multiStep1 (step1 e) with Stuck -> e
let rec multiStep2 st = try multiStep2 (step2 st) with Stuck -> st

let stepStream1 e =
	let rec steps e = 
		match (stepOpt1 e) with
		  None -> Stream.from (fun _ -> None)
		| Some e' -> Stream.icons e' (steps e')
	in 
	Stream.icons e (steps e)

let stepStream2 st =
	let rec steps st = 
		match (stepOpt2 st) with
		  None -> Stream.from (fun _ -> None)
		| Some st' -> Stream.icons st' (steps st')
	in 
	Stream.icons st (steps st)
