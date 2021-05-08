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
 and env = Heap.loc list

 and value =
	| Lam_VAL of exp * env
	| Pair_VAL of exp * exp * env
	| Eunit_VAL
	| Inl_VAL of exp * env
	| Inr_VAL of exp * env
	| True_VAL
	| False_VAL
	| Num_VAL of int
	| Plus_VAL
	| Minus_VAL
	| Eq_VAL

 and frame =
	| App_FR of exp * env
	| Fst_FR
	| Snd_FR
	| Case_FR of exp * exp * env
	| Ifthenelse_FR of exp * exp * env
	| Plus_FR
	| Plus_Fst_FR of exp * env
	| Plus_Snd_FR of value
	| Minus_FR
	| Minus_Fst_FR of exp * env
	| Minus_Snd_FR of value
	| Eq_FR
	| Eq_Fst_FR of exp * env
	| Eq_Snd_FR of value
	| Loc_FR of Heap.loc

(* Define your own empty environment *)
let emptyEnv = []

(* Implement the function value2exp : value -> Tml.exp
 * Warning : If you give wrong implementation of this function,
 *           you wiil receive no credit for the entire third part!  *)
let value2exp v =
	match v with
	| Eunit_VAL -> Eunit
	| True_VAL -> True
	| False_VAL -> False
	| Num_VAL i -> Num i
	| _ -> raise NotConvertible

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

(* Return true if exp is value.
 * is_value : Tml.exp -> bool *)
let rec is_value e =
	match e with
	| Ind _ | Lam _ | Eunit | True | False | Num _ | Plus | Minus | Eq -> true
	| Pair (e1, e2) -> (is_value e1) && (is_value e2)
	| Inl e | Inr e -> is_value e
	| _ -> false

(* Shift free variables.
 * shift Tml.index -> Tml.index -> Tml. exp -> Tml.exp *)
let rec shift m n e =
	match e with
	| Ind i -> if i < n then Ind i else Ind (i + m)
	| Lam e -> Lam (shift m (n + 1) e)
	| App (e1, e2) -> App (shift m n e1, shift m n e2)
	| Pair (e1, e2) -> Pair (shift m n e1, shift m n e2)
	| Fst e -> Fst (shift m n e)
	| Snd e -> Snd (shift m n e)
	| Inl e -> Inl (shift m n e)
	| Inr e -> Inr (shift m n e)
	| Case (e, e1, e2) -> Case (shift m n e, shift m (n + 1) e1, shift m (n + 1) e2)
	| Fix e -> Fix (shift m (n + 1) e)
	| Ifthenelse (e, e1, e2) -> Ifthenelse (shift m n e, shift m n e1, shift m n e2)
	| _ -> e

(* Substitute e' for every occurrence of i in e.
 * substitute : Tml.exp -> Tml.index -> Tml.exp -> Tml.exp *)
let rec substitute e' m e =
	match e with
	| Ind i -> if i < m then Ind i else if i > m then Ind (i - 1) else shift m 0 e'
	| Lam e -> Lam (substitute e' (m + 1) e)
	| App (e1, e2) -> App (substitute e' m e1, substitute e' m e2)
	| Pair (e1, e2) -> Pair (substitute e' m e1, substitute e' m e2)
	| Fst e -> Fst (substitute e' m e)
	| Snd e -> Snd (substitute e' m e)
	| Inl e -> Inl (substitute e' m e)
	| Inr e -> Inr (substitute e' m e)
	| Case (e, e1, e2) -> Case (substitute e' m e, substitute e' (m + 1) e1, substitute e' (m + 1) e2)
	| Fix e -> Fix (substitute e' (m + 1) e)
	| Ifthenelse (e, e1, e2) -> Ifthenelse (substitute e' m e, substitute e' m e1, substitute e' m e2)
	| _ -> e

(* Problem 2. 
 * step1 : Tml.exp -> Tml.exp *)   
let rec step1 e =
	match e with
	| App (e1, e2) ->
		(match e1 with
		| Lam e1 -> if is_value e2 then substitute e2 0 e1 else App (Lam e1, step1 e2)
		| Plus -> (match e2 with Pair (Num i1, Num i2) -> Num (i1 + i2) | _ -> App (Plus, step1 e2))
		| Minus -> (match e2 with Pair (Num i1, Num i2) -> Num (i1 - i2) | _ -> App (Minus, step1 e2))
		| Eq -> (match e2 with Pair (Num i1, Num i2) -> if i1 = i2 then True else False | _ -> App (Eq, step1 e2))
		| _ -> App (step1 e1, e2))
	| Pair (e1, e2) -> if is_value e1 then Pair (e1, step1 e2) else Pair (step1 e1, e2)
	| Fst e -> if is_value e then match e with Pair (e1, _) -> e1 | _ -> raise Stuck else Fst (step1 e)
	| Snd e -> if is_value e then match e with Pair (_, e2) -> e2 | _ -> raise Stuck else Snd (step1 e)
	| Inl e -> Inl (step1 e)
	| Inr e -> Inr (step1 e)
	| Case (e, e1, e2) ->
		if is_value e then
		match e with
		| Inl e -> substitute e 0 e1
		| Inr e -> substitute e 0 e2
		| _ -> raise Stuck
		else Case (step1 e, e1, e2)
	| Fix e -> substitute (Fix e) 0 e
	| Ifthenelse (e, e1, e2) ->
		if is_value e then
		match e with True -> e1 | False -> e2 | _ -> raise Stuck
		else Ifthenelse (step1 e, e1, e2)
	| _ -> raise Stuck

(* Problem 3. 
 * step2 : state -> state *)
let step2 s =
	match s with
	| Anal_ST (h, sk, e, en) ->
		(match e with
		| Ind i ->
			let l = List.nth en i in
			(match Heap.deref h l with
			| Computed v -> Return_ST (h, sk, v)
			| Delayed (e, en) -> Anal_ST (h, Frame_SK (sk, Loc_FR l), e, en))
		| Lam e -> Return_ST (h, sk, Lam_VAL (e, en))
		| App (e1, e2) -> Anal_ST (h, Frame_SK (sk, App_FR (e2, en)), e1, en)
		| Pair (e1, e2) -> Return_ST (h, sk, Pair_VAL (e1, e2, en))
		| Fst e -> Anal_ST (h, Frame_SK (sk, Fst_FR), e, en)
		| Snd e -> Anal_ST (h, Frame_SK (sk, Snd_FR), e, en)
		| Eunit -> Return_ST (h, sk, Eunit_VAL)
		| Inl e -> Return_ST (h, sk, Inl_VAL (e, en))
		| Inr e -> Return_ST (h, sk, Inr_VAL (e, en))
		| Case (e, e1, e2) -> Anal_ST (h, Frame_SK (sk, Case_FR (e1, e2, en)), e, en)
		| Fix e -> let h, l = Heap.allocate h (Delayed (Fix e, en)) in Anal_ST (h, sk, e, l :: en)
		| True -> Return_ST (h, sk, True_VAL)
		| False -> Return_ST (h, sk, False_VAL)
		| Ifthenelse (e, e1, e2) -> Anal_ST (h, Frame_SK (sk, Ifthenelse_FR (e1, e2, en)), e, en)
		| Num i -> Return_ST (h, sk, Num_VAL i)
		| Plus -> Return_ST (h, sk, Plus_VAL)
		| Minus -> Return_ST (h, sk, Minus_VAL)
		| Eq -> Return_ST (h, sk, Eq_VAL))
	| Return_ST (h, sk, v) ->
		(match sk with
		| Hole_SK -> raise Stuck
		| Frame_SK (sk, fr) ->
			(match fr, v with
			| App_FR (e, en), Lam_VAL (e_, en_) -> let h, l = Heap.allocate h (Delayed (e, en)) in Anal_ST (h, sk, e_, l :: en_)
			| App_FR (e, en), Plus_VAL -> Anal_ST (h, Frame_SK(sk, Plus_FR), e, en)
			| App_FR (e, en), Minus_VAL -> Anal_ST (h, Frame_SK(sk, Minus_FR), e, en)
			| App_FR (e, en), Eq_VAL -> Anal_ST (h, Frame_SK(sk, Eq_FR), e, en)
			| Fst_FR, Pair_VAL (e1, e2, en) -> Anal_ST (h, sk, e1, en)
			| Snd_FR, Pair_VAL (e1, e2, en) -> Anal_ST (h, sk, e2, en)
			| Case_FR (e1, e2, en), Inl_VAL (e, en_) -> let h, l = Heap.allocate h (Delayed (e, en_)) in Anal_ST (h, sk, e1, l :: en)
			| Case_FR (e1, e2, en), Inr_VAL (e, en_) -> let h, l = Heap.allocate h (Delayed (e, en_)) in Anal_ST (h, sk, e2, l :: en)
			| Ifthenelse_FR (e1, e2, en), True_VAL -> Anal_ST (h, sk, e1, en)
			| Ifthenelse_FR (e1, e2, en), False_VAL -> Anal_ST (h, sk, e2, en)
			| Plus_FR, Pair_VAL (e1, e2, en) -> Anal_ST (h, Frame_SK (sk, Plus_Fst_FR(e2, en)), e1, en)
			| Plus_Fst_FR (e, en), Num_VAL i -> Anal_ST (h, Frame_SK (sk, Plus_Snd_FR v), e, en)
			| Plus_Snd_FR (Num_VAL i), Num_VAL i_ -> Return_ST (h, sk, Num_VAL (i + i_))
			| Minus_FR, Pair_VAL (e1, e2, en) -> Anal_ST (h, Frame_SK (sk, Minus_Fst_FR(e2, en)), e1, en)
			| Minus_Fst_FR (e, en), Num_VAL i -> Anal_ST (h, Frame_SK (sk, Minus_Snd_FR v), e, en)
			| Minus_Snd_FR (Num_VAL i), Num_VAL i_ -> Return_ST (h, sk, Num_VAL (i - i_))
			| Eq_FR, Pair_VAL (e1, e2, en) -> Anal_ST (h, Frame_SK (sk, Eq_Fst_FR(e2, en)), e1, en)
			| Eq_Fst_FR (e, en), Num_VAL i -> Anal_ST (h, Frame_SK (sk, Eq_Snd_FR v), e, en)
			| Eq_Snd_FR (Num_VAL i), Num_VAL i_ -> let v = if i = i_ then True_VAL else False_VAL in Return_ST (h, sk, v)
			| Loc_FR l, _ -> Return_ST (Heap.update h l (Computed v), sk, v)
			| _ -> raise Stuck))
                    
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
