open Tml
exception NotImplemented 
exception Stuck
exception NotConvertible

(* Define your own datatypes *)
type stoval = 
    Computed of value 
  | Delayed of exp * env

 and stack =
   Hole_SK
   | Frame_SK of stack * frame

 and state =
   Anal_ST of (stoval Heap.heap) * stack * exp * env
   | Return_ST of (stoval Heap.heap) * stack * value 

 and env = Env of Heap.loc list
                           
 and value = 
   Lam_VAL of exp * env                      
   | Pair_VAL of exp * exp * env            
   | Inl_VAL of exp * env                    
   | Inr_VAL of exp * env                  
   | Unit_VAL                               
   | True_VAL                                
   | False_VAL                            
   | Num_VAL of int                         
   | Plus_VAL                               
   | Minus_VAL                               
   | Eq_VAL                                 

 and frame = 
   Loc_FR of Heap.loc
   | App_FR of exp * env
   | Fst_FR
   | Snd_FR
   | Case_FR of exp * exp * env
   | If_FR of exp * exp * env
   | Plus_FR
   | PlusExp_FR of exp * env
   | PlusVal_FR of value
   | Minus_FR
   | MinusExp_FR of exp * env
   | MinusVal_FR of value 
   | Eq_FR
   | EqExp_FR of exp * env
   | EqVal_FR of value 

(* Define your own empty environment *)
let emptyEnv = Env []

(* Implement the function value2exp : value -> Tml.exp
 * Warning : If you give wrong implementation of this function,
 *           you wiil receive no credit for the entire third part!  *)
let value2exp v = match v with 
    Unit_VAL -> Eunit 
  | True_VAL -> True  
  | False_VAL -> False
  | Num_VAL n -> Num n   
  | _ -> raise NotConvertible

(* Problem 1. 
 * texp2exp : Tml.texp -> Tml.exp *)
let union l1 l2 = List.fold_left (fun l x -> if List.mem x l then x :: (List.filter (fun y -> x <> y) l) 
                                             else x :: l) l1 (List.rev l2)

let free_var e =
  let rec free_var' e l = 
    match e with 
      Tvar x -> if List.mem x l then x :: (List.filter (fun y -> x <> y) l) else x :: l
    | Tlam (x, _, e') -> List.filter (fun y -> x <> y) (free_var' e' l)
    | Tapp (e1, e2) -> union (free_var' e1 l) (free_var' e2 [])
    | Tpair (e1, e2) -> union (free_var' e1 l) (free_var' e2 [])
    | Tfst e' -> free_var' e' l
    | Tsnd e' -> free_var' e' l
    | Tinl (e', _) -> free_var' e' l
    | Tinr (e', _) -> free_var' e' l
    | Tcase (e', v1, e1, v2, e2) -> union (free_var' e' l)
                                          (union (List.filter (fun y -> v1 <> y) (free_var' e1 []))
                                                 (List.filter (fun y -> v2 <> y) (free_var' e2 [])))                                          
    | Tfix (x, _, e') -> List.filter (fun y -> x <> y) (free_var' e' l)
    | Tifthenelse (e', e1, e2) -> union (free_var' e' l) 
                                        (union (free_var' e1 []) (free_var' e2 []))
    | _ -> l
  in
  free_var' e []

let rec var2index x l = 
  match l with 
    [] -> raise Stuck
  | hd :: tl -> if x = hd then 0 else 1 + var2index x tl

let texp2exp e = 
  let rec texp2exp' e l = 
    match e with
      Tvar x -> Ind (var2index x l)
    | Tlam (x, _, e') -> Lam (texp2exp' e' (x::l))
    | Tapp (e1, e2) -> App (texp2exp' e1 l, texp2exp' e2 l)
    | Tpair (e1, e2) -> Pair (texp2exp' e1 l, texp2exp' e2 l)
    | Tfst e' -> Fst (texp2exp' e' l)
    | Tsnd e' -> Snd (texp2exp' e' l)
    | Teunit -> Eunit
    | Tinl (e', _) -> Inl (texp2exp' e' l)
    | Tinr (e', _) -> Inr (texp2exp' e' l)
    | Tcase (e', v1, e1, v2, e2) -> Case (texp2exp' e' l, texp2exp' e1 (v1::l), texp2exp' e2 (v2::l))
    | Tfix (x, _, e') -> Fix (texp2exp' e' (x::l))
    | Ttrue -> True
    | Tfalse -> False
    | Tifthenelse (e1, e2, e3) -> Ifthenelse (texp2exp' e1 l, texp2exp' e2 l, texp2exp' e3 l)
    | Tnum n -> Num n
    | Tplus -> Plus
    | Tminus -> Minus
    | Teq -> Eq
  in
  texp2exp' e (free_var e)

(* Problem 2. 
 * step1 : Tml.exp -> Tml.exp *)   
let rec shift idx i n = 
  match n with
    Ind m -> if m >= i then Ind (m+idx) 
             else n
  | Lam e -> Lam (shift idx (i+1) e)
  | App (e1, e2) -> App (shift idx i e1, shift idx i e2)
  | Pair (e1, e2) -> Pair (shift idx i e1, shift idx i e2)
  | Fst e' -> Fst (shift idx i e')
  | Snd e' -> Snd (shift idx i e')
  | Inl e' -> Inl (shift idx i e')
  | Inr e' -> Inr (shift idx i e')
  | Case (e1, e2, e3) -> Case (shift idx i e1, shift idx (i+1) e2, shift idx (i+1) e3)
  | Ifthenelse (e1, e2, e3) -> Ifthenelse (shift idx i e1, shift idx i e2, shift idx i e3)
  | Fix e' -> Fix (shift idx (i+1) e')
  | _ -> n

(* [n/i]m *)
let rec subst m n i = 
  match m with
    Ind m' -> if m' < i then m 
              else if m' = i then shift i 0 n
              else Ind (m'-1)
  | Lam e -> Lam (subst e n (i+1))
  | App (e1, e2) -> App (subst e1 n i, subst e2 n i)
  | Pair (e1, e2) -> Pair (subst e1 n i, subst e2 n i)
  | Fst e' -> Fst (subst e' n i)
  | Snd e' -> Snd (subst e' n i)
  | Inl e' -> Inl (subst e' n i)
  | Inr e' -> Inr (subst e' n i)
  | Case (e1, e2, e3) -> Case (subst e1 n i, subst e2 n (i+1), subst e3 n (i+1))
  | Ifthenelse (e1, e2, e3) -> Ifthenelse (subst e1 n i, subst e2 n i, subst e3 n i)
  | Fix e' -> Fix (subst e' n (i+1))
  | _ -> m

let rec is_value e = match e with
    Lam _ -> true
  | Num _ -> true
  | True -> true
  | False -> true
  | Eunit -> true
  | Plus -> true
  | Minus -> true
  | Eq -> true
  | Pair (e1, e2) -> (is_value e1) && (is_value e2)
  | Inl e' -> is_value e'
  | Inr e' -> is_value e'
  | _ -> false

let rec step1 e = 
  match e with
  | App (e1, e2) -> 
     if is_value e1 then 
       match e1 with
       | Lam e' -> if is_value e2 then subst e' e2 0
                   else App (e1, step1 e2)
       | Plus -> if is_value e2 
                 then match e2 with
                        Pair (Num n1, Num n2) -> Num (n1 + n2)
                      | _ -> raise Stuck
                 else App (e1, step1 e2)
       | Minus -> if is_value e2 
                  then match e2 with
                         Pair (Num n1, Num n2) -> Num (n1 - n2)
                       | _ -> raise Stuck
                  else App (e1, step1 e2)
       | Eq -> if is_value e2 
               then match e2 with
                      Pair (n1, n2) -> if n1 = n2 then True else False
                    | _ -> raise Stuck
               else App (e1, step1 e2)
       | _ -> raise Stuck
     else App (step1 e1, e2) 
  | Pair (e1, e2) -> if is_value e1 then Pair (e1, step1 e2)
                     else Pair (step1 e1, e2)
  | Fst e' -> if is_value e' then match e' with
                                    Pair (v1, v2) -> v1
                                  | _ -> raise Stuck
              else Fst (step1 e')
  | Snd e' -> if is_value e' then match e' with
                                    Pair (v1, v2) -> v2
                                  | _ -> raise Stuck
              else Snd (step1 e')
  | Inl e' -> Inl (step1 e')
  | Inr e' -> Inr (step1 e')
  | Ifthenelse (e1, e2, e3) -> if is_value e1 then match e1 with
                                                     True -> e2
                                                   | False -> e3
                                                   | _ -> raise Stuck
                               else Ifthenelse (step1 e1, e2, e3)
  | Case (e1, e2, e3) -> if is_value e1 then match e1 with
                                               Inl e' -> subst e2 e' 0
                                             | Inr e' -> subst e3 e' 0
                                             | _ -> raise Stuck
                         else Case (step1 e1, e2, e3)
  | Fix e' -> subst e' (Fix e') 0
  | _ -> raise Stuck
               
(* Problem 3. 
 * step2 : state -> state *)
let step2 s = 
  try 
    (match s with
       Anal_ST (h, sk, exp, env) -> 
       (match exp with 
          Ind n -> (let Env en = env in 
                    try
                      match Heap.deref h (List.nth en n) with 
                        Computed v -> Return_ST (h, sk, v)
                      | Delayed (e, (Env env')) -> Anal_ST(h, Frame_SK (sk, Loc_FR (List.nth en n)), e, (Env env'))
                    with _ -> raise Stuck)
        | Lam e -> Return_ST (h, sk, Lam_VAL (Lam e, env))
        | App (e1, e2) -> Anal_ST (h, Frame_SK (sk, App_FR (e2, env)), e1, env)
        | Pair (e1, e2) -> Return_ST (h, sk, Pair_VAL (e1, e2, env))
        | Fst e -> Anal_ST (h, Frame_SK (sk, Fst_FR), e, env)
        | Snd e -> Anal_ST (h, Frame_SK (sk, Snd_FR), e, env)
        | Eunit -> Return_ST (h, sk, Unit_VAL)
        | Inl e -> Return_ST (h, sk, Inl_VAL (e, env))
        | Inr e -> Return_ST (h, sk, Inr_VAL (e, env))
        | Case (e, e1, e2) -> Anal_ST (h, Frame_SK (sk, Case_FR (e1, e2, env)), e, env)
        | Fix e -> let Env env' = env in
                   let (h', l) = Heap.allocate h (Delayed (Fix e, env)) in
                   Anal_ST (h', sk, e, Env (l::env')) 
        | Ifthenelse (e, e1, e2) -> Anal_ST (h, Frame_SK (sk, If_FR (e1, e2, env)), e, env)
        | True -> Return_ST (h, sk, True_VAL)
        | False -> Return_ST (h, sk, False_VAL)
        | Num n -> Return_ST (h, sk, Num_VAL n)      
        | Plus -> Return_ST (h, sk, Plus_VAL)
        | Minus -> Return_ST (h, sk, Minus_VAL)
        | Eq -> Return_ST (h, sk, Eq_VAL)
       )
     | Return_ST (h, sk, v) ->
        (match sk with
           Frame_SK (sk', Loc_FR l) -> Return_ST (Heap.update h l (Computed v), sk', v)
         | Frame_SK (sk',App_FR(e2,env)) ->
            (match v with 
               Lam_VAL(Lam e1,(Env env')) -> (try let (h', l) = Heap.allocate h (Delayed (e2,env))
                                                  in Anal_ST (h', sk', e1, Env (l::env'))
                                              with _ -> raise Stuck) 
             | Plus_VAL -> Anal_ST (h, Frame_SK (sk', Plus_FR), e2, env) 
             | Minus_VAL -> Anal_ST (h, Frame_SK (sk', Minus_FR), e2, env)
             | Eq_VAL -> Anal_ST (h, Frame_SK (sk', Eq_FR), e2, env)
             | _ -> raise Stuck)
              
         | Frame_SK (sk', Plus_FR) -> (match v with
                                         Pair_VAL (e1, e2, env) -> Anal_ST (h, Frame_SK (sk', PlusExp_FR (e2, env)), e1, env) 
                                       | _ -> raise Stuck)
         | Frame_SK (sk', PlusExp_FR (e2, env)) -> Anal_ST (h, Frame_SK (sk', PlusVal_FR v), e2, env)
         | Frame_SK (sk', PlusVal_FR (Num_VAL v1)) -> (match v with 
                                                         Num_VAL v2 -> Return_ST (h, sk', Num_VAL (v1 + v2))
                                                       | _ -> raise Stuck)               
                                                        
         | Frame_SK (sk', Minus_FR) -> (match v with
                                          Pair_VAL (e1, e2, env) -> Anal_ST (h, Frame_SK (sk', MinusExp_FR (e2, env)), e1, env)
                                        | _ -> raise Stuck)                       
         | Frame_SK (sk', MinusExp_FR (e2, env)) -> Anal_ST (h, Frame_SK (sk', MinusVal_FR v), e2, env)
         | Frame_SK (sk', MinusVal_FR (Num_VAL v1)) -> (match v with 
                                                          Num_VAL v2 -> Return_ST (h, sk', Num_VAL (v1 - v2))            
                                                        | _ -> raise Stuck)

         | Frame_SK (sk', Eq_FR) -> (match v with 
                                       Pair_VAL (e1, e2, env) -> Anal_ST (h, Frame_SK (sk', EqExp_FR (e2, env)), e1, env) 
                                     |  _ -> raise Stuck)
         | Frame_SK (sk', EqExp_FR (e2, env)) -> Anal_ST (h, Frame_SK (sk', EqVal_FR v),e2,env)
         | Frame_SK (sk', EqVal_FR (Num_VAL v1)) -> (match v with
                                                       Num_VAL v2 -> if v1 = v2 then Return_ST (h, sk', True_VAL) 
                                                                     else Return_ST (h, sk', False_VAL) 
                                                     | _ -> raise Stuck)
                                                      
         | Frame_SK (sk', Case_FR (e1, e2, Env env)) -> (match v with 
                                                           Inl_VAL (e,env') -> (try let (h', l) = Heap.allocate h (Delayed (e, env')) in 
                                                                                    Anal_ST (h', sk', e1, Env (l::env))
                                                                                with _ -> raise Stuck)
                                                         | Inr_VAL (e,env') -> (try let (h', l) = Heap.allocate h (Delayed (e, env')) in 
                                                                                    Anal_ST (h', sk', e2, Env (l::env)) 
                                                                                with _ -> raise Stuck)
                                                         | _ -> raise Stuck)
         | Frame_SK (sk', Fst_FR) -> (match v with
                                        Pair_VAL (e1, e2, env) -> Anal_ST (h, sk', e1, env) 
                                      | _ -> raise Stuck)
         | Frame_SK (sk', Snd_FR) -> (match v with 
                                        Pair_VAL (e1, e2, env) -> Anal_ST (h, sk', e2, env)
                                      | _ -> raise Stuck)
         | Frame_SK (sk', If_FR (e1, e2, env)) -> (match v with
                                                     True_VAL -> Anal_ST (h, sk', e1, env)
                                                   | False_VAL -> Anal_ST (h, sk', e2, env)
                                                   | _ -> raise Stuck)
         | _ -> raise Stuck
        )
    )
  with _ -> raise Stuck
                  
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
let value2string v = match v with
    Lam_VAL(e,env) -> (exp2string e) 
  | Pair_VAL(e1,e2,_) -> "Pair(" ^ (exp2string e1) ^"," ^ (exp2string e2) ^ ")"
  | Inl_VAL (e,_) -> "Inl(" ^ (exp2string e) ^ ")"
  | Inr_VAL (e,_) -> "Inr(" ^ (exp2string e) ^ ")"
  | Unit_VAL -> "Unit"
  | True_VAL -> "True"
  | False_VAL -> "False"
  | Num_VAL n -> "Num " ^ (string_of_int n)
  | Plus_VAL -> "+"  | Minus_VAL -> "-" | Eq_VAL -> "="
                                                      
let env2string h (Env env) = 
  let rec env2string' h env n str = match env with
      [] -> str ^ "]"
    | e :: env' -> let str' = str ^ (string_of_int n) ^ " -> " in
                   let result = match (Heap.deref h e) with
                       Computed v -> str' ^ "Computed(" ^ (value2string v) ^ ") "
                     | Delayed (e', env) -> str' ^ "Delayed(" ^ (exp2string e') ^ ") "
                   in env2string' h env' (n+1) result
  in env2string' h env 0 ""
                 
let frame2string f = 
  let rec frame2string' f str = match f with
      Loc_FR l -> "[" ^ (string_of_int l) ^ "];"
    | App_FR (e, _) -> "hole " ^ (exp2string e) ^ ";"
    | Fst_FR -> "Fst;"
    | Snd_FR -> "Snd;"
    | Plus_FR -> "Plus_FR;"
    | PlusExp_FR (e, _) -> "Plus_Exp " ^ (exp2string e) ^ ";"
    | PlusVal_FR v -> "PlusVal"
    | _ -> " not implement"
  in frame2string' f ""
                   
let sk2string sk = 
  let rec sk2string' sk str = match sk with
      Hole_SK -> str ^ "]"
    | Frame_SK (sk', f) -> sk2string' sk' ((frame2string f) ^ " " ^ str)
  in sk2string' sk ""
                
let heap2string h = 
  let rec heap2string' h str = match h with
      [] -> str ^ "]"
    | l::h'-> heap2string' h' (str ^ (match l with (l', _) -> string_of_int l'))
  in heap2string' h ""
                  
let state2string st = match st with
    Anal_ST (h, sk, exp, env) -> "\nAnalysis : " ^ (exp2string exp) ^
                                   "\nEnv : [" ^ (env2string h env) ^ 
                                     "\nHeap : [" ^ (heap2string h) ^ " ; Stack : [" ^ (sk2string sk)
                                                                                         
  | Return_ST(h,_,Lam_VAL(exp,env)) -> "Return : CLO(" ^ (exp2string exp) 
                                       ^ ", [" ^ (env2string h env) ^ ")"
  | Return_ST(h,_,v) -> "Return : " ^ (value2string v) 

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
