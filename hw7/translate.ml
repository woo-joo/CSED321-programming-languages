open Mach
open Mono 

exception NotImplemented
exception NeverHappen

(* location *)
type loc =
    | L_INT of int          (* integer constant *)
    | L_BOOL of bool        (* boolean constant *)
    | L_UNIT                (* unit constant *)
    | L_STR of string       (* string constant *)
    | L_ADDR of addr   (* at the specified address *)
    | L_REG of reg     (* at the specified register *)
    | L_DREF of loc * int   (* at the specified location with the specified offset *)

type venv = (Mono.avid, loc) Dict.dict  (* variable environment *)
let venv0 : venv = Dict.empty           (* empty variable environment *)

type env = venv * int
let env0 : env = (venv0, 0)

let constructor_label = "_Constructor_CSE_321_HW7_"
let pop_label = "_Pop_CSE_321_HW7_"
let ret_label = "_Ret_CSE_321_HW7_"
let exception_label = "_Exception_CSE_321_HW7_"
let patty2label patty = labelNewLabel "[Patty] " ((Mono_print.patty2str patty) ^ " ")
let expty2label expty = labelNewLabel "[Expty] " ((Mono_print.expty2str expty) ^ " ")
let dec2label dec = labelNewLabel "[Dec]   " ((Mono_print.dec2str dec) ^ " ")
let mrule2label mrule = labelNewLabel "[Mrule] " ((Mono_print.mrule2str mrule) ^ " ")

let get opt = match opt with Some v -> v | None -> raise NeverHappen

let rec init i item = if i = 0 then [] else item :: init (i - 1) item

let rec union s1 s2 =
    match s1 with
    | [] -> s2
    | h :: t -> union t (h :: List.filter (fun x -> x <> h) s2)

let spCurrent = ref 0

(* val loc2rvalue : loc -> Mach.code * Mach.rvalue *)
let rec loc2rvalue l = match l with
    | L_INT i -> code0, INT i
    | L_BOOL b -> code0, BOOL b
    | L_UNIT -> code0, UNIT
    | L_STR s -> code0, STR s
    | L_ADDR a -> code0, ADDR a
    | L_REG r -> code0, REG r
    | L_DREF (L_ADDR a, i) -> code0, REFADDR (a, i)
    | L_DREF (L_REG r, i) -> code0, REFREG (r, i)
    | L_DREF (l, i) ->
        let code, rvalue = loc2rvalue l in
        cpost code [MOVE (LREG tr, rvalue)], REFREG (tr, i)

(* val r2loc : Mach.rvalue -> loc *)
let r2loc rvalue = match rvalue with
    | INT int -> L_INT int
    | BOOL bool -> L_BOOL bool
    | UNIT -> L_UNIT
    | STR string -> L_STR string
    | ADDR addr -> L_ADDR addr
    | REG reg -> L_REG reg
    | REFADDR (addr, int) -> L_DREF (L_ADDR addr, int)
    | REFREG (reg, int) -> L_DREF (L_REG reg, int)

(*
 * helper functions for debugging
 *)
(* val loc2str : loc -> string *)
let rec loc2str l = match l with 
    | L_INT i -> "INT " ^ (string_of_int i)
    | L_BOOL b -> "BOOL " ^ (string_of_bool b)
    | L_UNIT -> "UNIT"
    | L_STR s -> "STR " ^ s
    | L_ADDR (CADDR a) -> "ADDR " ^ ("&" ^ a)
    | L_ADDR (HADDR a) -> "ADDR " ^ ("&Heap_" ^ (string_of_int a))
    | L_ADDR (SADDR a) -> "ADDR " ^ ("&Stack_" ^ (string_of_int a))
    | L_REG r -> 
        if r = sp then "REG SP"
        else if r = bp then "REG BP"
        else if r = cp then "REG CP"
        else if r = ax then "REG AX"
        else if r = bx then "REG BX"
        else if r = tr then "REG TR"
        else if r = zr then "REG ZR"
        else "R[" ^ (string_of_int r) ^ "]"
    | L_DREF (l, i) -> "DREF(" ^ (loc2str l) ^ ", " ^ (string_of_int i) ^ ")"

(* val patty2bound : Mono.patty -> Mono.avid list *)
let rec patty2bound patty =
    match patty with
    | PATTY (P_VID (avid, VAR), _) -> [avid]
    | PATTY (P_VIDP ((avid, CONF), patty), _) -> union [avid] (patty2bound patty)
    | PATTY (P_PAIR (patty1, patty2), _) -> union (patty2bound patty1) (patty2bound patty2)
    | _ -> []

(* val expty2free : Mono.avid list -> Mono.expty -> Mono.avid list *)
and expty2free bound expty =
    match expty with
    | EXPTY (E_VID (avid, VAR), _) -> if List.mem avid bound then [] else [avid]
    | EXPTY (E_FUN mlist, _) -> mlist2free bound mlist
    | EXPTY (E_APP (expty1, expty2), _) -> union (expty2free bound expty1) (expty2free bound expty2)
    | EXPTY (E_PAIR (expty1, expty2), _) -> union (expty2free bound expty1) (expty2free bound expty2)
    | EXPTY (E_LET (dec, expty), _) ->
        let bound = union bound (dec2bound dec) in
        union (dec2free bound dec) (expty2free bound expty)
    | _ -> []

(* val dec2free : Mono.expty -> Mono.avid list *)
and dec2bound dec =
    match dec with
    | D_VAL (patty, expty) -> patty2bound patty
    | D_REC (patty, expty) -> patty2bound patty
    | _ -> []

(* val dec2free : Mono.avid list -> Mono.expty -> Mono.avid list *)
and dec2free bound dec =
    match dec with
    | D_VAL (patty, expty) -> expty2free (union bound (patty2bound patty)) expty
    | D_REC (patty, expty) -> expty2free (union bound (patty2bound patty)) expty
    | _ -> []

(* val mlist2free : Mono.mrule list -> Mono.avid list *)
and mlist2free bound mlist =
    match mlist with
    | [] -> []
    | M_RULE (patty, expty) :: t -> union (expty2free (union bound (patty2bound patty)) expty) (mlist2free bound t)

(*
 * Generate code for Abstract Machine MACH 
 *)
(* pat2code : Mach.label -> Mach.label - > loc -> Mono.pat -> Mach.code * venv *)
let rec pat2code start failure l pat =
    let code, rvalue = loc2rvalue l in
    let code = cpre [LABEL start] code in
    match pat with
    | P_WILD -> code, venv0
    | P_INT int -> code @@ [MOVE (LREG bx, INT !spCurrent)] @@ [MOVE (LREG ax, ADDR (CADDR failure))] @@
                   [JMPNEQ (ADDR (CADDR ret_label), rvalue, INT int)], venv0
    | P_BOOL bool -> code @@ [MOVE (LREG bx, INT !spCurrent)] @@ [MOVE (LREG ax, ADDR (CADDR failure))] @@
                     [XOR (LREG tr, rvalue, BOOL bool)] @@ [JMPTRUE (ADDR (CADDR ret_label), REG tr)], venv0
    | P_UNIT -> code, venv0
    | P_VID (avid, VAR) ->
        (match rvalue with
        | INT _ | BOOL _ | UNIT | STR _ | ADDR (CADDR _) | REFREG (30, _) ->
            spCurrent := !spCurrent + 1;
            cpost code [PUSH rvalue], Dict.singleton (avid, L_DREF (L_REG bp, !spCurrent - 1))
        | _ -> code, Dict.singleton (avid, l))
    | P_VID (avid, CON) ->
        code @@ [MOVE (LREG tr, rvalue)] @@ [MOVE (LREG bx, INT !spCurrent)] @@ [MOVE (LREG ax, ADDR (CADDR failure))] @@
        [JMPNEQSTR ((ADDR (CADDR ret_label)), REFREG (tr, 0), STR avid)], venv0
    | P_VIDP ((avid, CONF), patty) ->
        let code = code @@ [MOVE (LREG tr, rvalue)] @@ [MOVE (LREG bx, INT !spCurrent)] @@ [MOVE (LREG ax, ADDR (CADDR failure))] @@
        [JMPNEQSTR ((ADDR (CADDR failure)), REFREG (tr, 0), STR avid)]
        in
        let code', venv = patty2code (patty2label patty) failure (L_DREF (L_REG tr, 1)) patty in
        code @@ code', venv
    | P_PAIR (patty1, patty2) ->
        let code', l' =
            (match rvalue with
            | REFADDR _ | REFREG _ ->
                spCurrent := !spCurrent + 1;
                [PUSH rvalue], L_DREF (L_REG bp, !spCurrent - 1)
            | _ -> [], r2loc rvalue)
        in
        let code1, venv1 = patty2code (patty2label patty1) failure (L_DREF (l', 0)) patty1 in
        let code2, venv2 = patty2code (patty2label patty2) failure (L_DREF (l', 1)) patty2 in
        code @@ code' @@ code1 @@ code2, Dict.merge venv1 venv2
    | _ -> raise NeverHappen

(* patty2code : Mach.label -> Mach.label -> loc -> Mono.patty -> Mach.code * venv *)
and patty2code start failure l patty =
    match patty with PATTY (pat, _) -> pat2code start failure l pat

(* exp2code : Mach.code -> env -> Mach.label -> Mono.exp -> Mach.code * Mach.rvalue *)
let rec exp2code code env start exp =
    let venv, _ = env in
    match exp with
    | E_INT int -> cpost code [LABEL start], INT int
    | E_BOOL bool -> cpost code [LABEL start], BOOL bool
    | E_UNIT -> cpost code [LABEL start], UNIT
    | E_VID (avid, VAR) ->
        let code', rvalue = loc2rvalue (get (Dict.lookup avid venv)) in
        code @@ (cpre [LABEL start] code'), rvalue
    | E_VID (avid, CON) ->
        spCurrent := !spCurrent + 1;
        code @@ [LABEL start] @@ [MALLOC (LREG tr, INT 1)] @@ [MOVE (LREFREG (tr, 0), STR avid)] @@ [PUSH (REG tr)],
        REFREG (bp, !spCurrent - 1)
    | E_VID (avid, CONF) ->
        spCurrent := !spCurrent + 1;
        code @@ [LABEL start] @@ [MALLOC (LREG tr, INT 2)] @@ [MOVE (LREFREG (tr, 0), ADDR (CADDR constructor_label))] @@
        [PUSH (REG tr)] @@ [MALLOC (LREFREG (tr, 1), INT 1)] @@ [MOVE (LREG tr, REFREG (tr, 1))] @@
        [MOVE (LREFREG (tr, 0), STR avid)], REFREG (bp, !spCurrent - 1)
    | E_FUN mlist ->
        let free_vars = mlist2free [] mlist in
        let alloc_code =
            spCurrent := !spCurrent + 1;
            [MALLOC (LREG tr, INT 2)] @@ [MOVE (LREFREG (tr, 0), ADDR (CADDR start))] @@ [PUSH (REG tr)] @@
            (if free_vars = [] then code0 else
            [MALLOC (LREFREG (tr, 1), INT (List.length free_vars))] @@ [MOVE (LREG tr, REFREG (tr, 1))] @@
            (let f i free_var =
                let code, rvalue = loc2rvalue (get (Dict.lookup free_var venv)) in
                cpost code [MOVE (LREFREG (tr, i), rvalue)]
            in
            List.flatten (List.mapi f free_vars)))
        in
        let f i free_var = free_var, r2loc (REFREG (cp, i)) in
        let venv = Dict.merge venv (List.mapi f free_vars) in
        let tempSpCurrent = !spCurrent in
        spCurrent := 0;
        let fun_code = mlist2code (mrule2label (List.hd mlist)) [LABEL start] (venv, 0) mlist in
        spCurrent := tempSpCurrent;
        fun_code @@ code @@ alloc_code, REFREG (bp, !spCurrent - 1)
    | E_APP (expty1, expty2) ->
        let op = expty1 in
        let code = cpost code [LABEL start] in
        (match expty1, expty2 with
        | EXPTY (E_PLUS, _), EXPTY (E_PAIR (expty1, expty2), _)
        | EXPTY (E_MINUS, _), EXPTY (E_PAIR (expty1, expty2), _)
        | EXPTY (E_MULT, _), EXPTY (E_PAIR (expty1, expty2), _)
        | EXPTY (E_EQ, _), EXPTY (E_PAIR (expty1, expty2), _)
        | EXPTY (E_NEQ, _), EXPTY (E_PAIR (expty1, expty2), _) ->
            let code1, rvalue1 = expty2code code env (expty2label expty1) expty1 in
            let code2, rvalue2 = expty2code code1 env (expty2label expty2) expty2 in
            (match rvalue1, rvalue2 with
            | INT int1, INT int2 ->
                (match op with
                | EXPTY (E_PLUS, _) -> code2, INT (int1 + int2)
                | EXPTY (E_MINUS, _) -> code2, INT (int1 - int2)
                | EXPTY (E_MULT, _) -> code2, INT (int1 * int2)
                | EXPTY (E_EQ, _) -> code2, if int1 = int2 then BOOL true else BOOL false
                | EXPTY (E_NEQ, _) -> code2, if int1 <> int2 then BOOL true else BOOL false
                | _ -> raise NeverHappen)
            | _ ->
                spCurrent := !spCurrent + 1;
                code2 @@
                (let neq_label = labelNewStr "NEQ" in
                match op with
                | EXPTY (E_PLUS, _) -> [ADD (LREG tr, rvalue1, rvalue2)]
                | EXPTY (E_MINUS, _) -> [SUB (LREG tr, rvalue1, rvalue2)]
                | EXPTY (E_MULT, _) -> [MUL (LREG tr, rvalue1, rvalue2)]
                | EXPTY (E_EQ, _) -> [MOVE (LREG tr, BOOL false)] @@ [JMPNEQ (ADDR (CADDR neq_label), rvalue1, rvalue2)] @@
                                    [MOVE (LREG tr, BOOL true)] @@ [LABEL neq_label]
                | EXPTY (E_NEQ, _) -> [MOVE (LREG tr, BOOL true)] @@ [JMPNEQ (ADDR (CADDR neq_label), rvalue1, rvalue2)] @@
                                    [MOVE (LREG tr, BOOL false)] @@ [LABEL neq_label]
                | _ -> raise NeverHappen)
                @@ [PUSH (REG tr)], REFREG (bp, !spCurrent - 1))
        | _ ->
            let code1, rvalue1 = expty2code code env (expty2label expty1) expty1 in
            let code2, rvalue2 = expty2code code1 env (expty2label expty2) expty2 in
            spCurrent := !spCurrent + 1;
            code2 @@ [PUSH (REG cp)] @@ [PUSH rvalue2] @@ [MOVE (LREG tr, rvalue1)] @@ [MOVE (LREG cp, REFREG (tr, 1))] @@
            [CALL (REFREG (tr, 0))] @@ [POP (LREG zr)] @@ [POP (LREG cp)] @@ [PUSH (REG ax)], REFREG (bp, !spCurrent - 1))
    | E_PAIR (expty1, expty2) ->
        let code1, rvalue1 = expty2code (cpost code [LABEL start]) env (expty2label expty1) expty1 in
        let code2, rvalue2 = expty2code code1 env (expty2label expty2) expty2 in
        let code = code2 @@ [MALLOC (LREG tr, INT 2)]
                         @@ [MOVE (LREFREG (tr, 0), rvalue1)]
                         @@ [MOVE (LREFREG (tr, 1), rvalue2)]
                         @@ [PUSH (REG tr)] in
        spCurrent := !spCurrent + 1;
        code, REFREG (bp, !spCurrent - 1)
    | E_LET (dec, expty) ->
        let code, env = dec2code (cpost code [LABEL start]) env (dec2label dec) dec in
        expty2code code env (expty2label expty) expty
    | _ -> raise NeverHappen

(* expty2code : Mach.code -> env -> Mach.label -> Mono.expty -> Mach.code * Mach.rvalue *)
and expty2code code env start expty =
    match expty with EXPTY (exp, _) -> exp2code code env start exp

(* dec2code : Mach.code -> env -> Mach.label -> Mono.dec -> Mach.code * env *)
and dec2code code env start dec =
    let venv, count = env in
    match dec with
    | D_VAL (patty, expty) ->
        let code1, rvalue = expty2code code env (expty2label expty) expty in
        let code2, venv' = patty2code (patty2label patty) exception_label (r2loc rvalue) patty in
        code1 @@ code2, (Dict.merge venv venv', count)
    | D_REC (patty, expty) ->
        (match patty, expty with PATTY (P_VID (avid, VAR), _), EXPTY (E_FUN mlist, _) ->
            let venv, _ = env in
            let venv = Dict.insert (avid, r2loc (REFREG (bp, !spCurrent))) venv in
            let code1, rvalue = expty2code code (venv, 0) (expty2label expty) expty in
            let code2, venv' = patty2code (patty2label patty) exception_label (r2loc rvalue) patty in
            code1 @@ code2, (Dict.merge venv venv', count)
        | _ -> raise NeverHappen)
    | D_DTYPE -> code, env

(* mrule2code : Mach.code -> env -> Mach.label -> Mach.label -> Mono.mrule -> Mach.code *)
and mrule2code code env start failure mrule =
    match mrule with M_RULE (patty, expty) ->
    let tempSpCurrent = !spCurrent in
    let venv, count = env in
    let code1, venv' = patty2code (patty2label patty) failure (L_DREF (L_REG bp, -3)) patty in
    let code2, rvalue = expty2code (code @@ cpre [LABEL start] code1) (Dict.merge venv venv', count) (expty2label expty) expty in
    let pop_code = init !spCurrent (POP (LREG zr)) in
    spCurrent := tempSpCurrent;
    code2 @@ [MOVE (LREG ax, rvalue)] @@ pop_code @@ [RETURN]

(* mlist2code : Mach.label -> Mach.code -> env -> Mono.mrule list -> Mach.code *)
and mlist2code start code env mlist =
    match mlist with
    | mrule1 :: mrule2 :: t ->
        let next_start = mrule2label mrule2 in
        let code = mrule2code code env start next_start mrule1 in
        mlist2code next_start code env (mrule2 :: t)
    | mrule :: [] -> mrule2code code env start exception_label mrule
    | [] -> raise NeverHappen

(* program2code : Mono.program -> Mach.code *)
let program2code (dlist, et) =
    let f (acc, env) dec = dec2code acc env (dec2label dec) dec in
    let code, env = List.fold_left f ([LABEL start_label], env0) dlist in
    let code, rvalue = expty2code code env (expty2label et) et in
    let constructor_code = [LABEL constructor_label] @@ [MALLOC (LREG tr, INT 2)] @@ [MOVE (LREFREG (tr, 0), REFREG (cp, 0))] @@
                           [MOVE (LREFREG (tr, 1), REFREG (bp, -3))] @@ [MOVE (LREG ax, REG tr)] @@ [RETURN]
    in
    let pop_code = [LABEL pop_label] @@ [POP (LREG zr)] @@ [SUB (LREG bx, REG bx, INT 1)] @@[LABEL ret_label] @@
                   [JMPNEQ (ADDR (CADDR pop_label), REG bx, REG zr)] @@ [JUMP (REG ax)]
    in
    let exception_code = [LABEL exception_label] @@ [EXCEPTION] in
    constructor_code @@ pop_code @@ (cpost code [HALT rvalue]) @@ exception_code
