exception NotImplemented
exception TypingError

let tyvarCurrent = ref 0
let freshTyvar () = tyvarCurrent := !tyvarCurrent + 1; !tyvarCurrent

let tynameCurrent = ref 0
let freshTyname () = tynameCurrent := !tynameCurrent + 1; !tynameCurrent

let get opt = match opt with Some v -> v | None -> raise TypingError

let rec unify e =
    let rec ftv tyvar ty =
        match ty with
        | Core.T_PAIR (ty1, ty2) | Core.T_FUN (ty1, ty2) -> (ftv tyvar ty1) && (ftv tyvar ty2)
        | Core.T_VAR tyvar' -> tyvar = tyvar'
        | _ -> false
    in
    let eSub s e = List.map (fun (ty1, ty2) -> (tySub s ty1, tySub s ty2)) e in
    match e with
    | [] -> []
    | (Core.T_INT, Core.T_INT) :: t
    | (Core.T_BOOL, Core.T_BOOL) :: t
    | (Core.T_UNIT, Core.T_UNIT) :: t -> unify t
    | (Core.T_NAME tyname1, Core.T_NAME tyname2) :: t -> if tyname1 = tyname2 then unify t else raise TypingError
    | (Core.T_PAIR (ty11, ty12), Core.T_PAIR (ty21, ty22)) :: t
    | (Core.T_FUN (ty11, ty12), Core.T_FUN (ty21, ty22)) :: t -> unify ((ty11, ty21) :: (ty12, ty22) :: t)
    | (Core.T_VAR tyvar1, Core.T_VAR tyvar2) :: t ->
        if tyvar1 = tyvar2 then unify t
        else let s = Core.T_VAR tyvar2, tyvar1 in s :: (unify (eSub [s] t))
    | (Core.T_VAR tyvar, ty) :: t
    | (ty, Core.T_VAR tyvar) :: t ->
        if ftv tyvar ty then raise TypingError
        else let s = (ty, tyvar) in s :: (unify (eSub [s] t))
    | _ -> raise TypingError

and veSub s ve =
    match s with
    | [] -> ve
    | (ty, tyvar) :: t ->
        let f ((tyvars, ty'), is) =
            if Set_type.mem tyvar tyvars then (tyvars, ty'), is
            else (tyvars, tySub [(ty, tyvar)] ty'), is
        in
        veSub t (Dict.map f ve)

and ty2core te ty =
    match ty with
    | Ast.T_INT -> Core.T_INT
    | Ast.T_BOOL -> Core.T_BOOL
    | Ast.T_UNIT -> Core.T_UNIT
    | Ast.T_CON tycon -> Core.T_NAME (get (Dict.lookup tycon te))
    | Ast.T_PAIR (ty1, ty2) -> Core.T_PAIR (ty2core te ty1, ty2core te ty2)
    | Ast.T_FUN (ty1, ty2) -> Core.T_FUN (ty2core te ty1, ty2core te ty2)

and tySub s ty =
    match s with
    | [] -> ty
    | h :: t ->
        (match ty with
        | Core.T_PAIR (ty1, ty2) -> tySub t (Core.T_PAIR (tySub [h] ty1, tySub [h] ty2))
        | Core.T_FUN (ty1, ty2) -> tySub t (Core.T_FUN (tySub [h] ty1, tySub [h] ty2))
        | Core.T_VAR tyvar' -> let ty, tyvar = h in tySub t (if tyvar = tyvar' then ty else Core.T_VAR tyvar')
        | _ -> ty)

and pat2core te ve pat =
    match pat with
    | Ast.P_WILD -> Core.PATTY (Core.P_WILD, Core.T_VAR (freshTyvar ())), Dict.empty
    | Ast.P_INT int -> Core.PATTY (Core.P_INT int, Core.T_INT), Dict.empty
    | Ast.P_BOOL bool -> Core.PATTY (Core.P_BOOL bool, Core.T_BOOL), Dict.empty
    | Ast.P_UNIT -> Core.PATTY (Core.P_UNIT, Core.T_UNIT), Dict.empty
    | Ast.P_VID vid ->
        let (tyvars, ty), is =
            try get (Dict.lookup vid ve)
            with TypingError -> (Set_type.empty, Core.T_UNIT), Core.VAR
        in
        (match tyvars, ty, is with
        | _, _, Core.VAR ->
            let tyvar = freshTyvar () in
            Core.PATTY (Core.P_VID (vid, is), Core.T_VAR tyvar), Dict.singleton (vid, ((Set_type.empty, Core.T_VAR tyvar), is))
        | [], Core.T_NAME tyname, Core.CON -> Core.PATTY (Core.P_VID (vid, is), ty), Dict.empty
        | _ -> raise TypingError)
    | Ast.P_VIDP (vid, pat) ->
        let (tyvars, ty), is = get (Dict.lookup vid ve) in
        (match tyvars, ty, is with
        | [], Core.T_FUN (ty, Core.T_NAME tyname), Core.CONF ->
            let Core.PATTY (pat, ty'), ve = pat2core te ve pat in
            let s = unify [(ty, ty')] in
            Core.PATTY (Core.P_VIDP ((vid, Core.CONF), pattySub s (Core.PATTY (pat, ty'))), Core.T_NAME tyname),
            veSub s ve
        | _ -> raise TypingError)
    | Ast.P_PAIR (pat1, pat2) ->
        let Core.PATTY (pat1, ty1), ve1 = pat2core te ve pat1 in
        let Core.PATTY (pat2, ty2), ve2 = pat2core te ve pat2 in
        Core.PATTY (Core.P_PAIR (Core.PATTY (pat1, ty1), Core.PATTY (pat2, ty2)), Core.T_PAIR (ty1, ty2)),
        Dict.merge ve1 ve2
    | Ast.P_TPAT (pat, ty) ->
        let Core.PATTY (pat, ty'), ve = pat2core te ve pat in
        let s = unify [(ty2core te ty, ty')] in
        pattySub s (Core.PATTY (pat, ty')), veSub s ve

and pattySub s patty =
    match s with
    | [] -> patty
    | h :: t ->
        let Core.PATTY (pat, ty) = patty in
        (match pat with
        | Core.P_VIDP (vid, patty) -> pattySub t (Core.PATTY (Core.P_VIDP (vid, pattySub [h] patty), tySub [h] ty))
        | Core.P_PAIR (patty1, patty2) -> pattySub t (Core.PATTY (Core.P_PAIR (pattySub [h] patty1, pattySub [h] patty2), tySub [h] ty))
        | _ -> pattySub t (Core.PATTY (pat, tySub [h] ty)))

and exp2core te ve exp =
    match exp with
    | Ast.E_INT int -> Core.EXPTY (Core.E_INT int, Core.T_INT), []
    | Ast.E_BOOL bool -> Core.EXPTY (Core.E_BOOL bool, Core.T_BOOL), []
    | Ast.E_UNIT -> Core.EXPTY (Core.E_UNIT, Core.T_UNIT), []
    | Ast.E_PLUS -> Core.EXPTY (Core.E_PLUS, Core.T_FUN (Core.T_PAIR (Core.T_INT, Core.T_INT), Core.T_INT)), []
    | Ast.E_MINUS -> Core.EXPTY (Core.E_MINUS, Core.T_FUN (Core.T_PAIR (Core.T_INT, Core.T_INT), Core.T_INT)), []
    | Ast.E_MULT -> Core.EXPTY (Core.E_MULT, Core.T_FUN (Core.T_PAIR (Core.T_INT, Core.T_INT), Core.T_INT)), []
    | Ast.E_EQ -> Core.EXPTY (Core.E_EQ, Core.T_FUN (Core.T_PAIR (Core.T_INT, Core.T_INT), Core.T_BOOL)), []
    | Ast.E_NEQ -> Core.EXPTY (Core.E_NEQ, Core.T_FUN (Core.T_PAIR (Core.T_INT, Core.T_INT), Core.T_BOOL)), []
    | Ast.E_VID vid ->
        let (tyvars, ty), is = get (Dict.lookup vid ve) in
        let s = Set_type.fold (fun s tyvar -> (Core.T_VAR (freshTyvar ()), tyvar) :: s) [] tyvars in
        Core.EXPTY (Core.E_VID (vid, is), tySub s ty), []
    | Ast.E_FUN mlist ->
        let mlist, ty, s = mlist2core te ve mlist in
        Core.EXPTY (Core.E_FUN mlist, ty), s
    | Ast.E_APP (exp1, exp2) ->
        let Core.EXPTY (exp1, ty1), s1 = exp2core te ve exp1 in
        let Core.EXPTY (exp2, ty2), s2 = exp2core te (veSub s1 ve) exp2 in
        let tyvar = Core.T_VAR (freshTyvar ()) in
        let s3 = unify [(tySub s2 ty1, Core.T_FUN (ty2, tyvar))] in
        let s = s1 @ s2 @ s3 in
        Core.EXPTY (Core.E_APP (exptySub s (Core.EXPTY (exp1, ty1)), exptySub s (Core.EXPTY (exp2, ty2))), tySub s3 tyvar), s
    | Ast.E_PAIR (exp1, exp2) ->
        let Core.EXPTY (exp1, ty1), s1 = exp2core te ve exp1 in
        let Core.EXPTY (exp2, ty2), s2 = exp2core te (veSub s1 ve) exp2 in
        let s = s1 @ s2 in
        exptySub s (Core.EXPTY (Core.E_PAIR (Core.EXPTY (exp1, ty1), Core.EXPTY (exp2, ty2)), Core.T_PAIR (ty1, ty2))), s
    | Ast.E_LET (dec, exp) ->
        let dec, te', ve' = dec2core te ve dec in
        let Core.EXPTY (exp, ty), s = exp2core (Dict.merge te te') (Dict.merge ve ve') exp in
        Core.EXPTY (Core.E_LET (dec, Core.EXPTY (exp, ty)), ty), s
    | Ast.E_TEXP (exp, ty) ->
        let Core.EXPTY (exp, ty'), s = exp2core te ve exp in
        let s' = unify [(ty2core te ty, ty')] in
        exptySub (s @ s') (Core.EXPTY (exp, ty')), []

and exptySub s expty =
    match s with
    | [] -> expty
    | h :: t ->
        let Core.EXPTY (exp, ty) = expty in
        (match exp with
        | Core.E_FUN mlist -> exptySub t (Core.EXPTY (Core.E_FUN (mlistSub [h] mlist), tySub [h] ty))
        | Core.E_APP (expty1, expty2) -> exptySub t (Core.EXPTY (Core.E_APP (exptySub [h] expty1, exptySub [h] expty2), tySub [h] ty))
        | Core.E_PAIR (expty1, expty2) -> exptySub t (Core.EXPTY (Core.E_PAIR (exptySub [h] expty1, exptySub [h] expty2), tySub [h] ty))
        | Core.E_LET (dec, expty) -> exptySub t (Core.EXPTY (Core.E_LET (decSub [h] dec, exptySub [h] expty), tySub [h] ty))
        | _ -> exptySub t (Core.EXPTY (exp, tySub [h] ty)))

and mlist2core te ve mlist =
    match mlist with
    | h :: [] -> let mrule, ty, s = mrule2core te ve h in [mrule], ty, s
    | h :: t ->
        let Core.M_RULE (patty, expty), ty, _ = mrule2core te ve h in
        let mlist, ty', _ = mlist2core te ve t in
        let s = unify [(ty, ty')] in
        mlistSub s (Core.M_RULE (patty, expty) :: mlist), tySub s ty', s
    | _ -> raise TypingError

and mlistSub s mlist =
    match mlist with
    | [] -> []
    | Core.M_RULE (patty, expty) :: t -> Core.M_RULE (pattySub s patty, exptySub s expty) :: mlistSub s t

and mrule2core te ve mrule =
    match mrule with Ast.M_RULE (pat, exp) ->
    let Core.PATTY (pat, ty1), ve' = pat2core te ve pat in
    let Core.EXPTY (exp, ty2), s = exp2core te (Dict.merge ve ve') exp in
    Core.M_RULE (pattySub s (Core.PATTY (pat, ty1)), Core.EXPTY (exp, ty2)), Core.T_FUN (tySub s ty1, ty2), s

and dec2core te ve dec =
    let closure ve ve' =
        let rec tyvar ty =
            match ty with
            | Core.T_PAIR (ty1, ty2) | Core.T_FUN (ty1, ty2) -> Set_type.union (tyvar ty1) (tyvar ty2)
            | Core.T_VAR tyvar -> Set_type.singleton tyvar
            | _ -> Set_type.empty
        in
        let tyvar' ve =
            let rec tyvar'' range =
                match range with
                | ((tyvars, ty), _) :: t -> Set_type.union (Set_type.diff tyvars (tyvar ty)) (tyvar'' t)
                | [] -> Set_type.empty
            in
            tyvar'' (Dict.range ve)
        in
        let tyvarVE = tyvar' ve in
        let f ((tyvars, ty), is) = (Set_type.union (Set_type.diff (tyvar ty) tyvarVE) tyvars, ty), is in
        Dict.map f ve'
    in
    match dec with
    | Ast.D_VAL (pat, exp) ->
        let Core.PATTY (pat, ty1), ve' = pat2core te ve pat in
        let Core.EXPTY (exp, ty2), _ = exp2core te ve exp in
        let s = unify [(ty1, ty2)] in
        Core.D_VAL (pattySub s (Core.PATTY (pat, ty1)), exptySub s (Core.EXPTY (exp, ty2))), Dict.empty, closure ve (veSub s ve')
    | Ast.D_REC (pat, exp) ->
        let Core.PATTY (pat, ty1), ve' = pat2core te ve pat in
        let Core.EXPTY (exp, ty2), _ = exp2core te (Dict.merge ve ve') exp in
        let s = unify [(ty1, ty2)] in
        Core.D_REC (pattySub s (Core.PATTY (pat, ty1)), exptySub s (Core.EXPTY (exp, ty2))), Dict.empty, closure ve (veSub s ve')
    | Ast.D_DTYPE (tycon, conbind) ->
        let tyname = freshTyname () in
        let ve = conbind2core (Dict.insert (tycon, tyname) te) tyname conbind in
        Core.D_DTYPE, Dict.singleton (tycon, tyname), ve

and decSub s dec =
    match dec with
    | Core.D_VAL (patty, expty) -> Core.D_VAL (pattySub s patty, exptySub s expty)
    | Core.D_REC (patty, expty) -> Core.D_REC (pattySub s patty, exptySub s expty)
    | Core.D_DTYPE -> dec

and conbind2core te tyname conbind =
    match conbind with
    | Ast.CB_VID vid :: t ->
        Dict.insert (vid, ((Set_type.empty, Core.T_NAME tyname), Core.CON)) (conbind2core te tyname t)
    | Ast.CB_TVID (vid, ty) :: t ->
        Dict.insert (vid, ((Set_type.empty, Core.T_FUN (ty2core te ty, Core.T_NAME tyname)), Core.CONF)) (conbind2core te tyname t)
    | [] -> Dict.empty

(* tprogram : Ast.program -> Core.program *)
let tprogram (dlist, exp) =
    let f (dlist, te, ve) dec =
        let dec', te', ve' = dec2core te ve dec in
        dlist @ [dec'], Dict.merge te te', Dict.merge ve ve'
    in
    let dlist, te, ve = List.fold_left f ([], Dict.empty, Dict.empty) dlist in
    let expty, _ = exp2core te ve exp in
    dlist, expty
