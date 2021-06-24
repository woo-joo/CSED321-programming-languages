module type HW3 =
sig
  open Common

  exception NotImplemented

  exception IllegalFormat

  module Integer : SCALAR  with type t = int

  module Boolean : SCALAR with type t = bool

  module VectorFn (Scal : SCALAR) : VECTOR with type elem = Scal.t

  module MatrixFn (Scal : SCALAR) : MATRIX with type elem = Scal.t

  module ClosureFn (Mat : MATRIX) :
  sig
    val closure : Mat.t -> Mat.t
  end

  module BoolMat : MATRIX with type elem = bool

  module BoolMatClosure :
  sig
    val closure : BoolMat.t -> BoolMat.t
  end

  val reach : bool list list -> bool list list
  val al : bool list list
  val solution_al' : bool list list

  val distance : int list list -> int list list
  val dl : int list list
  val solution_dl' : int list list

  val weight : int list list -> int list list
  val ml : int list list
  val solution_ml' : int list list

end

module S = (Hw3sol : HW3)

module F (P : HW3)
  (ST : sig val name : string end) =
struct
  open P

  module SVec = S.VectorFn(S.Integer)
  module PVec = VectorFn(Integer)

  module SMat = S.MatrixFn(S.Integer)
  module PMat = MatrixFn(Integer)

  let _ = prerr_endline (ST.name ^ " --- ")

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
  | Illegal_Format
  | Vector_Illegal
  | Matrix_Illegal
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
      | IllegalFormat -> ret := Illegal_Format
      | PVec.VectorIllegal -> ret := Vector_Illegal
      | PMat.MatrixIllegal -> ret := Matrix_Illegal
      | BoolMat.MatrixIllegal -> ret := Matrix_Illegal
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
      | S.IllegalFormat -> Illegal_Format
      | SVec.VectorIllegal -> Vector_Illegal
      | SMat.MatrixIllegal -> Matrix_Illegal
      | S.BoolMat.MatrixIllegal -> Matrix_Illegal
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

  let test name score t f g l =
    let _ = prerr_string (name ^ " ") in
    let check f_r g_r =
      let (r,s) = gen_check_msg f_r g_r in
      (*let _ = prerr_string (s ^ " ") in*)
      r;
    in
    let s = if List.for_all (fun r -> r) (List.map (fun x -> try check (wrap_fun f x) (delayed_fun g x t) with _ -> false) l)
      then score else 0 in
    let _ = if s = score then prerr_endline ": passed" else prerr_endline ": failed"
    in s

  let test2 name score t f g l =
    let _ = prerr_string (name ^ " ") in
    let check f_r g_r =
      let (r,s) = gen_check_msg f_r g_r in
      (*let _ = prerr_string (s ^ " ") in*)
      r
    in
    let s = if List.for_all (fun r -> r) (List.map (fun (x,y) -> try check (wrap_fun f x) (delayed_fun g y t) with _ -> false) l)
      then score else 0 in
    let _ = if s = score then prerr_endline ": passed" else prerr_endline ": failed"
    in s

  let curry2 f (x,y) = f x y
  let curry3 f (x,y,z) = f x y z

  (* test Boolean *)

  let boolSumScore = test "Boolean.(++)" 4 1 (curry2 S.Boolean.(++)) (curry2 Boolean.(++)) [(true,false); (false,false)]

  let boolMulScore = test "Boolean.( ** )" 4 1 (curry2 S.Boolean.( ** )) (curry2 Boolean.( ** )) [(true,true); (true,false)]

  let boolEqScore =  test "Boolean.(==)" 2 1 (curry2 S.Boolean.(==)) (curry2 Boolean.(==)) [(true,false); (false,false)]

  let boolScore = boolSumScore + boolMulScore + boolEqScore

  let _ = prerr_string ("BoolScore : " ^ (string_of_int boolScore) ^ "\n")

  (* test Vector *)

  let sVecToList v =
    let d = SVec.dim v in
    let rec to_list v i =
      if (i < d) then [SVec.nth v i] @ to_list v (i+1)
      else []
    in to_list v 0

  let pVecToList v =
    let d = PVec.dim v in
    let rec to_list v i =
      if (i < d) then [PVec.nth v i] @ to_list v (i+1)
      else []
    in to_list v 0

  let testVec name score f g l =
    let _ = prerr_string (name ^ " ") in
    let testvec v =
      let pVec =
        try
          match (delayed_fun f v 1)
          with
            OK k -> pVecToList k
          | Vector_Illegal -> [-2]
          | _ -> [-3]
        with _ -> [-3]
      in
      let sVec =
        try
          match (wrap_fun g v)
          with
            OK k -> sVecToList k
          | Vector_Illegal -> [-2]
          | _ -> [-4]
        with _ -> [-4]
      in
      pVec = sVec
    in
    let s = if (List.for_all testvec l) then score else 0  in
    let _ = if s = score then prerr_endline ": passed" else prerr_endline ": failed"
    in s

  let testVec2 name score f g l =
    let _ = prerr_string (name ^ " ") in
    let testvec v =
      let pVec =
        try
          match (delayed_fun (curry2 f) ((PVec.create [1;2;3]),(PVec.create v)) 1)
          with
            OK k -> pVecToList k
          | Vector_Illegal -> [-2]
          | _ -> [-3]
        with PVec.VectorIllegal -> [-2]
        | _ -> [-3]
      in
      let sVec =
        try
          match (wrap_fun (curry2 g) ((SVec.create [1;2;3]),(SVec.create v)))
          with
            OK k -> sVecToList k
          | Vector_Illegal -> [-2]
          | _ -> [-4]
        with SVec.VectorIllegal -> [-2]
        | _ -> [-3]
      in
      pVec = sVec
    in
    let s = if (List.for_all testvec l) then score else 0 in
    let _ = if s = score then prerr_endline ": passed" else prerr_endline ": failed"
    in s

  let testVec3 name score f g l =
    let _ = prerr_string (name ^ " ") in
    let testvec v =
      let pVec =
        try
          match (delayed_fun f (PVec.create v) 1) with
            OK k -> k
          | _ -> -1
        with _ -> -1
      in
      let sVec =
        try
          match (wrap_fun g (SVec.create v)) with
            OK k -> k
          | _ -> -2
        with _ -> -2
      in
      pVec = sVec
    in
    let s = if (List.for_all testvec l) then score else 0 in
    let _ = if s = score then prerr_endline ": passed" else prerr_endline ": failed"
    in s

  let testVec4 name score f g l =
    let _ = prerr_string (name ^ " ") in
    let testvec (v1,v2) =
      let pVec =
        try
          match (delayed_fun (curry2 f) ((PVec.create v1), v2) 1)
          with
            OK k -> k
          | Vector_Illegal -> -2
          | _ -> -3
        with PVec.VectorIllegal -> -2
        | _ -> -3
      in
      let sVec =
        try
          match (wrap_fun (curry2 g) ((SVec.create v1), v2))
          with
            OK k-> k
          | Vector_Illegal -> -2
          | _ -> -4
        with SVec.VectorIllegal -> -2
        | _ -> -4
      in
      pVec = sVec
    in
    let s = if List.for_all (fun r -> r) (List.map (fun x -> testvec x) l) then score else 0 in
    let _ = if s = score then prerr_endline ": passed" else prerr_endline ": failed"
    in s

  let testVec5 name score f g l =
    let _ = prerr_string (name ^ " ") in
    let testvec v =
      let pVec =
        try
          match (delayed_fun (curry2 f) ((PVec.create [1;2;3]), (PVec.create v)) 1)
          with
            OK k -> k
          | Vector_Illegal -> true
          | _ -> false
        with PVec.VectorIllegal -> true
        | _ -> false
      in

      let sVec =
        try
          match (wrap_fun (curry2 g) ((SVec.create [1;2;3]), (SVec.create v)))
          with OK k -> k
          | Vector_Illegal -> true
          | _ -> true
        with SVec.VectorIllegal -> true
        | _ -> true
      in
      pVec = sVec
    in
    let s = if (List.for_all testvec l) then score else 0 in
    let _ = if s = score then prerr_endline ": passed" else prerr_endline ": failed"
    in s

  let testVec6 name score f g l =
    let _ = prerr_string (name ^ " ") in
    let testvec v =
      let pVec = try
                   match (delayed_fun (curry2 f) ((PVec.create [1;2;3]), (PVec.create v)) 1)
                   with
                     OK k -> k
                   | Vector_Illegal -> -2
                   | _ -> -3
        with PVec.VectorIllegal -> -2
        | _ -> -3
      in
      let sVec =
        try
          match (wrap_fun (curry2 g) ((SVec.create [1;2;3]), (SVec.create v)))
          with OK k -> k
          | Vector_Illegal -> -2
          | _ -> -4
        with SVec.VectorIllegal -> -2
        | _ -> -4
      in
      pVec = sVec
    in
    let s = if (List.for_all testvec l) then score else 0 in
    let _ = if s = score then prerr_endline ": passed" else prerr_endline ": failed"
    in s

  let vecCreateScore = testVec "Vector.create" 3 PVec.create SVec.create [[];[1];[1;2;3]]

  let vecSumScore = testVec2 "Vector++" 4 PVec.(++) SVec.(++) [[];[1];[1;2;3];[10;20;30]]

  let vecDimScore = testVec3 "Vector.dim" 3 PVec.dim SVec.dim [[1];[1;2;3];[10;20;30;40]]

  let vecNthScore = testVec4 "Vector.nth" 3 PVec.nth SVec.nth [([1],0);([1;2;3],2);([10;20;30;40],5)]

  let vecEqScore = testVec5 "Vector.(==)" 3 PVec.(==) SVec.(==) [[];[1];[1;2;3];[10;20;30]]

  let vecInnepScore = testVec6 "Vector.innerp" 4 PVec.innerp SVec.innerp [[];[1];[1;2;3];[10;20;30]]

  let vecScore = vecCreateScore + vecSumScore + vecDimScore + vecNthScore + vecInnepScore + vecEqScore

  let _ = prerr_string ("VectorScore : " ^ (string_of_int vecScore) ^ "\n")

  (* test Matrix *)

  let rec init n = if n = 0 then [] else (init (n - 1)) @ [n]

  let pMatToList m = List.map (fun r -> List.map (fun c -> PMat.get m (r-1) (c-1)) (init (PMat.dim m))) (init (PMat.dim m))

  let sMatToList m = List.map (fun r -> List.map (fun c -> SMat.get m (r-1) (c-1)) (init (SMat.dim m))) (init (SMat.dim m))

  let testMat name score f g l =
    let _ = prerr_string (name ^ " ") in
    let testmat v =
      let pmat =
        try
          match (delayed_fun f v 1)
          with OK k -> pMatToList k
          | Matrix_Illegal -> [[-2]]
          | _ -> [[-3]]
        with  _ -> [[-3]]
      in
      let smat =
        try
          match (wrap_fun g v)
          with
            OK k -> sMatToList k
          | Matrix_Illegal -> [[-2]]
          | _ -> [[-4]]
        with _ -> [[-4]]
      in
      pmat = smat
    in
    let s = if (List.for_all testmat l) then score else 0 in
    let _ = if s = score then prerr_endline ": passed" else prerr_endline ": failed"
    in s


  let testMat2 name score f g l =
    let _ = prerr_string (name ^ " ") in
    let testmat v =
      let pmat =
        try
          match (delayed_fun f (PMat.create v) 1)
          with OK k -> k
          | _ -> -1
        with _ -> -1
      in
      let smat =
        try
          match (wrap_fun g (SMat.create v))
          with OK k -> k
          | _ -> -2
        with _ -> -2
      in
      pmat = smat
    in
    let s = if (List.for_all testmat l) then score else 0 in
    let _ = if s = score then prerr_endline ": passed" else prerr_endline ": failed"
    in s


  let testMat3 name score f g l =
    let _ = prerr_string (name ^ " ") in
    let testmat v =
      let pmat =
        try
          match (delayed_fun f (PMat.create v) 1)
          with OK k -> pMatToList k
          | _ -> [[-1]]
        with _ -> [[-1]]
      in
      let smat =
        try
          match (wrap_fun g (SMat.create v))
          with OK k -> sMatToList k
          | _ -> [[-2]]
        with _ -> [[-1]]
      in
      pmat = smat
    in
    let s = if List.for_all testmat l then score else 0 in
    let _ = if s = score then prerr_endline ": passed" else prerr_endline ": failed"
    in s


  let testMat4 name score f g l =
    let _ = prerr_string (name ^ " ") in
    let testmat (v1,v2,v3) =
      let pmat =
        try
          match (delayed_fun (curry3 f) ((PMat.create v1), v2, v3) 1)
          with OK k -> k
          | Matrix_Illegal -> -2
          | _ -> -3
        with PMat.MatrixIllegal -> -2
        | _ -> -3
      in
      let smat = try
                   match (wrap_fun (curry3 g) ((SMat.create v1), v2, v3))
                   with
                     OK k -> k
                   | Matrix_Illegal -> -2
                   | _ -> -4
        with SMat.MatrixIllegal -> -2
        | _ -> -4
      in
      pmat = smat
    in
    let s = if (List.for_all testmat l) then score else 0 in
    let _ = if s = score then prerr_endline ": passed" else prerr_endline ": failed"
    in s

  let testMat5 name score f g ll =
    let _ = prerr_string (name ^ " ") in
    let testmat l =
      let pmat =
        try
          match (delayed_fun (curry2 f) ((PMat.create [[1;2;3];[4;5;6];[7;8;9]]), (PMat.create l)) 1)
          with
            OK k -> pMatToList k
          | Matrix_Illegal -> [[-2]]
          | _ -> [[-3]]
        with PMat.MatrixIllegal -> [[-2]]
        | _ -> [[-3]]
      in
      let smat = try
                   match (wrap_fun (curry2 g) ((SMat.create [[1;2;3];[4;5;6];[7;8;9]]), (SMat.create l)))
                   with OK k-> sMatToList k
                   | Matrix_Illegal -> [[-2]]
                   | _ -> [[-4]]
        with SMat.MatrixIllegal -> [[-2]]
        | _ -> [[-4]]
      in
      pmat = smat
    in
    let s = if (List.for_all testmat ll) then score else 0 in
    let _ = if s = score then prerr_endline ": passed" else prerr_endline ": failed"
    in s

  let testMat6 name score f g ll =
    let _ = prerr_string (name ^ " ") in
    let testmat l =
      let pmat =
        try
          match (delayed_fun (curry2 f) ((PMat.create [[1;2;3];[4;5;6];[7;8;9]]), (PMat.create l)) 1)
          with OK k-> k
          | Matrix_Illegal -> true
          | _ -> false
        with PMat.MatrixIllegal -> true
        | _ -> false
      in
      let smat =
        try
          match (wrap_fun (curry2 g) ((SMat.create [[1;2;3];[4;5;6];[7;8;9]]), (SMat.create l)))
          with OK k-> k
          | Matrix_Illegal -> true
          | _ -> true
        with SMat.MatrixIllegal -> true
        | _ -> true
      in
      pmat = smat
    in
    let s = if (List.for_all testmat ll) then score else 0 in
    let _ = if s = score then prerr_endline ": passed" else prerr_endline ": failed"
    in s

  let matCreateScore = testMat "Matrix.create" 3 PMat.create SMat.create [[];[[1;2;3];[4;5;6]];[[1;2;3];[4;5;6];[7;8;9]]]

  let matIdentityScore = testMat "Matrix.identity" 5 PMat.identity SMat.identity [-1;0;1;2;3]

  let matDimScore = testMat2 "Matrix.dim" 3 PMat.dim SMat.dim [[[1;2;3];[4;5;6];[7;8;9]]]

  let matTransScore = testMat3 "Matrix.transpose" 5 PMat.transpose SMat.transpose [[[1;2;3];[4;5;6];[7;8;9]]]

  let matGetScore = testMat4 "Matrix.get" 3 PMat.get SMat.get
    [([[1]],0,0); ([[1;2;3];[4;5;6];[7;8;9]],1,2); ([[1;2;3];[4;5;6];[7;8;9]],5,3)]

  let matSumScore = testMat5 "Matrix.++" 3 PMat.(++) SMat.(++)
    [[[1;2];[3]];
     [[1;2;3];[4;5;6];[7;8;9]];
     [[1;2;3;4];[4;5;6;7];[7;8;9;10];[11;12;13;14]]]

  let matMulScore = testMat5 "Matrix.( ** )" 5 PMat.( ** ) SMat.( ** )
    [[[1;2];[3]];
     [[1;2;3];[4;5;6];[7;8;9]];
     [[1;2;3;4];[4;5;6;7];[7;8;9;10];[11;12;13;14]]]

  let matEqScore = testMat6 "Matrix.(==)" 3 PMat.((==)) SMat.((==))
    [[[1;2];[3]];
     [[1;2;3];[4;5;6];[7;8;9]];
     [[1;2;3;4];[4;5;6;7];[7;8;9;10];[11;12;13;14]]]
  let matToListScore =
    let _ = prerr_string ("Matrix.to_list" ^ " ") in
    let data = [[1;2;3];[4;5;6];[7;8;9]] in
    let s = try if data = pMatToList (PMat.create data) then 5
      else 0
      with _ -> 0 in
    let _ = if s = 5 then prerr_endline ": passed" else prerr_endline ": failed"
    in s

  let matScore = matCreateScore + matDimScore + matTransScore + matGetScore
    + matSumScore + matMulScore + matEqScore + matIdentityScore
    + matToListScore

  let _ = prerr_string ("MatrixScore : " ^ (string_of_int matScore) ^ "\n")

  (* test Closure *)

  let pBoolMatToList m = List.map (fun r -> List.map (fun c -> BoolMat.get m (r-1) (c-1)) (init (BoolMat.dim m)))
    (init (BoolMat.dim m))

  let sBoolMatToList m = List.map (fun r -> List.map (fun c -> S.BoolMat.get m (r-1) (c-1)) (init (S.BoolMat.dim m)))
    (init (S.BoolMat.dim m))

  let testClosure name score test_l =
    let _ = prerr_string (name ^ " ") in
    let testclosure c =
      let pmat =
        try
          match (delayed_fun BoolMatClosure.closure (BoolMat.create c) 1)
          with
            OK k -> pBoolMatToList k
          | Matrix_Illegal -> [[false]]
          | _ -> [[true;false]]
        with BoolMat.MatrixIllegal -> [[false]]
        | _ -> [[true;false]]
      in
      let smat = try
                   match  (wrap_fun S.BoolMatClosure.closure (S.BoolMat.create c))
                   with
                     OK k -> sBoolMatToList k
                   | Matrix_Illegal -> [[false]]
                   | _ -> [[true;true]]
        with S.BoolMat.MatrixIllegal -> [[false]]
        | _ -> [[true;true]]
      in
      pmat = smat
    in
    let s = if (List.for_all testclosure test_l) then score else 0 in
    let _ = if s = score then prerr_endline ": passed" else prerr_endline ": failed"
    in s


  let testReach name score f g l =
    let _ = prerr_string (name ^ " ") in
    let testReach' x =
      let p =
        try
          match (delayed_fun f x 1) with
            OK k -> k
          | Illegal_Format -> [[false]]
          | _ -> [[true];[false]]
        with _ -> [[true];[false]]
      in
      let s =
        try
          match (wrap_fun g x)  with
            OK k -> k
          | Illegal_Format -> [[false]]
          | _ -> [[true];[true]]
        with _ -> [[true];[true]]
      in
      p = s
    in
    let s =  if (List.for_all (fun x -> testReach' x) l) then score else 0 in
    let _ = if s = score then prerr_endline ": passed" else prerr_endline ": failed"
    in s


  let testDistWeight name score f g l =
    let _ = prerr_string (name ^ " ") in
    let testReach' x =
      let p =
        try
          match (delayed_fun f x 1)
          with OK k-> k
          | Illegal_Format -> [[-2]]
          | _ -> [[-3]]
        with _ -> [[-3]]
      in
      let s =
        try
          match (wrap_fun g x)
          with OK k-> k
          | Illegal_Format -> [[-2]]
          | _ -> [[-4]]
        with  _ -> [[-4]]
      in
      p = s
    in
    let s = if (List.for_all (fun x -> testReach' x) l) then score else 0 in
    let _ = if s = score then prerr_endline ": passed" else prerr_endline ": failed"
    in s



  let closureScore =
    let test1 = testClosure "closure" 10 [al] in
    let test2 = testClosure "closure" 1 [[];[[true;false;true]]] in
    if test2 <> 1 && test1 <> 0 then test1 - 3 else test1

  let _ = prerr_string ("ClosureScore : " ^ (string_of_int closureScore) ^ "\n")

  let reachScore =
    let test1 = testReach "reach" 5 reach S.reach [al] in
    let test2 = testReach "reach" 1 reach S.reach [[];[[true];[false]]] in
    if test2 <> 1 && test1 <> 0 then test1 - 3
    else test1

  let _ = prerr_string ("ReachScore : " ^ (string_of_int reachScore) ^ "\n")

  let distScore =
    let test1 = testDistWeight "distance" 10 distance S.distance [dl] in
    let test2 = testDistWeight "distance" 1 distance S.distance [[];[[1;2]]] in
    if test2 <> 1 && test1 <> 0 then test1 - 3
    else test1

  let _ = prerr_string ("DistanceScore : " ^ (string_of_int distScore) ^ "\n")

  let weightScore =
    let test1 = testDistWeight "weight" 10 weight S.weight [ml] in
    let test2 = testDistWeight "weight" 1 weight S.weight [[];[[1;2]]] in
    if test2 <> 1 && test1 <> 0 then test1 - 3
    else test1

  let _ = prerr_string ("WeightScore : " ^ (string_of_int weightScore) ^ "\n")


  let score = boolScore + vecScore + matScore +
    closureScore +  reachScore + distScore + weightScore

  let _ = flush_all ();
    print_string (ST.name ^ " ");
    print_int score;
    print_newline ()

end;;

module Hfoo = F (Hw3) (struct let name = "Test score" end);;
