open Common

exception NotImplemented

exception IllegalFormat

module Integer : SCALAR with type t = int
=
struct
    type t = int

    exception ScalarIllegal

    let zero = 0
    let one = 1

    let (++) x y = x + y
    let ( ** ) x y = x * y
    let (==) x y = x = y 
end

(* Problem 1-1 *)
(* Scalars *)

module Boolean : SCALAR with type t = bool 
=
struct
    type t = bool

    exception ScalarIllegal

    let zero = false
    let one = true

    let (++) x y = x || y
    let ( ** ) x y = x && y
    let (==) x y = x = y
end

(* Problem 1-2 *)
(* Vectors *)

module VectorFn (Scal : SCALAR) : VECTOR with type elem = Scal.t
=
struct
    type elem = Scal.t
    type t = elem list

    exception VectorIllegal

    let create l =
        match l with
        | [] -> raise VectorIllegal
        | _ -> l
    let to_list v = v
    let dim v = List.length v
    let nth v n =
        try
            List.nth v n
        with Failure _ | Invalid_argument _ -> raise VectorIllegal
    let (++) v1 v2 =
        try
            List.map2 (fun e1 e2 -> Scal.(++) e1 e2) v1 v2
        with Invalid_argument _ -> raise VectorIllegal
    let (==) v1 v2 =
        try
            List.for_all2 (fun e1 e2 -> Scal.(==) e1 e2) v1 v2
        with Invalid_argument _ -> raise VectorIllegal
    let innerp v1 v2 =
        try
            List.fold_left2 (fun acc e1 e2 -> Scal.(++) acc (Scal.( ** ) e1 e2)) Scal.zero v1 v2
        with Invalid_argument _ -> raise VectorIllegal
end

(* Problem 1-3 *)
(* Matrices *)

module MatrixFn (Scal : SCALAR) : MATRIX with type elem = Scal.t
=
struct
    module Vec = VectorFn(Scal)

    type elem = Scal.t
    type t = Vec.t list

    exception MatrixIllegal

    let create l =
        match l with
        | [] -> raise MatrixIllegal
        | _ -> List.map (fun l_ -> if List.length l_ = List.length l then Vec.create l_ else raise MatrixIllegal) l
    let identity d =
        if d <= 0
        then raise MatrixIllegal
        else List.init d (fun i -> Vec.create (List.init d (fun i_ -> if i = i_ then Scal.one else Scal.zero)))
    let dim m = List.length m
    let transpose m =
        let d = dim m in
        List.init d (fun i -> Vec.create (List.init d (fun i_ -> Vec.nth (List.nth m i_) i)))
    let to_list m =
        let rec to_list_aux m acc =
            match m with
            | [] -> acc
            | h :: t -> to_list_aux t (acc @ [Vec.to_list h])
        in to_list_aux m []
    let get m r c =
        try
            Vec.nth (List.nth m r) c
        with Failure _ | Invalid_argument _ | Vec.VectorIllegal -> raise MatrixIllegal

    let (++) m1 m2 =
        try
            List.map2 (fun v1 v2 -> Vec.(++) v1 v2) m1 m2
        with Invalid_argument _ | Vec.VectorIllegal -> raise MatrixIllegal
    let ( ** ) m1 m2 =
        try
            List.map (fun v1 -> Vec.create (List.map (fun v2 -> Vec.innerp v1 v2) (transpose m2))) m1
        with Invalid_argument _ | Vec.VectorIllegal -> raise MatrixIllegal
    let (==) m1 m2 =
        try
            List.for_all2 (fun v1 v2 -> Vec.(==) v1 v2) m1 m2
        with Invalid_argument _ | Vec.VectorIllegal -> raise MatrixIllegal
end

(* Problem 2-1 *)
(* Closure *)

module ClosureFn (Mat : MATRIX) :
sig
    val closure : Mat.t -> Mat.t
end
=
struct
    let closure m =
        let i = Mat.identity (Mat.dim m) in
        let rec closure_aux acc =
            let acc2 = Mat.(++) i (Mat.( ** ) acc m) in
            if Mat.(==) acc acc2
            then acc
            else closure_aux acc2
        in closure_aux i
end

(* Problem 2-2 *)
(* Applications to Graph Problems *)

module BoolMat = MatrixFn (Boolean)
module BoolMatClosure = ClosureFn (BoolMat)

let reach d =
    try
        BoolMat.to_list (BoolMatClosure.closure (BoolMat.create d))
    with BoolMat.MatrixIllegal -> raise IllegalFormat

let al = 
    [[true;  false; false; false; false; false];
     [false; true;  true;  true;  false; false];
     [false; true;  true;  false; true;  false];
     [false; true;  false; true;  true;  true];
     [false; false; true;  true;  true;  false];
     [false; false; false; true;  false; true]]

let solution_al' = 
    [[true;  false; false; false; false; false];
     [false; true;  true;  true;  true;  true];
     [false; true;  true;  true;  true;  true];
     [false; true;  true;  true;  true;  true];
     [false; true;  true;  true;  true;  true];
     [false; true;  true;  true;  true;  true]]

module Distance : SCALAR with type t = int
=
struct
    type t = int

    exception ScalarIllegal

    let zero = -1
    let one = 0

    let (++) x y = if x = zero || y = zero then max x y else min x y
    let ( ** ) x y = if x = zero || y = zero then zero else x + y
    let (==) x y = x = y
end

module DistMat = MatrixFn (Distance)
module DistMatClosure = ClosureFn (DistMat)

let distance e =
    try
        DistMat.to_list (DistMatClosure.closure (DistMat.create e))
    with DistMat.MatrixIllegal -> raise IllegalFormat

let dl =
    [[  0;  -1;  -1;  -1;  -1;  -1 ];
     [ -1; 0  ; 35 ; 200; -1 ; -1  ];
     [ -1; 50 ; 0  ; -1 ; 150; -1  ];
     [ -1; 75;  -1 ; 0  ; 100; 25  ];
     [ -1; -1 ; 50 ; 65 ; 0  ; -1  ];
     [ -1; -1 ; -1 ; -1 ; -1 ; 0   ]]

let solution_dl' =
    [[0;  -1;  -1;  -1;  -1;  -1  ];
     [-1; 0;   35;  200; 185; 225 ];
     [-1; 50;  0;   215; 150; 240 ];
     [-1; 75;  110; 0;   100; 25  ];
     [-1; 100; 50;  65;  0;   90  ];
     [-1; -1;  -1;  -1;  -1;  0   ]]

module Weight : SCALAR with type t = int
=
struct
    type t = int

    exception ScalarIllegal

    let zero = 999999               (* Dummy value : Rewrite it! *)
    let one = 999999                (* Dummy value : Rewrite it! *)
    
    let (++) _ _ = raise NotImplemented
    let ( ** ) _ _ = raise NotImplemented
    let (==) _ _ = raise NotImplemented
end

(* .. Write some code here .. *)

let weight _ = raise NotImplemented

let ml =
    [[-1; 0  ; 0  ; 0  ; 0  ; 0   ];
     [0 ; -1 ; 10 ; 100; 0  ; 0   ];
     [0 ; 50 ; -1 ; 0  ; 150; 0   ];
     [0 ; 75 ; 0  ; -1 ; 125; 40 ];
     [0 ; 0  ; 25 ; -1 ; -1 ; 0   ];
     [0 ; 0  ; 0  ; 0  ; 0  ; -1  ]]

let solution_ml' =
    [[-1; 0;  0;   0;   0;   0  ];
     [0;  -1; 25;  100; 100; 40 ];
     [0;  75; -1;  150; 150; 40 ];
     [0;  75; 25;  -1;  125; 40 ];
     [0;  75; 25;  -1;  -1;  40 ];
     [0;  0;  0;   0;   0;   -1 ]]

let _ =
    try 
    if reach al = solution_al' && distance dl = solution_dl' && weight ml = solution_ml' then
        print_endline "\nYour program seems fine (but no guarantee)!"
    else
        print_endline "\nYour program might have bugs!"
    with _ -> print_endline "\nYour program is not complete yet!" 
