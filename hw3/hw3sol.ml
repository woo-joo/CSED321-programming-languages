open Common

exception NotImplemented

module Integer : (SCALAR with type t = int) =
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

module Boolean : (SCALAR with type t = bool) =
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

module VectorFn (Scal : SCALAR) : (VECTOR with type elem = Scal.t)=
  struct
    type elem = Scal.t
    type t = elem list
                  
    exception VectorIllegal
                
    let create l = match l with
        [] -> raise VectorIllegal
      | _ -> l

    let to_list t = t

    let dim t = List.length t

    let rec nth t n = try List.nth t n
                      with _ -> raise VectorIllegal
                                      
    let rec (++) t1 t2 = if dim t1 <> dim t2 then raise VectorIllegal
                         else List.map2 (fun x y -> Scal.(++) x y) t1 t2
                                        
    let rec (==) t1 t2 = if dim t1 <> dim t2 then raise VectorIllegal
                         else List.for_all2 (fun x y -> Scal.(==) x y) t1 t2
                                            
    let rec innerp t1 t2 = if dim t1 <> dim t2 then raise VectorIllegal
                           else List.fold_left2 (fun x y z -> Scal.(++) x ( Scal.( ** ) y z )) Scal.zero t1 t2
                                                
  end

(* Problem 1-3 *)
(* Matrices *)

module MatrixFn (Scal : SCALAR) : (MATRIX with type elem = Scal.t) =
  struct                        
    module Vec = VectorFn (Scal)

    type elem = Scal.t
    type t = Vec.t list

    exception MatrixIllegal 
                
    let rec create l = match l with
        [] -> raise MatrixIllegal
      | _ -> List.map (fun x -> if List.length l = List.length x then Vec.create x else raise MatrixIllegal) l
                      
    let rec init n = if n = 0 then []
                     else (init (n - 1)) @ [n]
                                             
    let identity n = if n <= 0 then raise MatrixIllegal 
                     else List.map (fun c -> Vec.create 
                                               (List.map (fun r -> if r = c then Scal.one else Scal.zero) (init n)) ) 
                                   (init n) 

    let dim t = List.length t

    let rec to_list t = match t with
        [] -> []
      | x :: xs -> (Vec.to_list x) :: (to_list xs)

    let transpose t = List.map (fun c -> let t' = t in Vec.create 
                                                         (List.map (fun r -> Vec.nth r (c-1)) t') )
                               (init (dim t))                      

    let get t r c = try Vec.nth (List.nth t r) c
                    with _ -> raise MatrixIllegal

    let (++) t1 t2 =  if dim t1 <> dim t2 then raise MatrixIllegal
                      else List.map2 (fun x y -> Vec.(++) x y) t1 t2
                                     
    let ( ** ) t1 t2 = if dim t1 <> dim t2 then raise MatrixIllegal 
                       else List.map (fun x -> Vec.create ( 
                                                   List.map (fun y -> Vec.innerp x y) (transpose t2) ) ) 
                                     t1
                                     
    let (==) t1 t2 = if dim t1 <> dim t2 then raise MatrixIllegal
                     else List.for_all2 (fun x y -> Vec.(==) x y) t1 t2
                                        
  end

(* Problem 2-1 *)
(* Closure *)

module ClosureFn (Mat : MATRIX) : (sig val closure : Mat.t -> Mat.t end) =
  struct
    let closure a = 
      let i = Mat.identity (Mat.dim a) in
      let rec closure_rev curr = 
        let next = Mat.(++) i (Mat.( ** ) curr a) in
        if Mat.(==) curr next then curr
        else closure_rev next
      in
      closure_rev i
  end
    
(* Problem 2-2 *)
(* Applications to Graph Problems *)

exception IllegalFormat 

module BoolMat = MatrixFn (Boolean)

module BoolMatClosure = ClosureFn (BoolMat)
                                  
let reach bll = try BoolMat.to_list ( BoolMatClosure.closure ( BoolMat.create bll ) )
                with _ -> raise IllegalFormat

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

module Distance : (SCALAR with type t = int) =
  struct
    type t = int
               
    exception ScalarIllegal
                
    let zero = -1                (* Dummy value : Rewrite it! *)

    let one = 0                 (* Dummy value : Rewrite it! *)
                
    let (++) x y = if x = zero then y
                   else if y = zero then x
                   else min x y

    let ( ** ) x y = if x = zero || y = zero then zero
                     else x + y

    let (==) x y = x = y
  end
    
module DisMat = MatrixFn (Distance)

module DisMatClosure = ClosureFn (DisMat)

let distance ill = try DisMat.to_list ( DisMatClosure.closure ( DisMat.create ill ) )
                   with _ -> raise IllegalFormat
                                   
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
    
module Weight : (SCALAR with type t = int) =
  struct
    type t = int
               
    exception ScalarIllegal
                
    let zero = 0                (* Dummy value : Rewrite it! *)

    let one = -1                (* Dummy value : Rewrite it! *)
                 
    let (++) x y = if x = one || y = one then one
                   else max x y

    let ( ** ) x y = if x = one then y 
                     else if y = one then x
                     else min x y

    let (==) x y = x = y
                         
  end
    
module WeiMat = MatrixFn (Weight)

module WeiMatClosure = ClosureFn (WeiMat)

let weight ill = try WeiMat.to_list ( WeiMatClosure.closure ( WeiMat.create ill ) )
                 with _ -> raise IllegalFormat

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
