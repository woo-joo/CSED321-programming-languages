module type HW1 =
sig
  exception Not_implemented

  type 'a tree = Leaf of 'a | Node of 'a tree * 'a * 'a tree
      
  val sum : int -> int
  val fac : int -> int
  val fib : int -> int
  val gcd : int -> int -> int
  val max : int list -> int

  val sum_tree : int tree -> int
  val depth : 'a tree -> int
  val bin_search : int tree -> int -> bool
  val preorder : 'a tree -> 'a list

  val list_add : int list -> int list -> int list
  val insert : int -> int list -> int list
  val insort : int list -> int list

  val compose : ('a -> 'b) -> ('b -> 'c) -> ('a -> 'c)
  val curry : ('a * 'b -> 'c) -> ('a -> 'b -> 'c)
  val uncurry : ('a -> 'b -> 'c) -> ('a * 'b -> 'c)
  val multifun : ('a -> 'a) -> int -> ('a -> 'a)

  val ltake : 'a list -> int -> 'a list
  val lall : ('a -> bool) -> 'a list -> bool
  val lmap : ('a -> 'b) -> 'a list -> 'b list
  val lrev : 'a list -> 'a list
  val lzip : 'a list -> 'b list -> ('a * 'b) list
  val split : 'a list -> 'a list * 'a list
  val cartprod : 'a list -> 'b list -> ('a * 'b) list
end;;

module S = (Hw1sol : HW1);;

module F (P : HW1) (ST : sig val name : string end) =
struct
  open S

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

  (* test : string -> int -> ('a -> 'b) -> ('a -> 'b) -> 'a list *)
  let test name score t f g l =
    let _ = prerr_string (name ^ " ") in
    let check f_r g_r =
      let (r,s) = gen_check_msg f_r g_r in
      let _ = prerr_string (s ^ " ") in
      r;
    in
    let s = if List.for_all (fun r -> r) (List.map (fun x -> try check (wrap_fun f x) (delayed_fun g x t) with _ -> false) l)
      then score else 0 in
    let _ = if s = score then prerr_endline ": passed" else prerr_endline ": failed"
    in s

  (* test : string -> int -> ('a -> 'b) -> ('c -> 'b) -> ('a * 'c) list *)
  let test2 name score t f g l =
    let _ = prerr_string (name ^ " ") in
    let check f_r g_r =
      let (r,s) = gen_check_msg f_r g_r in
      let _ = prerr_string (s ^ " ") in
      r
    in
    let s = if List.for_all (fun r -> r) (List.map (fun (x,y) -> try check (wrap_fun f x) (delayed_fun g y t) with _ -> false) l)
      then score else 0 in
    let _ = if s = score then prerr_endline ": passed" else prerr_endline ": failed"
    in s

  let curry2 f (x,y) = f x y

  let sumScore = test "sum" 4 1 sum P.sum [1;5;10]

  let facScore = test "fac" 4 1 fac P.fac [1; 5; 10 ]

  let fibScore = test "fib" 3 1 fib P.fib [0; 1; 4; 10]

  let gcdScore = test "gcd" 4 1 (curry2 gcd) (curry2 P.gcd) [(15,20); (24,12); (10000,0)]

  let maxScore = test "max" 4 1 max P.max [[];[4;3;5;3;2];[-10;-100;-20]]

  let sumTreeScore = test2 "sum_tree" 4 1 sum_tree P.sum_tree
    [(Node(Node(Leaf 1,3,Leaf 2), 7, Leaf 4),
      P.Node(P.Node(P.Leaf 1,3,P.Leaf 2), 7, P.Leaf 4))]

  let depthScore = test2 "depth" 4 1 depth P.depth
    [(Node(Node(Leaf 1,3,Leaf 2), 7, Leaf 4),
      P.Node(P.Node(P.Leaf 1,3,P.Leaf 2), 7, P.Leaf 4))]

  let binSearchScore = test "bin_search" 4 1
    (bin_search (Node(Node(Leaf 1,2,Leaf 3), 4, Leaf 7)))
    (P.bin_search (P.Node(P.Node(P.Leaf 1,2,P.Leaf 3), 4, P.Leaf 7)))
    [2; 5]

  let preorderScore = test2 "preorder" 4 1 preorder P.preorder
    [(Node(Node(Leaf 1,3,Leaf 2), 7, Leaf 4),
      P.Node(P.Node(P.Leaf 1,3,P.Leaf 2), 7, P.Leaf 4))]

  let listAddScore = test "list_add" 4 1 (curry2 list_add) (curry2 P.list_add)
    [([],[]);([],[1;2]);([4;5],[]);([1;2],[3; 4]); ([1; 2; 3], [4; 5]); ([1; 2],[3; 4; 5])]

  let insertScore = test "insert" 4 1 (insert 3) (P.insert 3) [[];[1];[1;2;4;5];[2;6;8;10;15]]

  let insortScore = test "insort" 4 1 insort P.insort [[];[1];[1;4;5;3];[10;18;3;-5;12]]

  let composeScore =
    let f = (fun x -> x + 1) in
    let g = (fun x -> x * 5) in
    try test "compose" 4 1 (fun x -> g (f x)) (P.compose f g) [0;5;10]
    with _ -> (prerr_string "compose : failed \n"; 0)

  let curryScore =
    let multiply (x,y) = x * y in
    try test "curry" 4 1 (curry multiply 5) (P.curry multiply 5) [3]
    with _ -> (prerr_string "curry : failed \n "; 0)

  let uncurryScore =
    let multiply x y = x * y in
    try test "uncurry" 4 1 (uncurry multiply) (P.uncurry multiply) [(3,5)]
    with _ -> (prerr_string "uncurry : failed \n "; 0)

  let multifunScore =
    let f = fun x -> x * x in
    try test "multifun" 4 1 (multifun f 3) (P.multifun f 3) [2;3]
    with _ -> (prerr_string "multifun : failed \n"; 0)

  let ltakeScore = test "ltake" 4 1
    (ltake [3;7;5;1;2]) (P.ltake [3;7;5;1;2]) [0;3;7]

  let lallScore =
    let f = fun x -> x > 2 in
    test "lall" 4 1 (lall f) (P.lall f) [[]; [0; 1]; [3; 4; 5]]


  let lmapScore = test "lmap" 5 1 (lmap (fun x -> x * 2))
    (P.lmap (fun x -> x * 2))
    [[3;7;5;1;2];[10;14;15;18;20]]

  let lrevScore = test "lrev" 5 1 lrev P.lrev [[]; [1]; [1; 2; 3; 4]; [2; 4; 6]]

  let lzipScore = test "lzip" 5 1 (curry2 lzip) (curry2 P.lzip)
    [(["Rooney";"Park";"Scholes";"C.Ronaldo"],[8;13;18;7;10;12])]

  let splitScore = test "split" 7 1 split P.split [[1;2;3;4;5;6];[];[1]]

  let cartprodScore = test "cartprod" 7 1
    (cartprod [1;2;3]) (P.cartprod [1;2;3]) [["a";"b";"c";"d"]]

  let score = sumScore + facScore + fibScore + gcdScore + maxScore + depthScore
    + binSearchScore + sumTreeScore + preorderScore + listAddScore + insertScore + insortScore
    + composeScore + curryScore + uncurryScore + multifunScore + ltakeScore
    + lallScore + lmapScore + lrevScore + lzipScore + splitScore + cartprodScore

  let _ = print_string (ST.name ^ " ")
  let _ = print_int score
  let _ = print_newline ()

end;;

module Hfoo = F (Hw1) (struct let name = "Test score" end);;
