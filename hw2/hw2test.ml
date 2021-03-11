module type HW2 =
sig
  exception NotImplemented
  type 'a tree = Leaf of 'a | Node of 'a tree * 'a * 'a tree
  val lconcat : 'a list list -> 'a list
  val lfoldl : ('a * 'b -> 'b) -> 'b -> 'a list -> 'b
  val fact : int -> int
  val power : int -> int -> int
  val fib : int -> int
  val lfilter : ('a -> bool) -> 'a list -> 'a list
  val ltabulate : int -> (int -> 'a) -> 'a list
  val union : 'a list -> 'a list -> 'a list
  val inorder : 'a tree -> 'a list
  val postorder : 'a tree -> 'a list
  val preorder : 'a tree -> 'a list
  val quicksort : 'a list -> 'a list
  val mergesort : 'a list -> 'a list

  module type HEAP =
  sig
    exception InvalidLocation
    type loc
    type 'a heap
    val empty : unit -> 'a heap
    val allocate : 'a heap -> 'a -> 'a heap * loc
    val dereference : 'a heap -> loc -> 'a
    val update : 'a heap -> loc -> 'a -> 'a heap
  end

  module type DICT =
  sig
    type key
    type 'a dict
    val empty : unit -> 'a dict
    val lookup : 'a dict -> key -> 'a option
    val delete : 'a dict -> key -> 'a dict
    val insert : 'a dict -> key * 'a -> 'a dict
  end

  module Heap : HEAP

  module DictList :
  sig
    type key = string
    type 'a dict
    val empty : unit -> 'a dict
    val lookup : 'a dict -> key -> 'a option
    val delete : 'a dict -> key -> 'a dict
    val insert : 'a dict -> key * 'a -> 'a dict
  end

  module DictFun :
  sig
    type key = string
    type 'a dict
    val empty : unit -> 'a dict
    val lookup : 'a dict -> key -> 'a option
    val delete : 'a dict -> key -> 'a dict
    val insert : 'a dict -> key * 'a -> 'a dict
  end
end;;

module S = (Hw2sol : HW2);;

module F (P : HW2) (ST : sig val name : string end) =
struct
  open P

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

  let lconcatScore = test "lconcat" 5 1 (S.lconcat) lconcat [[[]; [1; 2; 3]];[[1; 2; 3]; []];[[1; 2; 3]; [6; 5; 4]; [9]]]

  let lfoldlScore =  test "lfoldl" 5 1 (S.lfoldl (fun (x,y) -> x^y) "c") (lfoldl (fun (x,y) -> x^y) "c")
    [[]; ["b"; "a"]; ["t"; "e"; "y"; "p"] ]

  let factScore = test "fact" 3 1 S.fact fact [0; 1; 5; 10 ]

  let powerScore = test "power" 3 1 (S.power 2) (power 2) [0; 12; 1 ]

  let fibScore = test "fib" 3 1 S.fib fib [0; 1; 5; 10 ]

  let lfilterScore = test "lfilter" 3 1 (S.lfilter (fun x -> x>0)) (lfilter (fun x -> x>0)) [[0]; [-1; 0; 1; 2]]

  let ltabulateScore =
    let n = 4 in
    let f1 = fun x -> x + 1 in
    let f2 = fun x -> x * x in
    test "ltabulate" 3 1 (S.ltabulate n) (ltabulate n) [f1; f2]

  let unionScore =
    let _ = prerr_string "union" in
    let rec insert a l = match l with
        [] -> [a]
      | x :: xs -> if a < x then a :: x :: xs
        else x :: (insert a xs) in
    let rec insort l = match l with
        [] -> []
      | x :: xs -> insert x (insort xs)
    in
    let l = [[]; [1; 2; 3]; [3; 6; 1; 7; 9] ]
    in
    let s =
      if List.for_all (fun r -> r)
        ( List.map (fun x -> try insort ( (union [2; 7; 6]) x ) = insort ( (S.union [2; 7; 6]) x )
          with _ -> false) l )
      then 5 else 0
    in
    let _ = if s = 5 then prerr_string " OK : passed\n" else prerr_string " : failed\n"
    in s

  let inorderScore = test2 "inorder" 8 1 S.inorder inorder  [( S.Node (S.Node (S.Leaf 1, 3, S.Leaf 2), 7, S.Leaf 4),
                                                               Node (Node (Leaf 1, 3, Leaf 2), 7, Leaf 4));
                                                             ( S.Node (S.Leaf 2, 1, S.Leaf 3),
                                                               Node (Leaf 2, 1, Leaf 3));
                                                             ( S.Leaf 0, Leaf 0)]

  let postorderScore = test2 "postorder" 8 1 S.postorder postorder  [( S.Node (S.Node (S.Leaf 1, 3, S.Leaf 2), 7, S.Leaf 4),
                                                                       Node (Node (Leaf 1, 3, Leaf 2), 7, Leaf 4));
                                                                     ( S.Node (S.Leaf 2, 1, S.Leaf 3),
                                                                       Node (Leaf 2, 1, Leaf 3));
                                                                     ( S.Leaf 0, Leaf 0)]

  let preorderScore = test2 "preorder" 8 1 S.preorder preorder   [( S.Node (S.Node (S.Leaf 1, 3, S.Leaf 2), 7, S.Leaf 4),
                                                                    Node (Node (Leaf 1, 3, Leaf 2), 7, Leaf 4));
                                                                  ( S.Node (S.Leaf 2, 1, S.Leaf 3),
                                                                    Node (Leaf 2, 1, Leaf 3));
                                                                  ( S.Leaf 0, Leaf 0)]

  let quicksortScore = test "quicksort" 8 1 S.quicksort quicksort  [[]; [5]; [3; -1]; [3; 1; 10; 9]; [9; 8; -7; 6; -5] ]

  let mergesortScore = test "mergesort" 8 1 S.mergesort mergesort  [[]; [5]; [3; -1]; [3; 1; 10; 9]; [9; 8; -7; 6; -5] ]

  module H = Heap
  module DL = DictList
  module DF = DictFun

  exception Catch

  let heapTest () =
    try
      let _ = prerr_string "Heap" in
      let (h1, l1) = H.allocate (H.empty ()) 5  in
      let (h2, l2) = H.allocate h1 10  in
      let (h3, l3) = H.allocate h2 7  in
      let h4 = H.update h3 l2 3   in

      let t1 =
        try
          let _ = try H.dereference (H.empty ()) l1
            with H.InvalidLocation -> raise Catch
          in 0
        with Catch -> 3
      in
      let t2 = if (H.dereference h4 l1 = 5) && (H.dereference h4 l2 = 3) then 3 else 0 in
      let t3 =
        try
          let _ = try H.update (H.empty ()) l3 15
            with H.InvalidLocation -> raise Catch
          in 0
        with Catch ->
          if (H.dereference h4 l2 = 3) && (H.dereference h4 l1 = 5) && (H.dereference h4 l3 = 7)
          then 4 else 0
      in
      let s = t1 + t2 + t3 in
      let _ = if s = 10 then prerr_string " OK : passed\n" else prerr_string " : failed\n"
      in
      s
    with _ ->  0

  let heapScore =
		match delayed_fun heapTest () 10 with
		| OK s -> s
		| StackOverflow -> prerr_string " Fail - Stack overflow : failed\n"; 0
		| NonTerminated -> prerr_string " Fail - Infinite loop : failed\n"; 0
		| _ -> prerr_string " Fail - Wrong implementation : failed\n"; 0


  let dictListTest () =
    try
      let _ = prerr_string "DictList" in

      let t1 = match (DL.lookup (DL.empty ()) "abc") with
          None -> 3
        | Some _ -> 0 in
      let t2 =
        let d1 = DL.insert (DL.insert (DL.insert (DL.empty ()) ("abc1", 10)) ("abc2", 5)) ("abc3", 15) in
        let s1 = if DL.lookup d1 "abc2" = Some 5 && DL.lookup d1 "abc3" = Some 15 && DL.lookup d1 "abc1" = Some 10
          then 3 else 0 in
        let d2 = DL.delete (DL.insert d1 ("abc1", 1)) "abc3" in
        let s2 = if DL.lookup d2 "abc1" = Some 1 && DL.lookup d2 "abc3" = None
          then 4 else 0
        in s1 + s2
      in
      let s = t1 + t2 in
      let _ = if s = 10 then prerr_string " : passed\n" else prerr_string " : failed\n"
      in s
    with _ -> 0

  let dictListScore =
		match delayed_fun dictListTest () 10 with
		| OK s -> s
		| StackOverflow -> prerr_string " Fail - Stack overflow : failed\n"; 0
		| NonTerminated -> prerr_string " Fail - Infinite loop : failed\n"; 0
		| _ -> prerr_string " Fail - Wrong implementation : failed\n"; 0


  let dictFunTest () =
    try
      let _ = prerr_string "DictFun" in

      let t1 = match (DF.lookup (DF.empty ()) "abc") with
          None -> 3
        | Some _ -> 0 in
      let t2 =
        let d1 = DF.insert (DF.insert (DF.insert (DF.empty ()) ("abc1", 10)) ("abc2", 5)) ("abc3", 15) in
        let s1 = if DF.lookup d1 "abc2" = Some 5 && DF.lookup d1 "abc3" = Some 15 && DF.lookup d1 "abc1" = Some 10
          then 3 else 0 in
        let d2 = DF.delete (DF.insert d1 ("abc1", 1)) "abc3" in
        let s2 = if DF.lookup d2 "abc1" = Some 1 && DF.lookup d2 "abc3" = None
          then 4 else 0
        in s1 + s2
      in
      let s = t1 + t2 in
      let _ = if s = 10 then prerr_string " : passed\n" else prerr_string " : failed\n"
      in s
    with _ -> 0

  let dictFunScore =
		match delayed_fun dictFunTest () 10 with
		| OK s -> s
		| StackOverflow -> prerr_string " Fail - Stack overflow : failed\n"; 0
		| NonTerminated -> prerr_string " Fail - Infinite loop : failed\n"; 0
		| _ -> prerr_string " Fail - Wrong implementation : failed\n"; 0


  let score =
    lconcatScore + lfoldlScore +
      factScore + powerScore + fibScore + lfilterScore + ltabulateScore + unionScore +
      inorderScore + postorderScore + preorderScore +
      quicksortScore + mergesortScore +
      heapScore + dictListScore +dictFunScore

  let _ = flush_all ();
    print_string (ST.name ^ " ");
    print_int score;
    print_newline ()

end;;

module Hfoo = F (Hw2) (struct let name = "Test score" end);;
