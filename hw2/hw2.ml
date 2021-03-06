exception NotImplemented
	    
type 'a tree = Leaf of 'a | Node of 'a tree * 'a * 'a tree
						      
(** Recursive functions **)

let rec lconcat l =
    match l with
    | [] -> []
    | h :: t -> h @ lconcat t ;;

let rec lfoldl f e l =
    match l with
    | [] -> e
    | h :: t -> lfoldl f (f (h, e)) t ;;

(** Tail recursive functions  **)

let fact n =
    let rec fact_aux n acc =
        match n with
        | 0 -> acc
        | _ -> fact_aux (n - 1) (acc * n)
    in fact_aux n 1 ;;

let power x n =
    let rec power_aux x n acc =
        match n with
        | 0 -> acc
        | _ -> power_aux x (n - 1) (acc * x)
    in power_aux x n 1 ;;

let fib n =
    let rec fib_aux n acc1 acc2 =
        match n with
        | 0 -> acc2
        | _ -> fib_aux (n - 1) acc2 (acc1 + acc2)
    in fib_aux n 0 1 ;;

let lfilter p l =
    let rec lfilter_aux p l acc =
        match l with
        | [] -> acc
        | h :: t -> lfilter_aux p t (if p h then acc @ [h] else acc)
    in lfilter_aux p l [] ;;

let ltabulate n f =
    let rec ltabulate_aux n f acc =
        match n with
        | 0 -> acc
        | _ -> ltabulate_aux (n - 1) f (f (n - 1) :: acc)
    in ltabulate_aux n f [] ;;

let rec union s1 s2 =
    match s1 with
    | [] -> s2
    | h :: t -> union t (h :: lfilter (fun x -> x <> h) s2) ;;

let inorder t =
    let rec inorder_aux t acc =
        match t with
        | Leaf l -> l :: acc
        | Node (t1, l, t2) -> inorder_aux t1 (l :: inorder_aux t2 acc)
    in inorder_aux t [] ;;
	   
let postorder t =
    let rec postorder_aux t acc =
        match t with
        | Leaf l -> l :: acc
        | Node (t1, l, t2) -> postorder_aux t1 (postorder_aux t2 (l :: acc))
    in postorder_aux t [] ;;

let preorder t =
    let rec preorder_aux t acc =
        match t with
        | Leaf l -> acc @ [l]
        | Node (t1, l, t2) -> preorder_aux t2 (preorder_aux t1 (acc @ [l]))
    in preorder_aux t [] ;;

(** Sorting in the ascending order **)

let rec quicksort l =
    match l with
    | [] -> []
    | h :: t -> quicksort (lfilter (fun x -> x <= h) t) @ [h] @ quicksort (lfilter (fun x -> x > h) t)

let rec mergesort l =
    match l with
    | [] -> []
    | [h] -> [h]
    | _ ->
        let rec len l acc =
            match l with
            | [] -> acc
            | h :: t -> len t (1 + acc)
        in
        let rec divide n l acc =
            match l with
            | [] -> acc
            | h :: t ->
                let (l1, l2) = acc in
                match n with
                | 0 -> (l1, l2 @ l)
                | _ -> divide (n - 1) t (l1 @ [h], l2)
        in
        let rec merge l1 l2 acc =
            match l1, l2 with
            | [], _ -> acc @ l2
            | _, [] -> acc @ l1
            | h1 :: t1, h2 :: t2 ->
                if h1 < h2
                then merge t1 l2 (acc @ [h1])
                else merge l1 t2 (acc @ [h2])
        in
        let (l1, l2) = divide ((len l 0) / 2) l ([], []) in
        merge (mergesort l1) (mergesort l2) [] ;;

(** Structures **)

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

module Heap : HEAP =
  struct
    exception InvalidLocation 
		
    type loc = unit       (* dummy type, to be chosen by students *) 
    type 'a heap = unit   (* dummy type, to be chosen by students *)

    let empty _ = raise NotImplemented
    let allocate _ _ = raise NotImplemented
    let dereference _ _ = raise NotImplemented
    let update _ _ _ = raise NotImplemented
  end
    
module DictList : DICT with type key = string =
  struct
    type key = string
    type 'a dict = (key * 'a) list
			      
    let empty _ = raise NotImplemented
    let lookup _ _ = raise NotImplemented
    let delete _ _ = raise NotImplemented 
    let insert _ _ = raise NotImplemented
  end
    
module DictFun : DICT with type key = string =
  struct
    type key = string
    type 'a dict = key -> 'a option
			     
    let empty _ = raise NotImplemented
    let lookup _ _ = raise NotImplemented
    let delete _ _ = raise NotImplemented
    let insert _ _ = raise NotImplemented
  end
