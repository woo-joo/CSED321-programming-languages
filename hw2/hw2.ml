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

let fact _ = raise NotImplemented

let power _ _ = raise NotImplemented

let fib _ = raise NotImplemented

let lfilter _ _ = raise NotImplemented

let ltabulate _ _ = raise NotImplemented

let union _ _ = raise NotImplemented

let inorder t = raise NotImplemented 
	   
let postorder _ = raise NotImplemented

let preorder _ = raise NotImplemented    
		       
(** Sorting in the ascending order **)

let rec quicksort _ = raise NotImplemented

let rec mergesort _ = raise NotImplemented
			
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
