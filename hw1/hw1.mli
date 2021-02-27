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
