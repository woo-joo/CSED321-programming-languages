exception NotImplemented
            
type 'a tree = Leaf of 'a | Node of 'a tree * 'a * 'a tree
                                                      
(** Recursive functions **)

let rec lconcat l =  match l with
    [] -> []
  | x :: xs -> x @ lconcat xs

let rec lfoldl f e l  = match l with
    [] -> e 
  | x :: xs -> lfoldl f (f (x, e)) xs
                         
(** Tail recursive functions  **)

let fact n = 
  let rec fact_aux n acc = match n with 
      0 -> acc
    | _ -> fact_aux (n - 1) acc * n
  in fact_aux n 1 

let power x n = 
  let rec power_aux x n acc = match n with
      0 -> acc
    | _ -> power_aux x (n - 1) acc * x
  in power_aux x n 1

let fib n = 
  let rec fib_aux n pre curr = match n with 
      0 -> pre
    | 1 -> curr
    | _ -> fib_aux (n - 1) curr (curr + pre)
  in fib_aux n 1 1

let lfilter p l = 
  let rec lfilter_aux p l acc = match l with 
      [] -> acc
    | x::xs -> if p x then lfilter_aux p xs (acc @ [x]) 
               else lfilter_aux p xs acc
  in lfilter_aux p l []

let ltabulate n f = 
  let rec ltabulate_aux n f acc = match n with
      0 -> (f 0) :: acc
    | _ -> ltabulate_aux (n - 1) f ((f n) :: acc)
  in ltabulate_aux (n - 1) f []
                   
let rec union l1 l2 =
  match l1 with
    [] -> l2
  | x :: xs ->  let rec exist x l = match l with 
                    [] -> false
                  | y::ys -> (x = y) || exist x ys 
                in 
                if exist x l2 then union xs l2
                else union xs (x :: l2)

let inorder t =
  let rec inorder' t post = match t with
      Leaf i -> i :: post
    | Node (l,i,r) -> inorder' l (i :: (inorder' r post))
  in
  inorder' t []

let postorder t = 
  let rec postorder' t post = match t with 
      Leaf i -> i::post
    | Node (l,i,r) -> postorder' l (postorder' r (i::post))
  in postorder' t []      

let preorder t = 
  let rec preorder' t post = match t with 
      Leaf i -> post@[i]
    | Node (l,i,r) -> preorder' r (preorder' l (post@[i]))
  in preorder' t []

(** Sorting in the ascending order **)

let rec quicksort t = match t with 
    [] -> []
  | x::xs -> let (l,r) = List.partition (fun i -> i<x) xs
             in (quicksort l) @ [x] @ (quicksort r)

let rec mergesort l = 
  let rec merge (l1, l2) = match ( l1, l2) with 
      ([], _) -> l2
    | (_, []) -> l1
    | (x :: xs, y :: ys) -> if x <= y 
                              then x :: merge (xs, y :: ys) 
                              else y :: merge (x :: xs, ys) in
  let rec sort l = match l with
      [] -> []
    | [x] -> [x]
    | _ ->  let k = ((List.length l) / 2) in
            let rec take (s, i) = if i = 0 then []
                                  else match s with 
                                         a :: b -> a :: take (b, i-1)
                                       | _ -> s in
            let rec drop (s, i) = if i = 0 then s 
                                  else match s with 
                                         a::b -> drop (b, i-1)
                                       | _ -> s 
            in
            merge (mergesort (take (l, k)), mergesort (drop (l, k)))
  in
  sort l

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
                
    type loc = int       (* dummy type, to be chosen by students *) 
    type 'a heap = (loc * 'a) list   (* dummy type, to be chosen by students *)

    let empty () = []
    let allocate h v = 
          let l = List.length h + 1
          in
          ( (l, v) :: h, l )
    let dereference h l = try let ( _, v) = List.find ( fun (loc,v) -> loc = l ) h 
                              in v
                          with
                            Not_found -> raise InvalidLocation
    let update h l v = try let _ = List.find ( fun (loc,v) -> loc = l ) h 
                           in List.map ( fun (loc,value) -> if loc = l then (loc, v) else (loc, value) ) h 
                       with
                         Not_found -> raise InvalidLocation
  end
    
module DictList : DICT with type key = string =
  struct
    type key = string
    type 'a dict = (key * 'a) list
                              
    let empty () = []
    let rec lookup d k = match d with
        [] -> None
      | ((k', v) :: d') -> if k' = k then Some v else lookup d' k
    let delete d k = List.filter ( fun (k', _) -> k <> k' ) d 
    let insert d (k, v) = (k, v) :: (delete d k)
  end
    
module DictFun : DICT with type key = string =
  struct
    type key = string
    type 'a dict = key -> 'a option
                             
    let empty () = fun _ -> None 
    let lookup d = d
    let delete d k = fun k' -> if k' = k then None else d k'
    let insert d (k, v) = fun k' -> if k' = k then Some v else d k'
  end
