exception Not_implemented
  
type 'a tree = Leaf of 'a | Node of 'a tree * 'a * 'a tree
    
(** 2.1 Functions on integers **)
    
let rec sum n = if n = 1 then 1
  else n+sum (n-1)
    
let rec fac n =
  if n = 1 then 1
  else n*fac (n-1)
    
let rec fib n = match n with
    0|1 -> 1
  | _ -> fib (n-1) + fib (n-2)
    
let rec gcd m n = match (m,n) with
    (0,n) -> n 
  | _ -> gcd (n mod m) m
    
let rec max l = 
  match l with
    [] -> 0     
  | [x] -> x    (* in case that l contains only negative numbers - by gok01172 *) 
  | x::xs -> if x > max xs then x else max xs
      
(** 2.2 Functions on binary trees **)
      
let rec sum_tree t = 
  match t with
    Leaf i -> i
  | Node (t1,i,t2) -> (sum_tree t1) + i + (sum_tree t2)
    
let rec depth t = 
  match t with
    Leaf l -> 0
  | Node (t1,v,t2) -> if (depth t1) > (depth t2) then (depth t1) + 1 
    else (depth t2) + 1

let rec bin_search t x = 
  match t with
    Leaf i -> x=i
  | Node (left,i,right) -> if x=i then true 
    else if x<i then bin_search left x
    else bin_search right x
      
let rec preorder t = 
  match t with
    Leaf v -> [v]
  | Node (t1,v,t2) -> [v] @ (preorder t1) @ (preorder t2)
    
(** 2.3 Functions on lists of integers **)
    
let rec list_add l1 l2 = 
  match (l1,l2) with
    ([],l2) -> l2
  | (l1,[]) -> l1
  | (i1::l1',i2::l2') -> (i1+i2) :: (list_add l1' l2')
    
let rec insert a l =
  match l with 
    [] -> [a]
  | x::xs -> if a < x then a :: x :: xs 
    else x :: (insert a xs)
      
let rec insort l = 
  match l with
    [] -> []
  | x::xs -> insert x (insort xs)
    
(** 2.4 Higher-order functions **)

let compose f g = fun x -> g (f x)
  
let curry g x y = g (x,y)
  
let uncurry f (x,y) = f x y
  
let rec multifun f n = 
  if n=1 then f else fun x -> f (multifun f (n-1) x)
    
(** 2.5 Functions on 'a list **)
    
let rec ltake l n = match (l,n) with
    ([],_) -> []
  | (_,0) -> []
  | (head::tail,num) -> head::(ltake tail (num-1))

let rec lall p l = match l with 
    [] -> true
  | x::xs -> p x && lall p xs
    
let rec lmap f l = match l with
    [] -> []
  | x::xs -> f x :: lmap f xs
    
let rec lrev l = 
  let rec lrev' out l = match out with 
      [] -> l
    | hd::tl -> lrev' tl (hd::l)
  in lrev' l [];;

let rec lzip l1 l2 = match (l1,l2) with
    (x::xlist,y::ylist) -> (x,y) :: lzip xlist ylist
  | _ -> []

let rec split l = match l with
    [] -> ([],[])
  | [x] -> ([x],[])
  | x::y::tail -> 
    let (t1,t2) = split tail
    in (x::t1,y::t2)
    
let rec cartprod l1 ys = match l1 with
    [] -> []
  | x::xs -> 
    let xsprod = cartprod xs ys in 
    let rec pairx l2 = match l2 with
        [] -> xsprod
      | y::ytail -> (x,y) :: (pairx ytail)
    in pairx ys
