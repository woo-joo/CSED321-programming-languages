exception Not_implemented

type 'a tree = Leaf of 'a | Node of 'a tree * 'a * 'a tree

let rec sum n =
    match n with
    | 1 -> 1
    | _ -> n + sum (n - 1) ;;
let rec fac n =
    match n with
    | 1 -> 1
    | _ -> n * fac (n - 1) ;;
let rec fib n =
    match n with
    | 0 -> 1
    | 1 -> 1
    | _ -> fib (n - 1) + fib (n - 2) ;;
let rec gcd m n =
    match n with
    | 0 -> m
    | _ -> gcd n (m mod n) ;;
let rec max l =
    match l with
    | [] -> 0
    | h :: [] -> h
    | h :: t ->
        if h > max t then h
        else max t ;;

let rec sum_tree t =
    match t with
    | Leaf l -> l
    | Node (t1, l, t2) -> sum_tree t1 + l + sum_tree t2 ;;
let rec depth t =
    match t with
    | Leaf l -> 0
    | Node (t1, l, t2) ->
        if depth t1 > depth t2 then depth t1 + 1
        else depth t2 + 1 ;;
let rec bin_search t x =
    match t with
    | Leaf l -> x = l
    | Node (t1, l, t2) when x < l -> bin_search t1 x
    | Node (t1, l, t2) when x > l -> bin_search t2 x
    | _ -> true ;;
let rec preorder t =
    match t with
    | Leaf l -> [l]
    | Node (t1, l, t2) -> l :: preorder t1 @ preorder t2 ;;

let rec list_add l1 l2 =
    match l1, l2 with
    | [], _ -> l2
    | _, [] -> l1
    | h1 :: t1, h2 :: t2 -> (h1 + h2) :: list_add t1 t2 ;;
let rec insert m l =
    match l with
    | h :: t when m > h -> h :: insert m t
    | _ -> m :: l ;;
let rec insort l =
    match l with
    | [] -> []
    | h :: t -> insert h (insort t) ;;

let rec compose f g  = fun x -> g (f x) ;;
let rec curry f x y = f (x, y) ;;
let rec uncurry f (x, y) = f x y ;;
let rec multifun f n =
    match n with
    | 1 -> f
    | _ -> fun x -> (multifun f (n - 1)) (f x) ;;

let rec ltake l n =
    match l, n with
    | [], _ -> []
    | _, _ when n <= 0 -> []
    | h :: t, n -> h :: ltake t (n - 1) ;;
let rec lall f l =
    match l with
    | [] -> true
    | h :: t -> f h && lall f t ;;
let rec lmap f l =
    match l with
    | [] -> []
    | h :: t -> f h :: lmap f t ;;
let rec lrev l =
    match l with
    | [] -> []
    | h :: t -> lrev t @ [h] ;;
let rec lzip l1 l2 =
    match l1, l2 with
    | h1 :: t1, h2 :: t2 -> (h1, h2) :: lzip t1 t2
    | _ -> [] ;;
let rec split l =
    match l with
    | [] -> ([], [])
    | h :: [] -> ([h], [])
    | h1 :: h2 :: t -> let (l1, l2) = split t in (h1 :: l1, h2 :: l2) ;;
let rec cartprod l1 l2 =
    match l1, l2 with
    | [], _ -> []
    | _, [] -> []
    | h1 :: t1, h2 :: t2 -> (h1, h2) :: cartprod [h1] t2 @ cartprod t1 l2 ;;
