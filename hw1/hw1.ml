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
    match m, n with
    | 0, _ -> n
    | _, 0 -> m
    | _ ->
        if m > n then gcd (m mod n) n
        else gcd m (n mod m) ;;
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
    | Node (t1, l, t2) ->
        if x < l then bin_search t1 x
        else if x > l then bin_search t2 x
        else true ;;
let rec preorder t =
    match t with
    | Leaf l -> [l]
    | Node (t1, l, t2) -> l :: (preorder t1 @ preorder t2) ;;

let rec list_add l1 l2 =
    match l1, l2 with
    | [], _ -> l2
    | _, [] -> l1
    | h1 :: t1, h2 :: t2 -> (h1 + h2) :: list_add t1 t2 ;;
let rec insert m l =
    match l with
    | [] -> [m]
    | h :: t ->
        if m < h then m :: h :: t
        else h :: insert m t ;;
let rec insort l =
    match l with
    | [] -> []
    | h :: t -> insert h (insort t) ;;

let rec compose _ _  = raise Not_implemented 
let rec curry _ _ _ = raise Not_implemented 
let rec uncurry _ _ = raise Not_implemented
let rec multifun _ _ = raise Not_implemented

let rec ltake _ _ = raise Not_implemented
let rec lall _ _ = raise Not_implemented
let rec lmap _ _ = raise Not_implemented
let rec lrev _ = raise Not_implemented
let rec lzip _ _ = raise Not_implemented
let rec split _ = raise Not_implemented
let rec cartprod _ _ = raise Not_implemented

