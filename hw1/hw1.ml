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

let rec sum_tree _ = raise Not_implemented
let rec depth _ = raise Not_implemented
let rec bin_search _ _ = raise Not_implemented
let rec preorder _ = raise Not_implemented

let rec list_add _ _ = raise Not_implemented
let rec insert _ _ = raise Not_implemented 
let rec insort _ = raise Not_implemented 

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

