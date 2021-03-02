#use "hw1.ml"



exception Error



let sum_test = [(1, 1); (5, 15); (10, 55)]
let fac_test = [(1, 1); (5, 120); (10, 3628800)]
let fib_test = [(0, 1); (1, 1); (4, 5); (10, 89)]
let gcd_test = [((15, 20), 5); ((24, 12), 12); ((10000, 0), 10000)]
let max_test = [([], 0); ([4; 3; 5; 3; 2], 5); ([-10; -100; -20], -10)]

let sum_tree_test = [((Node (Node (Leaf 1, 3, Leaf 2), 7, Leaf 4)), 17)]
let depth_test = [((Node (Node (Leaf 1, 3, Leaf 2), 7, Leaf 4)), 2)]
let bin_search_test = [(((Node (Node (Leaf 1, 2, Leaf 3), 4, Leaf 7)), 2), true);
                      (((Node (Node (Leaf 1, 2, Leaf 3), 4, Leaf 7)), 5), false)]
let preorder_test = [((Node (Node (Leaf 1, 3, Leaf 2), 7, Leaf 4)), [7; 3; 1; 2; 4])]

let list_add_test = [(([], []), []); (([], [1; 2]), [1; 2]); (([4; 5], []), [4; 5]); (([1; 2], [3; 4]), [4; 6]);
                    (([1; 2; 3], [4; 5]), [5; 7; 3]); (([1; 2], [3; 4; 5]), [4; 6; 5])]
let insert_test = [((3, []), [3]); ((3, [1]), [1; 3]); ((3, [1; 2; 4; 5]), [1; 2; 3; 4; 5]); ((3, [2; 6; 8; 10; 15]), [2; 3; 6; 8; 10; 15])]
let insort_test = [([], []); ([1], [1]); ([1; 4; 5; 3], [1; 3; 4; 5]); ([10; 18; 3; -5; 12], [-5; 3; 10; 12; 18])]

let compose_test = [(0, 5); (5, 30); (10, 55)]
let curry_test = [((5, 3), 15)]
let multifun_test = [(2, 256); (3, 6561)]

let ltake_test = [(([3; 7; 5; 1; 2], 0), []); (([3; 7; 5; 1; 2], 3), [3; 7; 5]); (([3; 7; 5; 1; 2], 7), [3; 7; 5; 1; 2])]
let lall_test =
    let f x = x > 2 in
    [((f, []), true); ((f, [0; 1]), false); ((f, [3; 4; 5]), true)]
let lmap_test =
    let f x = x * 2 in
    [((f, [3; 7; 5; 1; 2]), [6; 14; 10; 2; 4]); ((f, [10; 14; 15; 18; 20]), [20; 28; 30; 36; 40])]
let lrev_test = [([], []); ([1], [1]); ([1; 2; 3; 4], [4; 3; 2; 1]); ([2; 4; 6], [6; 4; 2])]
let lzip_test = [((["Rooney"; "Park"; "Scholes"; "C.Ronaldo"], [8; 13; 18; 7; 10; 12]),
                [("Rooney", 8); ("Park", 13); ("Scholes", 18); ("C.Ronaldo", 7)])]
let split_test = [([1; 2; 3; 4; 5; 6], ([1; 3; 5], [2; 4; 6])); ([], ([], [])); ([1], ([1], []))]
let cartprod_test = [(([1; 2; 3], ["a"; "b"; "c"; "d"]),
                    [(1, "a"); (1, "b"); (1, "c"); (1, "d"); (2, "a"); (2, "b"); (2, "c"); (2, "d"); (3, "a"); (3, "b"); (3, "c"); (3, "d")])]



let print_test_score name score pass =
    let res_msg = if pass then "pass" else "fail" in
    let msg = Printf.sprintf "%10s test %s (score : %d/%d)" name res_msg (if pass then score else 0) score in
    let _ = Printf.printf "%50s\n" msg in
    if pass then score else 0

let test1 name score f pairs =
    let check pair = let (input, ans) = pair in try f input = ans with _ -> false in
    print_test_score name score (List.for_all check pairs)

let test2 name score f pairs =
    let check pair = let ((input1, input2), ans) = pair in try f input1 input2 = ans with _ -> false in
    print_test_score name score (List.for_all check pairs)

let print_score name res_score tot_score =
    let _ = print_newline () in
    let msg = Printf.sprintf "[%s] score : %d/%d" name res_score tot_score in
    Printf.printf "%50s\n\n\n" msg


let _ = Printf.printf "--------------------------------------------------\n\n\n"

let sum_score = test1 "sum" 4 sum sum_test
let fac_score = test1 "fac" 4 fac fac_test
let fib_score = test1 "fib" 3 fib fib_test
let gcd_score = test2 "gcd" 4 gcd gcd_test
let max_score = test1 "max" 4 max max_test

let int_tot_score = 19
let int_res_score = sum_score + fac_score + fib_score + gcd_score + max_score
let _ = print_score "functions on integers" int_tot_score int_res_score



let sum_tree_score = test1 "sum_tree" 4 sum_tree sum_tree_test
let depth_score = test1 "depth" 4 depth depth_test
let bin_search_score = test2 "bin_search" 4 bin_search bin_search_test
let preorder_score = test1 "preorder" 4 preorder preorder_test

let bin_tree_tot_score = 16
let bin_tree_res_score = sum_tree_score + depth_score + bin_search_score + preorder_score
let _ = print_score "functions on binary trees" bin_tree_tot_score bin_tree_res_score



let list_add_score = test2 "list_add" 4 list_add list_add_test
let insert_score = test2 "insert" 4 insert insert_test
let insort_score = test1 "insort" 4 insort insort_test

let int_list_tot_score = 12
let int_list_res_score = list_add_score + insert_score + insort_score
let _ = print_score "functions on list of integers" int_list_tot_score int_list_res_score



let compose_score =
    let f x = x + 1 in
    let g x = x * 5 in
    let h = try compose f g with _ -> (fun x -> raise Error) in
    test1 "compose" 4 h compose_test
let curry_score =
    let f (x, y) = x * y in
    let g = try curry f with _ -> (fun x y -> raise Error) in
    test2 "curry" 4 g curry_test
let uncurry_score =
    let f x y = x * y in
    let g = try uncurry f with _ -> (fun x -> raise Error) in
    test1 "uncurry" 4 g curry_test
let multifun_score =
    let f x = x * x in
    let g = try multifun f 3 with _ -> (fun x -> raise Error) in
    test1 "multifun" 4 g multifun_test

let higher_tot_score = 16
let higher_res_score = compose_score + curry_score + uncurry_score + multifun_score
let _ = print_score "higher-order functions" higher_tot_score higher_res_score



let ltake_score = test2 "ltake" 4 ltake ltake_test
let lall_score = test2 "lall" 4 lall lall_test
let lmap_score = test2 "lmap" 5 lmap lmap_test
let lrev_score = test1 "lrev" 5 lrev lrev_test
let lzip_score = test2 "lzip" 5 lzip lzip_test
let split_score = test1 "split" 7 split split_test
let cartprod_score = test2 "cartprod" 7 cartprod cartprod_test

let list_tot_score = 37
let list_res_score = ltake_score + lall_score + lmap_score + lrev_score + lzip_score + split_score + cartprod_score
let _ = print_score "functions on 'a list" list_tot_score list_res_score



let tot_score = 100
let res_score = int_res_score + bin_tree_res_score + int_list_res_score + higher_res_score + list_res_score
let _ = Printf.printf "--------------------------------------------------\n\n"
let _ = print_score "total" tot_score res_score
