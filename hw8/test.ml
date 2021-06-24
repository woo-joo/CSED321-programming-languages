module TestTyping =
struct
let test name = 
  let program = Inout.read_file name in
  let _ = print_endline "Parse OK" in
  let _ = print_endline (Ast_print.program2str program) in
  
  let vprogram = Ast_valid.vprogram program in
  let _ = print_endline "Ast_valid.vprogram OK" in
  let _ = print_endline (Ast_print.program2str vprogram) in
  
  let tprogram = Typing.tprogram vprogram in
  let _ = print_endline "Typing.tprogram OK" in
  let _ = print_endline (Core_print.program2str tprogram) in
  ()
end
