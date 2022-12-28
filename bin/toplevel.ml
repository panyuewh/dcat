(*===----------------------------------------------------------------------===
 * Main driver code.
 *===----------------------------------------------------------------------===*)
open Llvm
open Llvm_executionengine
(* open Llvm_scalar_opts *)
(* open Llvm_passmgr_builder *)
open Interp
open Main
(* open Codegen *)

let loop expr func_count = 
  (* Create the JIT. *)
  print_endline "init...";
  ignore (initialize ());
  let the_execution_engine = create Codegen.the_module in
  let the_fpm = PassManager.create_function Codegen.the_module in
  (* Promote allocas to registers. *)
  Llvm_scalar_opts.add_memory_to_register_promotion the_fpm ;
  (* Do simple "peephole" optimizations and bit-twiddling optzn. *)
  Llvm_scalar_opts.add_instruction_combination the_fpm ;
  (* reassociate expressions. *)
  Llvm_scalar_opts.add_reassociation the_fpm ;
  (* Eliminate Common SubExpressions. *)
  Llvm_scalar_opts.add_gvn the_fpm ;
  (* Simplify the control flow graph (deleting unreachable blocks, etc). *)
  Llvm_scalar_opts.add_cfg_simplification the_fpm ;
  ignore (PassManager.initialize the_fpm);  

  let ast = parse expr in
  add_module Codegen.the_module the_execution_engine ;
  let tmp_name = Printf.sprintf "__toplevel%d" func_count in
  let tmp_proto = Ast.Prototype (tmp_name, (Array.make 0 "")) in
  let tmp_func = Ast.Function (tmp_proto, ast) in
  print_endline "\nbefore call codegen_fun in Toplevel";
  let the_function = Codegen.codegen_func the_fpm tmp_func in
  print_endline "\nbefore dump_value";
  dump_value the_function; 
  (* JIT the function, returning a function pointer. *)
  let fp =
    Llvm_executionengine.get_function_address tmp_name
      (Foreign.funptr Ctypes.(void @-> returning int))
      the_execution_engine
  in
  Printf.printf "\nEvaluated to %i\n" (fp ());
  Llvm_executionengine.remove_module Codegen.the_module the_execution_engine;
  (* Print out all the generated code. *)
  let dump_named_values n v = print_string n; dump_value v in
    Hashtbl.iter dump_named_values Codegen.named_values;
  dump_module Codegen.the_module
;;

let main () =

  let acc = ref [] in
  let anonymous_func_count = ref 0 in
    try
      while true do
        (* Prime the first token. *)
        print_string "ready> "; flush stdout;
        let str = read_line () in
          acc := str :: !acc;
          let n = String.length str in
          (if Char.equal str.[n-1] ';' then
            (* Run the main "interpreter loop" now. *)
            let s = String.concat " " !acc in 
            anonymous_func_count := !anonymous_func_count + 1 ;
            loop s !anonymous_func_count;
            acc := []
          else
            ()
          )
      done
    with
        End_of_file -> print_string (String.concat "\n" !acc);

;;

main ()
