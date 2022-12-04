(*===----------------------------------------------------------------------===
 * Main driver code.
 *===----------------------------------------------------------------------===*)

open Llvm
open Llvm_executionengine
open Llvm_target
open Llvm_scalar_opts
open Interp
open Main
open Codegen

let main () =

  (* Create the JIT. *)
  let the_execution_engine = ExecutionEngine.create Codegen.the_module in
  let the_fpm = PassManager.create_function Codegen.the_module in

  (* Set up the optimizer pipeline.  Start with registering info about how the
   * target lays out data structures. *)
  DataLayout.add (ExecutionEngine.target_data the_execution_engine) the_fpm;

  (* Do simple "peephole" optimizations and bit-twiddling optzn. *)
  add_instruction_combination the_fpm;

  (* reassociate expressions. *)
  add_reassociation the_fpm;

  (* Eliminate Common SubExpressions. *)
  add_gvn the_fpm;

  (* Simplify the control flow graph (deleting unreachable blocks, etc). *)
  add_cfg_simplification the_fpm;

  ignore (PassManager.initialize the_fpm);  

  let acc = ref [] in
    try
      while true do
        (* Prime the first token. *)
        print_string "ready> "; flush stdout;
        acc := read_line () :: !acc;
      done
    with
        End_of_file -> print_string (String.concat "\n" !acc);

  let s = String.concat " " !acc in
  (* Run the main "interpreter loop" now. *)
  let ast = parse s in
  let _ = codegen_expr ast in
  (* Print out all the generated code. *)
  let dump_named_values n v = print_string n; dump_value v in
  Hashtbl.iter dump_named_values Codegen.named_values;
  dump_module Codegen.the_module
;;

main ()
