(*===----------------------------------------------------------------------===
 * Main driver code.
 *===----------------------------------------------------------------------===*)

open Llvm
open Interp
open Main
open Codegen

let main () =

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
  let ast = interp_big s in
  let _ = codegen_expr ast in
  (* Print out all the generated code. *)
  let dump_named_values n v = print_string n; dump_value v in
  Hashtbl.iter dump_named_values Codegen.named_values;
  dump_module Codegen.the_module
;;

main ()
