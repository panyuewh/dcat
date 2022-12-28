(*===----------------------------------------------------------------------===
 * Code Generation
 *===----------------------------------------------------------------------===*)

open Llvm

exception Error of string

let context = global_context ()
let the_module = create_module context "PY jit"
let builder = builder context
let named_values:(string, llvalue) Hashtbl.t = Hashtbl.create 10
let int_type = i64_type context
let bool_type = i1_type context

(* Create an alloca instruction in the entry block of the function. This
 * is used for mutable variables etc. *)
let create_entry_block_alloca the_function var_name =
  let builder =
    Llvm.builder_at context (Llvm.instr_begin (Llvm.entry_block the_function))
  in
  Llvm.build_alloca int_type var_name builder

(* Create an alloca for each argument and register the argument in the symbol
 * table so that references to it will succeed. *)
let create_argument_allocas the_function proto =
  let args =
    match proto with
    | Ast.Prototype (_, args) -> args
  in
  Array.iteri (fun i ai ->
      let var_name = Array.get args i in
      (* Create an alloca for this variable. *)
      let alloca = create_entry_block_alloca the_function var_name in
      (* Store the initial value into the alloca. *)
      Llvm.build_store ai alloca builder |> ignore ;
      (* Add arguments to variable symbol table. *)
      Hashtbl.add named_values var_name alloca )
      (Llvm.params the_function) 

let codegen_proto_existing = function
  | Ast.Prototype (name, ps) ->
      let ints = Array.make (Array.length ps) int_type in
      let ft = function_type int_type ints in
      let func, existing =
        match lookup_function name the_module with
        | None -> (declare_function name ft the_module, `Existing)
        (* If 'f' conflicted, there was already something named 'name'. If it
         * has a body, don't allow redefinition or reextern. *)
        | Some f ->
            (* If 'f' already has a body, reject this. *)
            if Array.length (Llvm.basic_blocks f) = 0 then ()
            else raise (Error "redefinition of function");

            (* If 'f' took a different number of arguments, reject. *)
            if element_type (type_of f) <> ft then
            if Array.length (Llvm.params f) = Array.length ps then ()
            else  raise (Error "redefinition of function with different # args");
            (f, `Not_existing)
      in
      (* Set names for all arguments. *)
      Array.iteri (fun i a ->
        let n = Array.get ps i in
        set_value_name n a;
        Hashtbl.add named_values n a;
      ) (params func);
      (func, existing)

let rec codegen_expr the_fpm = function
  | Ast.Var name -> (
      try 
        let v = Hashtbl.find named_values name in 
        Llvm.build_load v name builder
      with _ -> raise (Error "unknown variable name"))
  | Ast.Int i -> const_int int_type i
  | Ast.Bool b -> const_int bool_type (Bool.to_int b)
  | Ast.Binop (op, e1, e2) -> 
      let e1_val = codegen_expr the_fpm e1 in
      let e2_val = codegen_expr the_fpm e2 in
      begin
        match op with
        | Add -> build_add e1_val e2_val "addtmp" builder
        | Mult -> build_mul e1_val e2_val "multmp" builder
        | Leq -> build_icmp Icmp.Sle e1_val e2_val "cmptmp" builder
      end
  | Ast.Call (name, args) ->
    print_endline "Ast.Call ***";
      (* Look up the name in the module table. *)
    let callee =
      match lookup_function name the_module with
      | Some callee -> callee
      | None -> raise (Error "unknown function referenced")
    in
    let params = params callee in
    (* If argument mismatch error. *)
    if Array.length params == Array.length args then () else
      raise (Error "incorrect # arguments passed");
    let args = Array.map (codegen_expr the_fpm) args in
    build_call callee args "calltmp" builder
  | Ast.Let (name, e1, e2) -> 
      let e1_val = codegen_expr the_fpm e1 in  
      let _ = Hashtbl.add named_values name e1_val in
      codegen_expr the_fpm e2
  | Ast.Def (proto, e1, e2) ->
      let _ = codegen_func the_fpm (Ast.Function (proto, e1)) in ();
      codegen_expr the_fpm e2
  | Ast.If (e1, e2, e3) -> 
      let e1_val = codegen_expr the_fpm e1 in
      let e2_val = codegen_expr the_fpm e2 in
      let e3_val = codegen_expr the_fpm e3 in
      build_select e1_val e2_val e3_val "seltmp" builder  

and codegen_func the_fpm = function
  | Ast.Function (proto, body) -> (
      Hashtbl.clear named_values;
      let func, existing = codegen_proto_existing proto in
          print_string "after codegen_proto; proto="; 
          print_string (string_of_llvalue func);
          print_string (match existing with
          | `Not_existing -> " not existing\n"
          | `Existing -> " existing\n") ;
      ( try 
          let bb = insertion_block builder in 
          position_at_end bb builder
        with Not_found ->
          (* Create a new basic block to start insertion into. *)
          let bb = append_block context "entry" func in
          position_at_end bb builder
        );
      try
        (* Add all arguments to the symbol table and create their allocas. *)
        create_argument_allocas func proto ;
        let return_val = codegen_expr the_fpm body in
        (* Finish off the function. *)
        let _ : Llvm.llvalue = Llvm.build_ret return_val builder in
        ( match proto with 
        | Prototype (name, _) -> print_string "after build_ret; proto name="; print_endline name ) ;
        (* Validate the generated code, checking for consistency. *)
        ( match Llvm_analysis.verify_function func with
        | true -> 
            print_endline "\nverify_function: true"; ()
        | false ->
            print_endline "\nverify_function: false"; 
            Printf.printf "invalid function generated\n%s\n"
              (Llvm.string_of_llvalue func) ;
            Llvm_analysis.assert_valid_function func ) ;
        ( match proto with 
        | Prototype (name, _) -> print_string "after verify_function; proto name="; print_endline name ) ;
        (* Optimize the function. *)
        let _ : bool = Llvm.PassManager.run_function func the_fpm in
        func 
      with ex ->
        ( match existing with
        | `Not_existing -> Llvm.delete_function func
        | `Existing ->
            Array.iter delete_block (Llvm.basic_blocks func)) ;
        raise ex )


