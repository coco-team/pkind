open Arg;;

let pp_imp_flag = ref false;;
let pp_oth_flag = ref false;;
let modular_flag = ref false;;
let as_string = ref false;;
let filename_count = ref 0;;
let filenames = ref "";;
let dir = ref ".";;

(* Parse the command line arguments and set the appropriate globals *)
Arg.parse [("-imp",Unit(fun x -> (pp_imp_flag := true)),"Recursively expand includes");
           ("-debug",Unit(fun x -> (pp_oth_flag := true)),"An unused option");
           ("-nm",Unit(fun x -> (modular_flag := true)),"Produce a modular Lustre file ");
           ("-s",Unit(fun x -> (as_string := true)), "Accept input Lustre file as string")
] (fun x -> (filenames := x; dir := Filename.dirname x; filename_count := (!filename_count + 1)))
          "lsimplify [OPTIONS] file...";;

(* If a filename has been specified on the command line, read from that.
 * Otherwise, use standard in *)
let parsed =  
  if ((!filename_count) > 0) then
        ( if !as_string then (
          let lexbuf = Lexing.from_string !filenames in 
            Lsimplify_parse.main Lsimplify_lex.token lexbuf
        )else(
        (Lsimplify_transforms.parse_file !filenames))
  )else (
    let lexbuf = Lexing.from_channel stdin in 
       Lsimplify_parse.main Lsimplify_lex.token lexbuf);;
 
(* If no options are specified, output the AST.
 * If "-imp" is specified, recursively expand the include statements, and pretty-print.
 * If "-oth" is specified, do nothing
 *)
match parsed with
  None -> ()
| Some(z) -> 
    let x = (Lsimplify_transforms.expand_imports z !dir) in (* first, recursively expand the imports *)
    if (!pp_imp_flag) then (Lsimplify_pp.pp (x)) else (
       (* Lsimplify_pp.pp z; *)
       if (!pp_oth_flag) then print_string "\nInitial symbol table:\n";
       if (!pp_oth_flag) then Ast.print_symbols ();
       if (!pp_oth_flag) then print_string "\n-----------------------Initial parsed file(s):\n";
       if (!pp_oth_flag) then Lsimplify_pp.pp x;
       if (!pp_oth_flag) then print_string "\n-----------------------After Propagate globals:\n\n";
       let p1 = (Lsimplify_transforms.propagate_globals_and_types x) in
       if (!pp_oth_flag) then Lsimplify_pp.pp p1;
       if (!pp_oth_flag) then print_string "\n-----------------------After Flatten decls:\n\n";
       let p2 = if (not !modular_flag) then p1 else Lsimplify_transforms.flatten_decls p1 in
       if (!pp_oth_flag) then Lsimplify_pp.pp p2;
       let root = ((Lsimplify_transforms.get_root_node p2)) in
       if (!pp_oth_flag) then print_string "\n-----------------------After Expand node calls:\n\n";
       let p3 = if (not !modular_flag) then p2 else Lsimplify_transforms.expand_node_calls p2 root in
       if (!pp_oth_flag) then Lsimplify_pp.pp p3;
       if (!pp_oth_flag) then print_string "\n-----------------------After Expand tuples:\n\n";
       let p4 = Lsimplify_transforms.expand_tuples p3 in
       if (!pp_oth_flag) then Lsimplify_pp.pp p4;
       if (!pp_oth_flag) then print_string "\n-----------------------After array operations:\n\n";
       let p5 = Lsimplify_transforms.do_array_ops p4 in
       if (!pp_oth_flag) then Lsimplify_pp.pp p5;
       if (!pp_oth_flag) then print_string "\n-----------------------After homomorphic extension:\n\n";
       let p6 = Lsimplify_transforms.do_homomorphic_extension p5 in
       if (!pp_oth_flag) then Lsimplify_pp.pp p6;
       if (!pp_oth_flag) then print_string "\n-----------------------After equate tuples:\n\n";
       let p7 = Lsimplify_transforms.equate_tuples p6 in
       if (!pp_oth_flag) then Lsimplify_pp.pp p7;
       if (!pp_oth_flag) then print_string "\n-----------------------After propagate consts:\n\n";
       let (p8) = Lsimplify_transforms.propagate_and_flatten_constants p7 in
       if (not !modular_flag) then Lsimplify_pp.pp p8
     else ( Lsimplify_pp.pp_node_decl (Lsimplify_transforms.get_root_node p8));
       (*if (not !modular_flag) then(
          if (!pp_oth_flag) then print_string "\n-----------------------\n\n";
          
        );*)
)
;;
