(** Generate Horn formulas *)

(**
@author Temesghen Kahsai
*)

open Types
open Exceptions
open Channels
open Printf
open ExtString

(** Specific solver *)
let solver = Globals.my_solver
let toss x = ()  (* toss outputs *)



(** Make horn formulas with rule format*)
let mk_horn_rule filename =
  let use_file = open_in filename in
  let in_ch = use_file in
  let lexbuf = Lexing.from_channel in_ch in
  let outdoc = Buffer.create 1000 in
  let def_hash = Deftable.get_defhash() in
  let no_stateful = ref false in

  try
    let (cp, p, list_p, target_node) = Lustre_parser.main Lustre_lexer.token lexbuf in
    let position = POSITION_VAR (solver#get#position_var1) in
    let _ = if (!Flags.abstr_bool || !Flags.abstr_ite || !Flags.abstr_pre) then
      Lus_flatten.flatten_all_node_defs () in

    let fd = Lus_convert.convert_def_list position target_node in
(*       Lus_convert_print.print_expr_formula fd;  *)
    let maxdepth = Lus_convert.get_max_depth() in
    if maxdepth > Lus_convert.get_max_adepth() then raise Unguarded_PRE;

    let fd' = if !Flags.aggressive_inlining > 0 then Inlining.inlined_formula fd (Coi.property_id_list p)
              else fd
    in
    let _ =  Coi.examine_assignments fd' in
    let vrefs1 = Coi.property_id_list p in
    let vrefs =
      if !Flags.pre_refine_state_vars then
        List.rev_append vrefs1 (Lus_convert.state_vars_list())
      else
        vrefs1
    in
    Coi.calculate_all_dependencies vrefs 0 maxdepth;
    (* Lus_convert_print.print_expr_formula fd'; *)
    begin
      let transState = Horn_convert.formula_string_buffer GENERAL maxdepth fd' in
      Globals.whichState := true;
      let iniState = Horn_convert.formula_string_buffer GENERAL maxdepth fd' in
      let property =  Horn_convert.property_header solver#get#position_var1 position p in
      let assertions = Horn_convert.assumption_string solver#get#position_var1 position in
      let allV, predDecl, initDecl, errorDecl, allVarDecl, predInit, predStep = Horn_convert.allVarRule() in


      let allDecl = List.fold_right(fun x acc -> x^"\n"^acc) allVarDecl ""  in

      let initStateFormula = "(rule (=> (and Init "
                             ^(Buffer.contents iniState)^")\n\t"^predInit^"))" in
      let transStateFormula = "(rule (=> (and "
                              ^(Buffer.contents transState)^" "^predInit^")\n\t"^predStep^"))" in
      let prop = Horn_convert.property_header solver#get#position_var1 position p in
      let property = "(rule (=> (and "^predInit^" (not "^prop^")) Error))" in
      Buffer.add_string outdoc (allV^"\n");
      Buffer.add_string outdoc (predDecl^"\n");
      Buffer.add_string outdoc (initDecl^"\n");
      Buffer.add_string outdoc (errorDecl^"\n");
      Buffer.add_string outdoc (allDecl^"\n");
      Buffer.add_string outdoc ("(rule Init)\n");
      Buffer.add_string outdoc ("; initial state\n");
      Buffer.add_string outdoc (initStateFormula^"\n\n");
      Buffer.add_string outdoc ("; transition relation\n");
      Buffer.add_string outdoc (transStateFormula^"\n\n");
      Buffer.add_string outdoc ("; property(ies)\n");
      Buffer.add_string outdoc property;
      Buffer.add_string outdoc ("\n\n; check safety UNSAT -> safe; SAT -> Unsafe\n");
      Buffer.add_string outdoc ("(query Error)");

      end;
    (* return values *)
      (Buffer.contents outdoc),
      maxdepth,
      def_hash,
      !no_stateful,
      vrefs,
      list_p
  with TypeMismatch(s,x,y) ->
    Printf.printf "\nType Mismatch %s:\n%s\n!=\n%s\n at line %d (col %d)\n" s
      (solver#get#type_string x) (solver#get#type_string y)
      (!Lus_convert.linenum)
      ((Lexing.lexeme_start lexbuf) - !Lus_convert.linepos);
    raise Lus_convert_error
    | Parsing.Parse_error ->
  Printf.printf "\nParse error at line %d (col %d): '%s'\n"
    (!Lus_convert.linenum)
    ((Lexing.lexeme_start lexbuf) - !Lus_convert.linepos)
    (Lexing.lexeme lexbuf);
  raise Lus_convert_error


(** Initialization *)
let main filename =
  let defdoc,maxdepth,def_hash,no_stateful,pvars,prop_list = mk_horn_rule filename in
  if maxdepth > 1 then (
    failwith("Program depth > 1. Work in progress to handle this case."));
  let smt_file_name = filename^".mono.smt2" in
  let oc = open_out smt_file_name in
  fprintf oc "%s\n" defdoc;
  close_out oc;
  print_string ("----------------------- \n");
  print_string ("GENERATED HORN CLAUSE IN [ " ^ smt_file_name ^ " ]");
  print_string ("\n----------------------- \n");
