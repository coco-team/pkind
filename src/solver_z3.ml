(** Z3 Module *)

(**
@author Temesghen Kahsai

*)

open Types
open Flags
open Channels
open Exceptions

let toss x = () (* toss output *)

let contains_line_of doc line =
  let lines = Str.split (Str.regexp "[ \n]+") doc in
    List.exists (fun x -> x = line) lines ;;


class solver_z3 = object (self)
  inherit Solver_base.solver_base

  (*************************************************************)
  (* given a cvcltype, produce a string representation *)
  method type_string x = match x with
  | L_INT -> "Int"
  | L_REAL -> "Real"
  | L_BOOL -> "Bool"
  | L_INT_RANGE(y,z) -> "int"
  | L_TUPLE(y) ->
     let rec list_string xs =
       match xs with
           [] -> ""
         | [t] -> self#type_string t
         | t::ts -> (self#type_string t)^" "^(list_string ts)
     in
     "(tuple "^(list_string y)^")"
  | L_RECORD(y) ->
     let rec list_string xs =
       match xs with
           [] -> ""
         | [f,t] -> f^"::"^(self#type_string t)
         | (f,t)::ts -> f^"::"^(self#type_string t)^" "^(list_string ts)
     in
     "(record "^(list_string y)^")"
  | L_TYPEDEF(y) -> y
  | M_BOOL -> "Bool"
  | M_NAT -> "_nat"
  (* | M_FUNC li -> List.fold_left (fun acc y -> acc^" "^(self#type_string y)) "->" li *)
  | M_FUNC li -> List.fold_left (fun acc y -> " "^(self#type_string y)) " " li
  | _ -> "???"




  (*************************************************************)
  (* string representation of typedef (and any other needed) header *)
  (* needs to at least define a _nat type *)
  (* may need to worry about flag define_mod_div *)
  method header_string =
        "(set-logic HORN)\n"
        ^"(set-option :fixedpoint.print_answer true)"


  (*************************************************************)
  (* command line string to call the solver *)
  method solver_call flags =
      Solvers_path.z3_path^" -in"


  (*************************************************************)
  (* how the solver represents expressions *)
  (* string -> string -> string *)
  method string_of_unary op s1 =
    "("^op^" "^s1^")"

  (* Buffer.t -> Buffer.t -> Buffer.t -> Buffer.t *)
  method buffer_of_unary buf op s1 =
    Buffer.add_string buf "(";
    Buffer.add_string buf op;
    Buffer.add_string buf " ";
    Buffer.add_buffer buf s1;
    Buffer.add_string buf ")"

  method string_of_binary op s1 s2 =
    "("^op^" "^s1^" "^s2^")"

  (* Buffer.t -> Buffer.t -> Buffer.t -> Buffer.t -> Buffer.t *)
  method buffer_of_binary buf op s1 s2 =
    Buffer.add_string buf "(";
    Buffer.add_string buf op;
    Buffer.add_string buf " ";
    Buffer.add_buffer buf s1;
    Buffer.add_string buf " ";
    Buffer.add_buffer buf s2;
    Buffer.add_string buf ")"

  method string_of_nary op l1 =
    (List.fold_left (fun acc x -> acc^" "^x) ("("^op) l1)^")"

  method buffer_of_nary buf op slist =
    Buffer.add_string buf ("("^op);
    List.iter (fun x -> Buffer.add_string buf " ";
                        Buffer.add_buffer buf x) slist;
    Buffer.add_string buf ")"

  method string_of_list_op op l1 =
    self#string_of_nary op l1

  method buffer_of_list_op buf op slist =
    self#buffer_of_nary buf op slist

  (* string -> string -> string -> string *)
  method string_of_ite s1 s2 s3 =
    "(ite "^s1^" "^s2^" "^s3^")"

  (* Buffer.t -> Buffer.t -> Buffer.t -> Buffer.t -> Buffer.t *)
  method buffer_of_ite buf s1 s2 s3 =
    Buffer.add_string buf "(ite ";
    Buffer.add_buffer buf s1;
    Buffer.add_string buf " ";
    Buffer.add_buffer buf s2;
    Buffer.add_string buf " ";
    Buffer.add_buffer buf s3;
    Buffer.add_string buf ")"

  method string_of_tuple slist =
    self#string_of_nary "mk-tuple" slist

  method buffer_of_tuple buf slist =
    self#buffer_of_nary buf "mk-tuple" slist

  method string_of_record slist =
    (List.fold_left (fun acc (x,y) -> acc^" "^x^"::"^y) "(mk-record" slist)^")"

  (* Buffer.t -> (string * Buffer.t) list -> Buffer.t *)
  method buffer_of_record buf slist =
    Buffer.add_string buf "(mk-record";
    List.iter (fun (x,y) -> Buffer.add_string buf " ";
                            Buffer.add_string buf x;
                            Buffer.add_string buf "::";
                            Buffer.add_buffer buf y) slist;
    Buffer.add_string buf ")"

  method string_of_tuple_ref s1 s2 =
    "(select "^s1^" "^s2^")"

  (* Buffer.t -> Buffer.t -> int -> Buffer.t *)
  method buffer_of_tuple_ref buf s1 s2 =
    Buffer.add_string buf "(select ";
    Buffer.add_buffer buf s1;
    Buffer.add_string buf " ";
    Buffer.add_string buf (string_of_int s2);
    Buffer.add_string buf ")"

  method string_of_record_ref s1 s2 =
    "(select "^s1^" "^s2^")"

  (* Buffer.t -> Buffer.t -> string -> Buffer.t *)
  method buffer_of_record_ref buf s1 s2 =
    Buffer.add_string buf "(select ";
    Buffer.add_buffer buf s1;
    Buffer.add_string buf " ";
    Buffer.add_string buf s2;
    Buffer.add_string buf ")"

  method string_of_var_ref var_string pos_string =
    if not !Globals.whichState then (
      if not (String.contains pos_string '1')  then (
        var_string^"_nxt"
      ) else (var_string)
    )else(
      var_string
    )

  method buffer_of_pred buf op slist =
    self#buffer_of_nary buf op slist


  (* string -> string -> string -> string *)

  method string_of_num x =
    if x<0 then
      ("(- 0 "^(string_of_int (-x))^")")
    else
      string_of_int x

  method buffer_of_num buf x =
    if x<0 then
      Buffer.add_string buf ("(- 0 "^(string_of_int (-x))^")")
    else
      Buffer.add_string buf (string_of_int x)


  method zero_string = "false"
  method one_string = "true"
  method true_string = "true"
  method false_string = "false"
  method step_base_string = "_base" (* a valid reserved id *)
  method k_position_string = "_n" (* a valid reserved id *)
  method position_var1 = "_M" (* a valid reserved id *)
  method position_var2 = "_MM" (* a valid reserved id *)
  method state_vars = "STATE_VARS" (* a valid reserved id *)
  method state_vars_r = "STATE_VARS_R" (* a valid reserved id *)
(*  method state_vars_link = "STATE_VARS_LINK" (* a valid reserved id *)*)
  method assertions = "ASSERTIONS" (* a valid reserved id *)
  method uminus_string = "-"
  method minus_string = "-"
  method plus_string = "+"
  method mult_string = "*"
  method div_string = "/"
  method intdiv_string = "div"
  method mod_string = "mod"
  method eq_string = "="
  method lt_string = "<"
  method gt_string = ">"
  method lte_string = "<="
  method gte_string = ">="
  method b_and_string = "and"
  method b_or_string = "or"
  method b_not_string = "not"
  method b_impl_string = "=>"
  method b_iff_string = "="
  method b_xor_string = "xor"
  method f_and_string = "and"
  method f_or_string = "or"
  method f_not_string = "not"
  method f_iff_string = "="
  method f_eq_string = "="
  method f_impl_string = "=>"


  method result_is_unsat out = contains_line_of out "unsat"
  method result_is_sat out = contains_line_of out "sat"
  method result_is_error out = contains_line_of out "error"
  method result_is_unknown out = contains_line_of out "unknown"

  (* generate a freah varname from a string and number *)
  method fresh_varname_string s x = s^"?"^(string_of_int x)

  (* set to true if we only allow binary connectives *)
  method boolean_connectives_strictly_binary = false
  method term_impl_available = true
  method supports_unary_minus = false
  method can_redefine = true

  (*************************************************************)
  (* these should all be "complete commands", including any terminating chars *)
  method safe_push = ""
  method safe_pop = ""

  method checker_setup_string = "(set-verbosity! 2)\n";
  method push_string = "(push)\n"
  method pop_string = "(pop)\n"
  (* string -> lustre_type -> string *)
  method define_var_string name t =
         "(declare-fun "^name^" (Int) "^(self#type_string(t))^")\n"
  method define_const_string name t =
         "(declare-fun "^name^(self#type_string t)^")\n"

  (* string -> lustre_type -> var_decl list -> string -> string *)
  method define_fun_buffer buf name t paramlist formula_buffer =
    match paramlist with
       [] -> Buffer.add_string buf ("(define-fun "^name^"(_M Int)" ^(self#type_string t)
           ^") ");
         Buffer.add_buffer buf formula_buffer;
         Buffer.add_string buf ")\n"
      | _ -> Buffer.add_string buf ("(define-fun "^name^" ((_M Int))" ^(self#type_string(t)));
         Buffer.add_buffer buf formula_buffer;
         Buffer.add_string buf ")\n"

  (* string -> string *)
  method query_buffer buf formula_buffer =
    Buffer.add_string buf "(assert ";
    Buffer.add_buffer buf formula_buffer;
    Buffer.add_string buf ")\n(check-sat)\n"
  (* string -> string *)
  method assert_buffer buf formula_buffer =
    Buffer.add_string buf "(assert ";
    Buffer.add_buffer buf formula_buffer;
    Buffer.add_string buf ")\n"

  method assert_string formula_string =
    "(assert "^formula_string^")\n"

  (* string -> string *)
  method assert_plus_buffer buf formula_buffer =
    Buffer.add_string buf "(assert+ ";
    Buffer.add_buffer buf formula_buffer;
    Buffer.add_string buf ")\n"

  method assert_plus_string formula_string =
    "(assert+ "^formula_string^")\n"

  (* print out the string "__DONE__" *)
  (*method done_string = "(get-info name)\n"*)
  method done_string = "(echo \"__DONE__\")\n"

  (* comment char *)
  method cc = "; "

  method file_extension = "z3"

  method property_header position_string formula_string =
  "\n(define-fun P ((_M Int)) Bool" ^formula_string^")\n\n"

  method aggdef_header outbuf formula_buffer =
    Buffer.add_string outbuf ("(define DEF::(-> _nat bool) (lambda ("
      ^self#position_var1^"::_nat) ");
    Buffer.add_buffer outbuf formula_buffer;
    Buffer.add_string outbuf "))\n\n"


  (*************************************************************)
  (* returns a string of the output from channel in_ch, terminated by __DONE__ *)
  method get_output in_ch =
    let buf = Buffer.create 1 in
    try
      while true do
        let line = input_line in_ch in
        let pos = 8 in
        let long_enough = (String.length line) > pos in
          print_string line;

        (*let reg1 = Str.regexp_string "((\"name\" \"Z3\"))" in*)
        let reg1 = Str.regexp_string "__DONE__" in
        let reg2 = Str.regexp_string_case_fold "error" in
        if long_enough && (Str.string_match reg1 line pos) then (* only if in position *)
          raise End_of_file
        else if (try Str.search_forward reg2 line 0 >= 0 with Not_found -> false)
          then
          raise (SolverError line)
        else
          Buffer.add_string buf (line^"\n")
      done;
      ""
    with End_of_file ->
      Buffer.contents buf


  (*************************************************************)

  (*************************************************************)
  (* get the associated assertion id from something*)
  (* stores this information in the assertion_hash *)
  method get_assert_id out (varid:idtype) (step:int) =
    debug_to_user ("get_assert_id "^(string_of_int varid));
          let reg = Str.regexp "id: \\([0-9]+\\)" in
          try
            toss(Str.search_forward reg out 0);
            let assert_num = int_of_string (Str.matched_group 1 out) in
            Hashtbl.replace assertion_hash assert_num (varid,step)
          with Not_found ->
            if !best_first_path_mode then
              begin
                let reg2 = Str.regexp_string_case_fold "unsat" in
                if (try Str.search_forward reg2 out 0 >=0 with Not_found->false)
                  then
                  raise UNSAT_FOUND (* stop early *)
              end
            else
              begin
                print_to_user "error in checker: cannot find assertion id\n";
                raise Not_found
              end


  method get_simulation_value_hash in_str _ _ =
(*    print_to_user (self#cc^"COUNTERMODEL found\n");*)
    let foundvars = (Hashtbl.create 1:(string,string)Hashtbl.t) in
    let chpos = ref 0 in
      try
        let reg2 = Str.regexp "(= \\([A-Za-z_0-9]+\\) \\([a-z0-9-]+\\))" in
        while !chpos < String.length in_str do
          chpos := Str.search_forward reg2 in_str (!chpos);
          chpos := Str.match_end();
          let word = Str.matched_group 1 in_str in
          let tval = Str.matched_group 2 in_str in
          debug_to_user (word^ " : " ^tval);
          Hashtbl.replace foundvars word tval
        done;
        foundvars
      with Not_found ->
        foundvars


  (*************************************************************)
  (* this returns a list of varids *)
  (* also sets the current_n_value *)
  method get_countermodel in_str _ _ =
(*    print_to_user (self#cc^"COUNTERMODEL found\n");*)
    let foundvars = (Hashtbl.create 1:(int*int,string)Hashtbl.t) in
    let chpos = ref 0 in
      try
        begin
          let n_val_reg = Str.regexp "(= _n \\([0-9-]+\\))" in
          if (try Str.search_forward n_val_reg in_str 0 >=0
              with Not_found->false) then
            begin
              let s = Str.matched_group 1 in_str in
              current_n_value <- Some (int_of_string s)
            end
          else
            current_n_value <- None
        end;
        let reg2 = Str.regexp "(= (\\([A-Za-z_0-9]+\\) \\([0-9-]+\\)) \\([a-z/0-9-]+\\))" in
        while !chpos < String.length in_str do
          chpos := Str.search_forward reg2 in_str (!chpos);
          chpos := Str.match_end();
          let word = Str.matched_group 1 in_str in
          let step = int_of_string (Str.matched_group 2 in_str) in
          let tval = Str.matched_group 3 in_str in
          let varid = Tables.varid_lookup word in
          debug_to_user (word^"("^(string_of_int step)^"): "^tval);
          Hashtbl.replace foundvars (varid,step) tval
        done;
        foundvars
      with Not_found ->
        foundvars


  (*************************************************************)
  (* get the unsat core ids, along with their associated positions *)
  method get_unsat_core out (_:string -> unit) (_:in_channel) =
    debug_to_user "get_unsat_core\n";
      let reg1 = Str.regexp "unsat core ids: \\(.+\\)" in
      let reg2 = Str.regexp "\\([0-9]+\\)" in
      toss(Str.search_forward reg1 out 0);
      let str = Str.matched_group 1 out in
      let pos = ref 0 in
      let numlist = ref [] in
      try
        while !pos < String.length str do
          pos := Str.search_forward reg2 str !pos;
          pos := Str.match_end();
          let a_id = (int_of_string (Str.matched_group 1 str)) in
          let id_step =
            try
              Hashtbl.find assertion_hash a_id
            with Not_found -> raise (Error_found (Str.matched_group 1 str))
          in
          numlist := (id_step)::(!numlist)
        done;
        !numlist
      with Not_found ->
        !numlist
end
