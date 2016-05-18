(*
This file is part of the Kind verifier

* Copyright (c) 2007-2012 by the Board of Trustees of the University of Iowa,
* here after designated as the Copyright Holder.
* All rights reserved.
*
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions are met:
*     * Redistributions of source code must retain the above copyright
*       notice, this list of conditions and the following disclaimer.
*     * Redistributions in binary form must reproduce the above copyright
*       notice, this list of conditions and the following disclaimer in the
*       documentation and/or other materials provided with the distribution.
*     * Neither the name of the University of Iowa, nor the
*       names of its contributors may be used to endorse or promote products
*       derived from this software without specific prior written permission.
*
* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER ''AS IS'' AND ANY
* EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
* WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
* DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY
* DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
* (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
* LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
* ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

(** CVC4 Module *)

(**
@author Morgan Deters
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


(* solver interface for cvc4 *)
class solver_cvc4 = object (self)
  inherit Solver_base.solver_base

  (*************************************************************)
  (* given a cvcltype, produce a string representation *)
  method type_string x = match x with
  | L_INT -> "INT"
  | L_REAL -> "REAL"
  | L_BOOL -> "BOOLEAN"
  | L_INT_RANGE(y,z) -> "["^(string_of_int y)^".."^(string_of_int z)^"]"
  | L_TUPLE(y) ->
     let rec list_string xs =
       match xs with
           [] -> ""
         | [t] -> self#type_string t
         | t::ts -> (self#type_string t)^" "^(list_string ts)
     in
     "["^(list_string y)^"]"
  | L_RECORD(y) ->
     let rec list_string xs =
       match xs with
           [] -> ""
         | [f,t] -> f^"::"^(self#type_string t)
         | (f,t)::ts -> f^"::"^(self#type_string t)^" "^(list_string ts)
     in
     "[#"^(list_string y)^"#]"
  | L_TYPEDEF(y) -> y
  | M_BOOL -> "BOOLEAN"
  | M_NAT -> "_nat"
  | M_FUNC ([x;y]) -> (self#type_string x) ^ " -> " ^ (self#type_string y)
      (* List.fold_left (fun acc y -> acc^" -> "^(self#type_string y)) (self#type_string x) li*) 
  
  | M_FUNC ([x;y;z]) -> "( " ^ (self#type_string x) ^ " , " ^ (self#type_string y) 
                        ^ ") -> " ^ (self#type_string z)
  | _ -> "???"

  
  (*let f l = 
    List.map 
      (fun el -> 
        let rev_el = List.rev el in 
        let last, args =  List.hd rev_el, List.rev (List.tl rev_el) in 
      args, last) 
    l


  let f2 l = 
    List.map 
      (fun el -> 
        List.fold_right 
          (fun e (args, res) ->
            match res, args with 
              | [], [] -> [], [e]
              | [], _ -> assert false
              | _ -> e::args, res
          ) 
          el 
          ([], [])) 
    l*)





  (*************************************************************)
  (* string representation of typedef (and any other needed) header *)
  (* needs to at least define a _nat type *)
  (* may need to worry about flag define_mod_div *)
  method header_string =
    (if !Flags.define_mod_div then
       "\nOPTION \"logic\" \"UFDTLIRA\";\n"
       ^"%from Clark Barrett, may be incomplete:\n"
       ^"div: (INT, INT) -> INT;\n"
       ^"ASSERT (FORALL (x, y, z: INT) : (NOT y = 0) => \n"
       ^"  (div(x, y) = z <=>  y * z <= x AND y * (z + 1) > x));\n"
       ^"mod: (INT, INT) -> INT = LAMBDA (x: INT, y: INT): x - div(x, y) * y;\n\n"
     else
       "\nOPTION \"logic\" \"QF_UFDTLIRA\";\n")
    ^(if !Flags.do_negative_index then
        "_base_t : TYPE = [_..0];\n"
        ^"_base : _base_t;\n"
        (* FIXME in CVC4 - predicate subtyping enumerators crash *)
        (*^"_nat : TYPE = SUBTYPE(LAMBDA(n : INT): n >= _base);\n"*)
        ^"_nat : TYPE = INT;\n"
      else
        "_nat : TYPE = [0.._];\n"
        ^"_base : _nat = 0;\n\n")
      ^"_n : _nat;\n"
      (* FIXME in CVC4 - shouldn't have to do this, but using encoding without predicate subtyping *)
      ^"ASSERT _n >= _base;\n" (**)
      ^"_check_quant : BOOLEAN;\n"



  (*************************************************************)
  (* command line string to call the solver *)
  method solver_call flags =
    Solvers_path.cvc4_path^" -im "^flags
   


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
    "("^s1^" "^op^" "^s2^")"

  (* Buffer.t -> Buffer.t -> Buffer.t -> Buffer.t -> Buffer.t *)
  method buffer_of_binary buf op s1 s2 =
    (if !Flags.define_mod_div && op = self#intdiv_string then
       begin
         Buffer.add_string buf "div(";
         Buffer.add_buffer buf s1;
         Buffer.add_string buf ",";
         Buffer.add_buffer buf s2;
         Buffer.add_string buf ")"
       end
     else (if !Flags.define_mod_div && op = self#mod_string then
             begin
               Buffer.add_string buf "mod(";
               Buffer.add_buffer buf s1;
               Buffer.add_string buf ",";
               Buffer.add_buffer buf s2;
               Buffer.add_string buf ")"
             end
           else
             begin
               Buffer.add_string buf "(";
               Buffer.add_buffer buf s1;
               Buffer.add_string buf " ";
               Buffer.add_string buf op;
               Buffer.add_string buf " ";
               Buffer.add_buffer buf s2;
               Buffer.add_string buf ")"
             end))

  method string_of_nary op l1 =
    (List.fold_left (fun acc x -> acc^" "^x) ("("^op^"(") l1)^"))"

  method buffer_of_nary buf op slist =
    Buffer.add_string buf ("("^op^"(");
    List.iter (fun x -> Buffer.add_string buf " ";
                        Buffer.add_buffer buf x) slist;
    Buffer.add_string buf "))"

  method string_of_list_op op l1 =
    self#string_of_nary op l1

  method buffer_of_list_op buf op slist =
    self#buffer_of_nary buf op slist


  (* string -> string -> string -> string *)
  method string_of_ite s1 s2 s3 =
    "(IF "^s1^" THEN "^s2^" ELSE "^s3^" ENDIF)"

  (* Buffer.t -> Buffer.t -> Buffer.t -> Buffer.t -> Buffer.t *)
  method buffer_of_ite buf s1 s2 s3 =
    Buffer.add_string buf "(IF ";
    Buffer.add_buffer buf s1;
    Buffer.add_string buf " THEN ";
    Buffer.add_buffer buf s2;
    Buffer.add_string buf " ELSE ";
    Buffer.add_buffer buf s3;
    Buffer.add_string buf " ENDIF)"

  method string_of_tuple slist =
    (self#string_of_nary "(" slist)^")"

  method buffer_of_tuple buf slist =
    (self#buffer_of_nary buf "(" slist);
    Buffer.add_string buf ")"

  method string_of_record slist =
    (List.fold_left (fun acc (x,y) -> acc^" "^x^" := "^y) "(#" slist)^"#)"

  (* Buffer.t -> (string * Buffer.t) list -> Buffer.t *)
  method buffer_of_record buf slist =
    Buffer.add_string buf "(#";
    List.iter (fun (x,y) -> Buffer.add_string buf " ";
                            Buffer.add_string buf x;
                            Buffer.add_string buf " := ";
                            Buffer.add_buffer buf y) slist;
    Buffer.add_string buf "#)"

  method string_of_tuple_ref s1 s2 =
    "("^s1^"."^s2^")"

  (* Buffer.t -> Buffer.t -> int -> Buffer.t *)
  method buffer_of_tuple_ref buf s1 s2 =
    Buffer.add_string buf "(";
    Buffer.add_buffer buf s1;
    Buffer.add_string buf ".";
    Buffer.add_string buf (string_of_int s2);
    Buffer.add_string buf ")"

  method string_of_record_ref s1 s2 =
    "("^s1^"."^s2^")"

  (* Buffer.t -> Buffer.t -> string -> Buffer.t *)
  method buffer_of_record_ref buf s1 s2 =
    Buffer.add_string buf "(";
    Buffer.add_buffer buf s1;
    Buffer.add_string buf ".";
    Buffer.add_string buf s2;
    Buffer.add_string buf ")"

  method string_of_var_ref var_string pos_string =
    "("^var_string^"("^pos_string^"))"

  method buffer_of_pred buf op slist =
    self#buffer_of_nary buf op slist


  (* string -> string -> string -> string *)

  method string_of_num x =
    if x<0 then
      (self#uminus_string^(string_of_int (-x)))
    else
      string_of_int x

  method buffer_of_num buf x =
    if x<0 then
      Buffer.add_string buf (self#uminus_string^(string_of_int (-x)))
    else
      Buffer.add_string buf (string_of_int x)


  method zero_string = "FALSE"
  method one_string = "TRUE"
  method true_string = "TRUE"
  method false_string = "FALSE"
  method step_base_string = "_base" (* a valid reserved id *)
  method k_position_string = "_n" (* a valid reserved id *)
  method position_var1 = "_M" (* a valid reserved id *)
  method position_var2 = "_MM" (* a valid reserved id *)
  method state_vars = "STATE_VARS" (* a valid reserved id *)
  method state_vars_r = "STATE_VARS_R" (* a valid reserved id *)
(*  method state_vars_link = "STATE_VARS_LINK" (* a valid reserved id *)*)
  method assertions = "_ASSERTIONS" (* a valid reserved id *)
  method assertions_inv = "_ASSERTIONS-INV" (* a valid reserved id *)
  method uminus_string = "-"
  method minus_string = "-"
  method plus_string = "+"
  method mult_string = "*"
  method div_string = "/"
  method intdiv_string = "DIV"
  method mod_string = "MOD"
  method eq_string = "="
  method neq_string = "/="
  method lt_string = "<"
  method gt_string = ">"
  method lte_string = "<="
  method gte_string = ">="
  method b_and_string = "AND"
  method b_or_string = "OR"
  method b_not_string = "NOT"
  method b_impl_string = "=>"
  method b_iff_string = "<=>"
  method b_xor_string = "XOR"

  method f_and_string = "AND"
  method f_or_string = "OR"
  method f_not_string = "NOT"
  method f_iff_string = "<=>"
  method f_eq_string = "="
  method f_impl_string = "=>"

(*
  method result_is_unsat out =
    let reg1 = Str.regexp_string_case_fold "unsat" in
    (try Str.search_forward reg1 out 0 >=0 with Not_found->false)
  method result_is_sat out =
    let reg1 = Str.regexp_string_case_fold "sat" in
    (try Str.search_forward reg1 out 0 >=0 with Not_found->false)
  method result_is_error out =
    let reg1 = Str.regexp_string_case_fold "error" in
    (try Str.search_forward reg1 out 0 >=0 with Not_found->false)
  method result_is_unknown out =
    let reg1 = Str.regexp_string_case_fold "unknown" in
    (try Str.search_forward reg1 out 0 >=0 with Not_found->false)

*)

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
  method safe_push = "PUSH; %safe\n"
  method safe_pop = "POP; %safe\n"

  method checker_setup_string = self#cc^"(set-verbosity! 2)\n";
  method push_string = "PUSH;\n"
  method pop_string = "POP;\n"

  (* string -> lustre_type -> string *)
  method define_var_string name t =
         name^" : "^(self#type_string(M_FUNC [M_NAT;t]))^";\n"

  method define_const_string name t =
         name^" : "^(self#type_string t)^";\n"

  (* string -> lustre_type -> var_decl list -> string -> string *)
  method define_fun_buffer buf name t paramlist formula_buffer =
    match paramlist with
       [] -> Buffer.add_string buf (name^" : "^(self#type_string t)^" = ");
         Buffer.add_buffer buf formula_buffer;
         Buffer.add_string buf ";\n"
     | _ -> Buffer.add_string buf (name^" : "^(self#type_string t)
           ^" = LAMBDA("
           ^(List.fold_left
              (fun acc (n,ty) -> 
                match n with
                "," -> acc^" "^n^" "
                | _  -> acc^" "^n^" : "^(self#type_string ty)
              )
              "" paramlist)
           ^"): ");
         Buffer.add_buffer buf formula_buffer;
         Buffer.add_string buf ";\n"

  (* string -> string *)
  method query_buffer buf formula_buffer =
    Buffer.add_string buf "ASSERT ";
    Buffer.add_buffer buf formula_buffer;
    Buffer.add_string buf ";\nCHECKSAT;\n"
  (* string -> string *)
  method assert_buffer buf formula_buffer =
    Buffer.add_string buf "ASSERT ";
    Buffer.add_buffer buf formula_buffer;
    Buffer.add_string buf ";\n"

  method assert_string formula_string =
    "ASSERT "^formula_string^";\n"

  (* string -> string *)
  method assert_plus_buffer buf formula_buffer =
    Buffer.add_string buf "ASSERT "; (* was an ASSERT+ to get unsat cores *)
    Buffer.add_buffer buf formula_buffer;
    Buffer.add_string buf ";\n"

  method assert_plus_string formula_string =
    "(ASSERT "^formula_string^";\n" (* was an ASSERT+ to get unsat cores *)

  (* print out the string "__DONE__" *)
  method done_string = "ECHO \"__DONE__\";\n"

  (* comment char *)
  method cc = "% "

  method file_extension = "cvc4"

  method property_header position_string formula_string =
  "\nP : _nat -> BOOLEAN = LAMBDA("
  ^position_string^" : _nat): "^formula_string^";\n\n"

  method property_header_new position_string formula_string =
  "\nP : _nat -> BOOLEAN = LAMBDA("
  ^position_string^" : _nat): "^formula_string^" = true;\n\n"

  method aggdef_header outbuf formula_buffer =
    Buffer.add_string outbuf ("DEF : _nat -> BOOLEAN = LAMBDA("
      ^self#position_var1^" : _nat): ");
    Buffer.add_buffer outbuf formula_buffer;
    Buffer.add_string outbuf ";\n\n"


  (*************************************************************)
  (* returns a string of the output from channel in_ch, terminated by __DONE__ *)
  method get_output in_ch =
    debug_to_user "get_output";
    let buf = Buffer.create 1 in
    let pos =
      match !Flags.set_my_solver with
        | CVC3 -> 5
        | CVC4 -> 0
	| Z3 -> 8
        | YICES -> 8
        | YICES_WRAPPER -> 0
    in
    try
      while true do
        let line = input_line in_ch in
        let long_enough = (String.length line) > pos in
        debug_to_user (line);

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
    debug_to_user "get_output_done";
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
  (* this version does not utilize in_str *) 
  method get_countermodel = self#get_cex BASE_PROC


  (*************************************************************)
  (* this returns a list of varids *)
  (* also sets the current_n_value *)
  (* this version does not utilize in_str *) 
  method get_cex _ _ print_to_solver from_solver_ch =
      let foundvars = (Hashtbl.create 1:(int*int,string)Hashtbl.t) in
      print_to_solver ("COUNTERMODEL;\n"^self#done_string);
      let in_str = self#get_output from_solver_ch in
      print_to_user (!commentchar^"COUNTERMODEL found\n======\n"^in_str^"\n======\n");
      let chpos = ref 0 in
      try
        let n =
        begin
          let n_val_reg = Str.regexp "_n : INT = \\([0-9-]+\\);" in
          if (try Str.search_forward n_val_reg in_str 0 >=0 
              with Not_found->false) then
            begin
              let s = Str.matched_group 1 in_str in
              current_n_value <- Some (int_of_string s);
              int_of_string s
            end
          else
            begin
              current_n_value <- None;
              0
            end
        end in
        let base =
        begin
          let base_val_reg = Str.regexp "_base : \[_\.\.0\] = \\([0-9-]+\\);" in
          Str.search_forward base_val_reg in_str 0;
          int_of_string (Str.matched_group 1 in_str)
        end in
        while !chpos < String.length in_str do
          let s2 = "\\([a-zA-Z0-9_]+\\) : (INT) -> [A-Z]+ = .*;" in
          let reg2 = Str.regexp s2 in
          chpos := Str.search_forward reg2 in_str (!chpos);
          chpos := Str.match_end();
          let word = Str.matched_group 1 in_str in
          for i = base to n do
            print_to_solver ("GET_VALUE "^word^"("^(string_of_int i)^");\n"^self#done_string);
            let in_str2 = self#get_output from_solver_ch in
            let s3 = "(("^word^"([0-9()-]+), \(.*\)))" in
            let reg3 = Str.regexp s3 in
            Str.search_forward reg3 in_str2 0;
            Str.match_end();
            let step = i in
            let tval = Str.matched_group 1 in_str2 in
            let varid = Tables.varid_lookup word in
            print_to_user (!commentchar^word^"("^(string_of_int step)^") = "^tval^";\n");
            Hashtbl.replace foundvars (varid,step) tval
          done
        done;
        foundvars
      with Not_found ->
        foundvars

  (*************************************************************)
  (* get the unsat core ids, along with their associated positions *)
  method get_unsat_core out (_:string -> unit) (_:in_channel) =
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

  (*************************************************************)
  (*************************************************************)

end

