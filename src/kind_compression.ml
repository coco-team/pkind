(*
This file is part of the Kind verifier

* Copyright (c) 2007-2009 by the Board of Trustees of the University of Iowa, 
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

open Types
open Exceptions
open Channels
open Globals

let solver = Globals.my_solver

(********************************************************************)
  (* this prints out jstart..k1 compression constraints *)
  (* note we cannot have "loops" smaller than the depth of memory+1 *)
  let general_compression_constraint startdepth add print_to_dest jstart k1 base_pos  =
  let maxdepth = startdepth - 1 in
  let nstart = solver#get#step_base_string in
                for j=jstart to k1 do
                  (* because a loop must be larger than the memory, we can
                     skip a comparison (or more) when maxdepth >= 2 *)
(* note i was 0 *)
                  for i=1 to j-1(*startdepth*) do
                      print_to_dest (Lus_convert_yc.simple_command_string
                        (ASSERT(
                           F_PRED(solver#get#state_vars,
                            [PLUS(POSITION_VAR(base_pos),NUM(add*j));
                             (PLUS(POSITION_VAR(base_pos),NUM(add*i)))])
                           )))
                    done;
                done;
                (* also distinct from base *)
                if !Flags.initial_compression && k1 > startdepth then
                  begin 
                    let jstart2 =
                      if jstart <= 1 then 1
                      else
                      if jstart <= startdepth then startdepth
                      else jstart - 1
                    in
                    let safe_base_pos =
                      if maxdepth > 1 then
                        PLUS(POSITION_VAR(base_pos),NUM(maxdepth-1))
                      else
                        POSITION_VAR(base_pos)
                    in
                    for i=jstart2 to k1-1 do
                      print_to_dest (Lus_convert_yc.simple_command_string
                        (ASSERT(
                           F_PRED(solver#get#state_vars,
                            [PLUS(safe_base_pos,NUM(add*i));
                             POSITION_VAR(nstart)])
                           )))
                    done
                  end

(********************************************************************)
  (* this prints out jstart..k1 compression constraints *)
  (* note we cannot have "loops" smaller than the depth of memory+1 *)
  let abstracted_compression_constraint startdepth add print_to_dest jstart k1 base_pos =
  let maxdepth = startdepth - 1 in
  let nstart = solver#get#step_base_string in
                  for j=jstart to k1 do
(* note i was 0 *)
                    for i=1 to j-1(*startdepth*) do
                      print_to_dest (Lus_convert_yc.simple_command_string
                        (ASSERT(
                           F_PRED(Lus_convert_yc.get_state_vars_r_version(),
                            [PLUS(POSITION_VAR(base_pos),NUM(add*j));
                             (PLUS(POSITION_VAR(base_pos),NUM(add*i)))])
                           )))
                      done;
                  done;
                  (* also distinct from base *)
                  if !Flags.initial_compression && k1 > startdepth then
                    begin
                      let jstart2 =
                        if jstart <= 1 then 1
                        else
                        if jstart <= startdepth then startdepth
                        else jstart - 1
                      in
                      let safe_base_pos =
                        if maxdepth > 1 then
                          PLUS(POSITION_VAR(base_pos),NUM(maxdepth-1))
                        else
                          POSITION_VAR(base_pos)
                      in
                      for i=jstart2 to k1-1 do
                      print_to_dest (Lus_convert_yc.simple_command_string
                        (ASSERT(
                           F_PRED(Lus_convert_yc.get_state_vars_r_version(),
                            [PLUS(safe_base_pos,NUM(add*i));
                             POSITION_VAR(nstart)])
                           )))
                      done
                    end
 
(********************************************************************)
let termination_check def_hash startdepth k_step_size firststep add newly_refined_vars k from_solver_ch from_checker_ch = 
  let k1 = k-1 in
  let nstart = solver#get#step_base_string in

      begin  (* do base path compression constraints *)
        print_to_solver (solver#get#cc^"Performing termination check\n");
          if not Flags.static_path_compression.(base_abstr) then
            begin (* dynamic compression *)
              try
                let s = solver#get#push_string^
                        (Lus_convert_yc.yc_state_vars_string_refined base_abstr)^"\n"
                in
                print_to_solver s;

                abstracted_compression_constraint startdepth add 
                  print_to_solver (k-startdepth) (k-startdepth) "0" ;

                if !Flags.loopfree_mode then
                  abstracted_compression_constraint startdepth add 
                    print_to_solver 0 (k1-startdepth) "0";


                (* TERMINATION check *)
                  print_to_solver solver#get#safe_push;
                  print_to_solver 
                      (Lus_convert_yc.simple_command_string
                        (QUERY(
                           F_EQ(POSITION_VAR(nstart),NUM(add*k),L_INT)
                           )));
                  print_to_solver solver#get#safe_pop;

                print_to_solver solver#get#done_string;
                let out0 = solver#get#get_output from_solver_ch in
                if (solver#get#result_is_unsat out0) then
                  begin
                    print_to_user (solver#get#cc^"Reachable space fully explored.\n");
                    if !Flags.check_compression then
                      begin
                        print_to_user (solver#get#cc^"Checking against static state definition.\n");
                        print_to_solver solver#get#pop_string;
                        if !Flags.interleave_termination_checks then
                          begin
(* may need to perform some refinements to catch this *)
                            (* force refinement? *)
                            let foundvars = (Hashtbl.create 1:(int*int,string)Hashtbl.t) in
                            let ids_steps = List.map (fun x -> (x,k-1)) (Lus_convert.state_vars_list()) in
                            print_to_user (solver#get#cc^"Forcing refinement in term check.\n");
                            let xs = Kind_refine.refine_abstraction from_checker_ch def_hash startdepth add true BASE foundvars k ids_steps in
                            (* note these new vars *)
                            (* they will be permanently added next time *)
                             newly_refined_vars := 
                               List.rev_append (!newly_refined_vars) xs
                          end;
                        raise AllStatefulVarsRefined
                      end;
                    Kind_refine.print_stats def_hash;
                    raise Reachable_space_explored
                        end;
                    print_to_solver solver#get#pop_string

              with NoStatefulVars -> (* do nothing *)
                  print_to_user (solver#get#cc^"Termination: No stateful variables refined\n")
              | AllStatefulVarsRefined -> (* switch to static compression *)
                  print_to_user (solver#get#cc^"All stateful variables refined\n");
                  Flags.static_path_compression.(base_abstr) <- true;
                  if !Flags.loopfree_mode then
                    begin
                      general_compression_constraint startdepth add print_to_solver 0 (k-startdepth) "0" 
                    end;
              print_to_solver solver#get#push_string;
(* temporarily assert in base the vars ust refined (if any) *)
                            List.iter (fun y ->
                              Kind_support.print_initialization_single def_hash 
                                startdepth add y;
                              for i=startdepth to k-1 do
                                Kind_support.persistent_step_single_assert def_hash startdepth add BASE i y
                              done
                            ) !newly_refined_vars;
                  (* TERMINATION check *)
                  print_to_solver solver#get#safe_push;
                  print_to_solver 
                      (Lus_convert_yc.simple_command_string
                        (QUERY(
                           F_EQ(POSITION_VAR(nstart),NUM(add*k),L_INT)
                           )));
                  print_to_solver solver#get#safe_pop;

                  print_to_solver solver#get#done_string;
                  let out0 = solver#get#get_output from_solver_ch in
                  if (solver#get#result_is_unsat out0) then
                    begin
                     print_to_user (solver#get#cc^"Reachable space fully explored.\n");
                      Kind_refine.print_stats def_hash;
                      raise Reachable_space_explored
                    end;
                  print_to_solver solver#get#pop_string
            end (* dynamic compression *)
          else 
            begin
              let startpoint = 
                if !Flags.interleave_termination_checks then
                  begin
                    if firststep then startdepth
                    else k - startdepth - k_step_size + 1
                  end
                else
                  k-startdepth
              in
              if !Flags.loopfree_mode then (* there is static compression *)
                begin 
                  general_compression_constraint startdepth add print_to_solver 
                    startpoint (k-startdepth) "0" ;
                  print_to_solver solver#get#push_string
                end
              else (* there is static compression *)
                begin
                  print_to_solver solver#get#push_string;
                  general_compression_constraint startdepth add print_to_solver 
                    0 (k-startdepth) "0" 
                end;

                (* TERMINATION check *)
                print_to_solver solver#get#safe_push;
                print_to_solver
                      (Lus_convert_yc.simple_command_string
                        (QUERY(
                           F_EQ(POSITION_VAR(nstart),NUM(add*k),L_INT)
                           )));

                print_to_solver solver#get#done_string;
                print_to_solver solver#get#safe_pop;
                let out0 = solver#get#get_output from_solver_ch in
                if (solver#get#result_is_unsat out0) then
                  begin
                    print_to_user (solver#get#cc^"Reachable space fully explored.\n");
                    Kind_refine.print_stats def_hash;
                    raise Reachable_space_explored
                        end;
                      print_to_solver solver#get#pop_string
            end
      end (* termination check *)

