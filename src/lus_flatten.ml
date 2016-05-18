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
open Lus_convert


let new_definitions = ref []

(* we still need to update the node defs *)
let add_definition var rhs node_id =
  let vid,t = match var with
    (S_VAR(_,vid),t) -> vid,t
   | _ -> raise Exceptions.Lus_convert_error
  in
  let new_def = (S_DEF(node_id,var,rhs),L_BOOL) in
  let clocals = 
    try
      Tables.get_node_locals node_id 
    with Not_found -> []
  in
  Tables.add_node_locals node_id ((vid,t)::clocals);
  new_definitions := new_def::(!new_definitions)

(* returns a S_VAR typed_stream *)
let generate_fresh_term t node_id = 
  let id = idcounter#next in
  let name = "__abs_"^(string_of_int node_id)^"_"^(string_of_int id) in
  Tables.update_varinfo id (node_id,name,t,ABSTRACT);
  Tables.varid_name_add name id;
  S_VAR(name,id),t

(* typed_stream -> bool *)
(* return true if a term is "simple" & not worth flattening *)
let rec is_simple_term (s,_) = 
  match s with 
      S_TRUE -> true
    | S_FALSE -> true
    | S_INT(x) -> true
    | S_REAL(i,n,d) -> true
    | S_VAR(sym,id) -> true
    | S_NOT(s1) -> is_simple_term s1
    | S_PRE(s1) -> is_simple_term s1
    | S_FBY(s1,_,s2) -> 
        (is_simple_term s1) && (is_simple_term s2)
    | S_FOLLOWEDBY(s1,s2) ->
        (is_simple_term s1) && (is_simple_term s2)
    | S_EQ(s1,s2) -> 
        (is_simple_term s1) && (is_simple_term s2)
    | S_LT(s1,s2) ->
        (is_simple_term s1) && (is_simple_term s2)
    | S_GT(s1,s2) ->
        (is_simple_term s1) && (is_simple_term s2)
    | S_LTE(s1,s2) ->
        (is_simple_term s1) && (is_simple_term s2)
    | S_GTE(s1,s2) ->
        (is_simple_term s1) && (is_simple_term s2)
    | S_UMINUS(s1) ->
        is_simple_term s1
    | S_COERCE_TO_INT(s1) -> (* not applicable to cvcl? *)
        is_simple_term s1
    | S_COERCE_TO_REAL(s1) -> (* not applicable to cvcl? *)
        is_simple_term s1
    | S_RECORDLIT(s1) ->
          List.fold_left (fun arr (field,e) -> 
            arr && (is_simple_term e)
          ) true s1 
    | S_TUPLELIT(s1) ->
          List.fold_left (fun arr e -> 
            arr && (is_simple_term e)
          ) true s1 
    | S_RECORDREF(s1,fieldname) -> true
    | S_TUPLEREF(s1,index) -> true
    | S_NODE(name,lnum,pnum,params) -> true
    | S_CURRENT(s1) -> 
        is_simple_term s1
    | _ -> false


(* typed_stream -> node_id_t -> bool -> typed_stream *)
(* the bool is to make sure we don't abstract the first layer of a S_DEF *)
(* d is true when we are below the first level of a S_DEF *)
(* d should not matter for the initial call, if it's on a S_DEF *)
let rec abstract_term ((s,t) as interm) node_id d =
  match s with 
    | S_AND(s1,s2) -> 
      let s1' = abstract_term s1 node_id true in
      let s2' = abstract_term s2 node_id true in
      let r = (S_AND(s1',s2'),t) in
      if d && !Flags.abstr_bool then
        begin
          let v = generate_fresh_term t node_id in
          add_definition v r node_id;
          v
        end
      else
        r
    | S_OR(s1,s2) ->
      let s1' = abstract_term s1 node_id true in
      let s2' = abstract_term s2 node_id true in
      let r = (S_OR(s1',s2'),t) in
      if d && !Flags.abstr_bool then
        begin
          let v = generate_fresh_term t node_id in
          add_definition v r node_id;
          v
        end
      else
        r
    | S_IMPL(s1,s2) ->
      let s1' = abstract_term s1 node_id true in
      let s2' = abstract_term s2 node_id true in
      let r = (S_IMPL(s1',s2'),t) in
      if d && !Flags.abstr_bool then
        begin
          let v = generate_fresh_term t node_id in
          add_definition v r node_id;
          v
        end
      else
        r
    | S_XOR(s1,s2) ->
      let s1' = abstract_term s1 node_id true in
      let s2' = abstract_term s2 node_id true in
      let r = (S_XOR(s1',s2'),t) in
      if d && !Flags.abstr_bool then
        begin
          let v = generate_fresh_term t node_id in
          add_definition v r node_id;
          v
        end
      else
        r
    | S_NOT(s1) -> 
      let s1' = abstract_term s1 node_id true in
      let r = (S_NOT(s1'),t) in
      if d && !Flags.abstr_bool then
        begin
          let v = generate_fresh_term t node_id in
          add_definition v r node_id;
          v
        end
      else
        r
    | S_EQ(((_,L_BOOL) as s1),((_,L_BOOL) as s2)) ->
      let s1' = abstract_term s1 node_id true in
      let s2' = abstract_term s2 node_id true in
      let r = (S_EQ(s1',s2'),t) in
      if d && !Flags.abstr_bool then
        begin
          let v = generate_fresh_term t node_id in
          add_definition v r node_id;
          v
        end
      else
        r
    | S_ITE(s1,s2,s3) ->
      let s1' = abstract_term s1 node_id true in
      let s2' = abstract_term s2 node_id true in
      let s3' = abstract_term s3 node_id true in
      let r = (S_ITE(s1',s2',s3'),t) in
      if d && !Flags.abstr_ite then
        begin
          let v = generate_fresh_term t node_id in
          add_definition v r node_id;
          v
        end
      else
        r
    | S_PRE(s1) ->
      let s1' = abstract_term s1 node_id true in
      if d && !Flags.abstr_pre && not (is_simple_term s1) then
        begin
          let v = generate_fresh_term t node_id in
          add_definition v s1' node_id;
          (S_PRE(v),t)
        end
      else
        (S_PRE(s1'),t)
    | S_FBY(s1,i,s2) ->
      let s1' = abstract_term s1 node_id true in
      let s2' = abstract_term s2 node_id true in
      S_FBY(s1',i,s2'),t
    | S_FOLLOWEDBY(s1,s2) ->
      let s1' = abstract_term s1 node_id true in
      let s2' = abstract_term s2 node_id true in
      S_FOLLOWEDBY(s1',s2'),t
(*
    | S_CONDACT(s1,s2,s3,s4) ->
*)
    | S_EQ(s1,s2) ->
      let s1' = abstract_term s1 node_id true in
      let s2' = abstract_term s2 node_id true in
      S_EQ(s1',s2'),t
    | S_LT(s1,s2) ->
      let s1' = abstract_term s1 node_id true in
      let s2' = abstract_term s2 node_id true in
      S_LT(s1',s2'),t
    | S_GT(s1,s2) ->
      let s1' = abstract_term s1 node_id true in
      let s2' = abstract_term s2 node_id true in
      S_GT(s1',s2'),t
    | S_LTE(s1,s2) ->
      let s1' = abstract_term s1 node_id true in
      let s2' = abstract_term s2 node_id true in
      S_LTE(s1',s2'),t
    | S_GTE(s1,s2) ->
      let s1' = abstract_term s1 node_id true in
      let s2' = abstract_term s2 node_id true in
      S_GTE(s1',s2'),t
    | S_PLUS(s1,s2) ->
      let s1' = abstract_term s1 node_id true in
      let s2' = abstract_term s2 node_id true in
      S_PLUS(s1',s2'),t
    | S_MINUS(s1,s2) ->
      let s1' = abstract_term s1 node_id true in
      let s2' = abstract_term s2 node_id true in
      S_MINUS(s1',s2'),t
    | S_MULT(s1,s2) ->
      let s1' = abstract_term s1 node_id true in
      let s2' = abstract_term s2 node_id true in
      S_MULT(s1',s2'),t
    | S_DIV(s1,s2) ->
      let s1' = abstract_term s1 node_id true in
      let s2' = abstract_term s2 node_id true in
      S_DIV(s1',s2'),t
    | S_INTDIV(s1,s2) ->
      let s1' = abstract_term s1 node_id true in
      let s2' = abstract_term s2 node_id true in
      S_INTDIV(s1',s2'),t
    | S_MOD(s1,s2) ->
      let s1' = abstract_term s1 node_id true in
      let s2' = abstract_term s2 node_id true in
      S_MOD(s1',s2'),t
    | S_UMINUS(s1) ->
      let s1' = abstract_term s1 node_id true in
      S_UMINUS(s1'),t
    | S_COERCE_TO_INT(s1) -> (* not applicable to cvcl? *)
      let s1' = abstract_term s1 node_id true in
      S_COERCE_TO_INT(s1'),t
    | S_COERCE_TO_REAL(s1) -> (* not applicable to cvcl? *)
      let s1' = abstract_term s1 node_id true in
      S_COERCE_TO_REAL(s1'),t
(*    | S_CURRENT(S_WHEN(s1,s2),t1) -> (* different clock *)
*)
    | S_CURRENT(s1) -> (* if no clock change, does nothing *)
      let s1' = abstract_term s1 node_id true in
      S_CURRENT(s1'),t
    | S_DEF(nid,s1,s2) -> (* this includes a "dummy" ONE expr *)
      let s2' = abstract_term s2 node_id false in
      S_DEF(nid,s1,s2'),t
    | S_NODE(name,lnum,pnum,params) -> (* flatten the node call *)
      let params' = 
        List.fold_left (fun acc x -> (abstract_term x node_id true)::acc) [] params 
      in
      S_NODE(name,lnum,pnum,params'),t
(*    | S_ATMOSTONE(),_ -> *)
    | x -> interm


let flatten_all_node_defs () =
  Hashtbl.iter (fun nid name ->
    let cdefs = Tables.get_node_defs nid in
    let revised_defs = List.fold_left (fun acc def -> 
        let this_def = abstract_term def nid false in
        this_def::acc
      ) [] cdefs
    in
    let all_defs = List.rev_append revised_defs !new_definitions in
    Tables.add_node_defs nid all_defs;
    new_definitions := []
  ) (Tables.get_nodename_table ())

