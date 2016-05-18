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

(* structural equality *)


(* il_expression -> string *)
(* if d = 0 then we keep the existing positions *)
let match_formula_structure f1 f2 =
  match f1,f2 with
    F_EQ(VAR_GET(s1,ed1,(NUM vn1),ei1),def1,t1),F_EQ(VAR_GET(s2,ed2,(NUM vn2),ei2),def2,t2) ->
      begin
        let var1 = Lus_convert.resolve_substitution vn1 in
        let var2 = Lus_convert.resolve_substitution vn2 in
let rec match_structure ex1 ex2 =
  begin
    match ex1,ex2 with
      | INT_CONST(e1),INT_CONST(e3) -> match_structure e1 e3
      | REAL_CONST(e1,f1),REAL_CONST(e3,f3) -> f1=f3 && (match_structure e1 e3)
      | PLUS(e1,e2),PLUS(e3,e4) -> (match_structure e1 e3) && (match_structure e2 e4)
      | MINUS(e1,e2),MINUS(e3,e4) -> (match_structure e1 e3) && (match_structure e2 e4)
      | UMINUS(e1),UMINUS(e3) -> (match_structure e1 e3)
      | MULT(e1,e2),MULT(e3,e4) -> (match_structure e1 e3) && (match_structure e2 e4)
      | DIV(e1,e2),DIV(e3,e4) -> (match_structure e1 e3) && (match_structure e2 e4)
      | INTDIV(e1,e2),INTDIV(e3,e4) -> (match_structure e1 e3) && (match_structure e2 e4)
      | MOD(e1,e2),MOD(e3,e4) -> (match_structure e1 e3) && (match_structure e2 e4)
      | REL(r1,e1,e2),REL(r3,e3,e4) -> r1=r3 && (match_structure e1 e3) && (match_structure e2 e4)
      | ITE(e1,e2,e3),ITE(e4,e5,e6) -> (match_structure e1 e4) && (match_structure e2 e5) && (match_structure e3 e6)
      | STREAM_ITE(e1,e2,e3),STREAM_ITE(e4,e5,e6) -> (match_structure e1 e4) && (match_structure e2 e5) && (match_structure e3 e6)
      | B_AND(e1,e2),B_AND(e3,e4) -> (match_structure e1 e3) && (match_structure e2 e4)
      | B_OR(e1,e2),B_OR(e3,e4) -> (match_structure e1 e3) && (match_structure e2 e4)
      | B_IMPL(e1,e2),B_IMPL(e3,e4) -> (match_structure e1 e3) && (match_structure e2 e4)
      | B_NOT(e1),B_NOT(e3) -> (match_structure e1 e3)
      | B_IFF(e1,e2),B_IFF(e3,e4) -> (match_structure e1 e3) && (match_structure e2 e4)
      | VAR_GET(_,d1,(NUM k1),i1),VAR_GET(_,d3,(NUM k3),i3) ->
          let nk1 = Lus_convert.resolve_substitution k1 in
          let nk2 = Lus_convert.resolve_substitution k3 in
          d1=d3 && i1=i3 && ((nk1=var1 && nk2=var2) || nk1=nk2)
      | RECORD_LIT(el1),RECORD_LIT(el3) -> 
         (List.length el1 = List.length el3) &&
         (List.fold_left2 (fun agg (f1,x1) (f3,x3) -> agg && f1=f3 && (match_structure x1 x3)) true (el1) (el3))
      | RECORDREF(e1,field1),RECORDREF(e3,field3) -> field1=field3 && (match_structure e1 e3)
      | TUPLE_LIT(el1),TUPLE_LIT(el3) -> 
         (List.length el1 = List.length el3) &&
         (List.fold_left2 (fun agg x1 x3 -> agg && (match_structure x1 x3)) true el1 el3)
      | TUPLEREF(e1,index1),TUPLEREF(e3,index3) -> index1=index3 && (match_structure e1 e3)
      | x1,x2 -> x1=x2
  end
      in
        if ed1=ed2 && ei1=ei2 && t1=t2 && (match_structure def1 def2) then
          begin
            Some(REL(EQ,VAR_GET(s1,ed1,(NUM var1),ei1),VAR_GET(s2,ed2,(NUM var2),ei2)))
          end
        else
          None
    end
  | _,_ -> None


let scan_formula f =
(* this adds equality constraints as assertions *)
let rec scan_formula' f' flist =
  match f' with
    | F_EQ(c1,c2,_) ->
      begin
        match c1 with
        | VAR_GET(_,_,_,_) ->
            List.iter (fun x -> 
                match match_formula_structure f' x with
                    None -> ()
                  | Some y ->
		      failwith "Debug here" (*Yeting *);
(*		      Lus_convert.add_assertion_term y*)
		      Lus_assertions.add_assertion_term y
            ) flist;
            f'::flist
        | _ -> flist
      end
    | F_NOT(f1) -> scan_formula' f1 flist
    | F_AND(f1,f2) -> scan_formula' f2 (scan_formula' f1 flist)
    | x -> flist
in
(scan_formula' f [];())

