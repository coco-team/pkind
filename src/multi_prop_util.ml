(*
This file is part of the Kind verifier

* Copyright (c) 2007-2010 by the Board of Trustees of the University of Iowa, 
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

open Util
open Expr_util
open Sub_exprs
open Types
open Exceptions
open Channels
open Flags
open Globals
open ExtString
open ExtList


(** Utilities for scanning a counterexample in multiproperty PKIND *)

(** 
@author Temesghen Kahsai

*)


(**
Various string utilities.
**)

let rec is_my_letter l c =
	if l = [] then
		false
	else
		if (List.hd l) == c then
			true
		else
			is_my_letter (List.tl l) c

(**
	Find the index of one of these characters, or -1 if it doesn't exist.

	@param str the string to search
	@param l the list of characters
	@param i the index at which to begin the search
 *)
let rec str_index_of_one str l i =
	if i < String.length str then
		if is_my_letter l (String.get str i) then
			i
		else
			str_index_of_one str l (i + 1)
	else
		-1

(* Private recursive function for splitting a stream in a buffer.
 skipf is the character skip function for when a match is found
 rv is the list that will contain the return value
 str is the string being split
 l is the list of things on which to split
 i is the index at which to split
 limit is the maximum number of entries in the return array
 *)
let rec pvt_rec_split_chars skipf rv str l i limit =
	if (List.length rv < (limit-1)) && (i < String.length str) then (
		let pos = str_index_of_one str l i in
		if pos != -1 then (
			pvt_rec_split_chars skipf
				(rv @ [ String.sub str i (pos - i)])
				str l
				(skipf str l pos)
				limit
		) else (
			rv @ [ String.sub str i ((String.length str) - i) ]
		)
	) else (
		if i < String.length str then (
			rv @ [ String.sub str i ((String.length str) - i) ]
		) else (
			rv
		)
	)

(* Private recursive function for splitting a stream in a buffer *)
let rec pvt_rec_split skipf rv str c i limit =
	if (List.length rv < (limit - 1)) && (i < String.length str) then (
		if String.contains_from str i c then
			let o = String.index_from str i c in
			pvt_rec_split skipf
				(rv @ [ String.sub str i (o - i)])
				str c
				(skipf str c o)
				limit;
		else
			rv @ [ String.sub str i ((String.length str) - i) ]
	) else (
		if i < String.length str then
			rv @ [ String.sub str i ((String.length str) - i) ]
		else
			rv
	)

(**
 Split a string into a list of Strings.
 @param s the original string
 @param c the character on which to split
 @param limit the maximum number of splits to do
 @return an array of strings of the split elements
*)
let split s c limit =
	let rec pvt_skip_char s c i =
		if (i >= String.length s ) then (
			String.length s
		) else (
			if ((String.get s i) == c) then (
				pvt_skip_char s c (i+1)
			) else (
				i
			)
		)
		in
	pvt_rec_split pvt_skip_char [] s c 0 limit

(**
 Split a string into a list of Strings.  The difference between this function
 and split is that this function will return empty strings for successive
 instance of split characters.

 @param s the original string
 @param c the character on which to split
 @param limit the maximum number of splits to do
 @return an array of strings of the split elements
*)
let split_all s c limit =
	pvt_rec_split (fun s c i ->
					if i >= String.length s then
						String.length s
					else
						succ i)
			[] s c 0 limit

(* skip characters in a string from the given list of characters *)
let rec pvt_skip_chars s l i =
	if (i >= String.length s ) then
		String.length s
	else
		if is_my_letter l (String.get s i) then
			pvt_skip_chars s l (i+1)
		else
			i

(**
 Split a string into a list of Strings.

 @param s the original string
 @param l the list of characters on which to split
 @param limit the maximum number of splits to do
 @return an array of strings
*)
let split_chars s l limit =
	pvt_rec_split_chars pvt_skip_chars [] s l 0 limit

(**
 Split a string into a list of Strings.  The difference between this function
 and split_chars is that this function will return empty strings for successive
 instance of split characters.

 @param s the original string
 @param l the list of characters on which to split
 @param limit the maximum number of splits to do
 @return an array of strings
*)
let split_chars_all s l limit =
	pvt_rec_split_chars (fun s c i ->
							if i >= String.length s then
								String.length s
							else
								succ i)
			[] s l 0 limit

(**
 Locate a string in another string.

 @param haystack the string in which we are searching
 @param needle the thing for which we are looking
 @param offset where to begin the search (0 for the beginning)
 @return the offset of the first match, or -1 if there is no match
 *)
let rec strstr haystack needle offset =
	if ((String.length needle) + offset) > (String.length haystack) then
		-1
	else
		if (String.sub haystack offset (String.length needle)) = needle then
			offset
		else
			if (String.contains_from haystack (offset+1) (String.get needle 0))
			then
				strstr haystack needle
					(String.index_from haystack (offset+1)
						(String.get needle 0))
			else
				-1

(*
 Test:
 strstr "abcdef" "def" 0;;
 strstr "abcdef" "efg" 0;;
 strstr "abcdef" "abc" 0;;
 strstr "abcdef" "xyz" 0;;
 *)

(**
 Does this string end with that string?

 @param src the source string
 @param pat the comparison string
 *)
let ends_with src pat =
	if ((String.length src) >= (String.length pat)) then
		(pat =
			String.sub src
				((String.length src) - (String.length pat)) (String.length pat))
	else
		false

(*
 Test:
 ends_with "test." ".";;
 ends_with "." "test.";;
 ends_with "test." "yourmom";;
*)

(**
 Does this string begin with that string?

 @param src the source string to test
 @param pat the string to check at the beginning
 *)
let begins_with src pat =
	if ((String.length src) >= (String.length pat)) then
		(pat = String.sub src 0 (String.length pat))
	else
		false

(*
 Test:
 begins_with "test." ".";;
 begins_with "." "test.";;
 begins_with "yourmom" "your";;
*)

(**
  Create a string from the list of characters provided.

  @param l the list of characters that will become the string.
  *)
let string_of_chars l =
	let rv = Buffer.create 64 in
	List.iter (fun c -> Buffer.add_char rv c) l;
	Buffer.contents rv

(**
 Convert a character to a string.

 @param c the character
 *)
let string_of_char =
	String.make 1

(**
 Remove characters from the front of the given string.
 *)
let remove_front chars s =
	let pos = pvt_skip_chars s chars 0 in
	String.sub s pos ((String.length s) - pos)

(* The whitespace characters *)
let pvt_whitespace = [' '; Char.chr 10; Char.chr 13; Char.chr 9]

(**
 Remove whitespace from the front of a string.
 *)
let strip_front =
	remove_front pvt_whitespace

(**
 Remove characters from the end of a string.
 *)
let remove_end chars s =
	let rec pvt_skip_chars_rev s i =
		if (i < 1) then
			0
		else
			if is_my_letter chars (String.get s i) then
			  pvt_skip_chars_rev s (i-1) 
			else
				i
		in
	let pos = pvt_skip_chars_rev s ((String.length s) - 1) in
	if pos > 0 then
		String.sub s 0 (pos + 1)
	else
		""

(**
 Remove whitespace from the end of a string.
 *)
let strip_end =
	remove_end pvt_whitespace

(**
 Remove whitespace from both ends of a string.
 *)
let strip s =
	strip_front (strip_end s)




(*******************************************************)
(* Utility functions used for the multi property verification*)

(** Make a property name*)
let mk_name_property s =
let l = remove_front ['('] s  in 
 remove_end [')';'_';'M'] l

(** Check if prop is true *)
let is_true str =
  let up_value = Char.uppercase (String.get str 0)  in
    if 'T' = up_value then true
    else if 'F' = up_value then false
    else failwith ("unknown boolean value: " ^ str)  

(** Check if prop is false*)
let is_false str = not (is_true str)

(** Create a named list *)
let create_new_named_list prop_list =
 List.map (fun x -> ("P"^x)) prop_list

(** Get invalid property *)
let get_invalid_prop_list prop_list hash_tbl =
  List.filter (fun x -> is_false (Hashtbl.find hash_tbl x) ) prop_list

(** Get valid property*)
let get_valid_prop_list prop_list hash_tbl =
  List.filter (fun x -> is_true (Hashtbl.find hash_tbl x) ) prop_list

(** Get the real name of a property*)    
let get_real_prop_name name =  
  let middle = remove_front ['P'] name in
    Tables.internal_name_to_original_name middle


(** Create a list of property names, having a list of internal names. (Used for XML outputs)*)
let rec mk_prop_names list_props = 
  match list_props with 
      [] -> ""
    | [a] -> get_real_prop_name(a)
    | h::l -> get_real_prop_name(h) ^ " " ^ mk_prop_names l


(** Create a string of property names. (Used for XML outputs)*)
let rec mk_string list_props = 
  match list_props with 
      [] -> ""
    | [a] -> a
    | h::l -> h ^ " " ^ mk_prop_names l


(** Print summary of all properties *)
let print_summary valid_prop invalid_prop =
print_to_user_final("\n\n    -------------------------------------\n");
print_to_user_final("    --^^--        SUMMARY          --^^--\n");
print_to_user_final("    -------------------------------------\n\n");
  
print_to_user_final ("VALID PROPERTIES : ");
 if (List.length valid_prop == 0) then
   (
   print_to_user_final("< NO VALID PROPERTIES >\n")
   )
 else
   (  
     List.iter (fun x -> print_to_user_final (x^" ")) valid_prop;
   print_to_user_final ("\n\n")
   );
 
 print_to_user_final ("INVALID PROPERTIES : ");
 if (List.length invalid_prop == 0) then
   (
   print_to_user_final("< NO INVALID PROPERTIES >\n")
   )
 else
   (  
     List.iter (fun x -> print_to_user_final (x^" ")) invalid_prop;
   print_to_user_final ("\n\n")
   )
     
     


(* A function to filter SAT and UNSAT props*)
let filter_props prop_ids cex k =
  let sat_prop = ref [] in
  let sat_prop_k = ref [(0,0)] in 
  let unsat_prop = ref [] in
  let _ =  debug_proc BASE_PROC None ("MULTI: Filtering up to the depth k = " ^ string_of_int(k) ^ " ") in
  let zero_sat_prop =  List.filter (fun id -> is_false 
				   (Hashtbl.find cex (id,0))) prop_ids in
  
  let zero_unsat_prop =  List.filter (fun id -> is_true
				   (Hashtbl.find cex (id,0))) prop_ids in
    if k > 0 then (
     for i=1 to k do
       let tmp_sat =  List.filter (fun id -> is_false 
				     (Hashtbl.find cex (id,-i))) prop_ids in
       let _ = sat_prop := List.append tmp_sat !sat_prop in

       let tmp_sat_prop_k = List.map (fun x -> (x,i)) !sat_prop in

       let _ = sat_prop_k := List.append tmp_sat_prop_k !sat_prop_k in
	  
       let tmp_unsat = List.filter (fun id -> is_true
				      (Hashtbl.find cex (id,-i))) prop_ids in
       unsat_prop := List.append tmp_unsat !unsat_prop;

   done;
   );
    let zero_sat_prop_k = List.map (fun x -> (x,0) ) zero_sat_prop in
    let _ = sat_prop_k := List.append zero_sat_prop_k !sat_prop_k in
    let _ = sat_prop_k := List.remove_assoc 0 !sat_prop_k in
    let _ = sat_prop := List.append zero_sat_prop !sat_prop in
    let _ = unsat_prop := List.append zero_unsat_prop !unsat_prop in	
      debug_proc BASE_PROC None "MULTI: Done filtering up to the depth";
      sat_prop := List.unique !sat_prop;
      unsat_prop := List.unique !unsat_prop;
      !sat_prop, !unsat_prop
	

