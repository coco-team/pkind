open Lsimplify_syntax;;
open Ast;;

let code_debug = false;;

(**********************************************************)
(** STEP 1  -  EXPAND INCLUDES                          ***)
(**********************************************************)

(* Strips the quotes off of a string literal
 *
 * s : string           - the string to strip
 *
 * returns s2 : string  - the contents of the string literal
 *)
let strip_stringlit s = String.sub s 1 ((String.length s)-2);;

(* Runs a given file through the parser.
 *
 * s : string         - the file to parse
 *
 * returns t : program   - the output AST
 *)
let parse_file s = let lexbuf =
                   Lexing.from_channel (open_in s) in
                   Lsimplify_util.file := s;
                   Lsimplify_util.line := 1;
                   Lsimplify_parse.main Lsimplify_lex.token lexbuf;;


(* Folds a list of programs and a given program into one program.
 *
 * l : program list      - a list of programs
 * x : program           - a program
 *
 * returns y : program   - a program containing the contents of all
 *                           programs in l and x
 *)
let rec join_programs l x = match l with
| [] -> x
| a::more -> let s = (join_programs more x) in
   (match (a,s) with
   | (Program(p1,_,LusFile(_,(_,tl1,cl1,fl1,nl1))),
      Program(p2,_,LusFile(_,(_,tl2,cl2,fl2,nl2))))  ->
         Program(p1,IncludeList(p1,(p1,[])),
         LusFile(p2,(p2,List.append tl1 tl2,
                        List.append cl1 cl2,
                        List.append fl1 fl2,
                        List.append nl1 nl2)))
   )
;;

(* Recursively expand the import statements.
 *
 * x : program          - the file containing import statements
 * name : string          - current working directory
 *
 * returns y : program  - a program with imports expanded
 *)
let rec expand_imports x name = match x with
| Program(_,IncludeList(_,(_,il1)),LusFile(_,_)) ->
      join_programs (expand_imports_list il1 name) x

(* Recursively expand a list of import statements into a program.
 *
 * l : string list        - a list of files to import
 * name : string          - current working directory
 *
 * returns x : program  - the expansion of all imported files
 *)
and expand_imports_list l name = match l with
| [] -> []
| Include(_,s)::more -> let x =
                let fname = (name^"/"^(strip_stringlit s)) in (parse_file fname)
             in (match x with
                | None -> (expand_imports_list more name)
                | Some(y) -> (expand_imports y name)::(expand_imports_list more name));;

(******************************************************************)

let rec get_node (pr:program) (id:int) = match pr with
| Program(_,_,LusFile(_,(_,_,_,_,nl))) ->
      let res = List.fold_left (fun a n ->
         (match (a,n) with
         | (None,NodeDecl(_,i,_,_,_,_)) ->
               if id=i then Some(n) else None
         | _ -> a)
      ) None nl in
      match res with
      | None -> failwith("TODO unknown node: "^(Ast.get_sym_name (id)))
      | Some(x) -> x

and get_root_node (pr:program) = get_node pr !(Ast.root_node)

(**********************************************************)

type var_rep_table = (int * exp) list
and  type_rep_table  = (int * ltype) list
;;


let print_var_rep_table vt =
   List.iter (fun (i,e) ->
      print_int i;
      print_string " -> ";
      Lsimplify_pp.pp_exp e;
      print_string "\n";
   ) vt
;;

(**********************************************************)
(** STEP 2  -  PROPAGATE GLOBAL CONSTANTS AND TYPES     ***)
(**********************************************************)

let get_global_const_reps (p:program) : (var_rep_table * const_decl list) = match p with
| Program(_,_,LusFile(_,(_,_,l,_,_))) ->
   List.fold_left (fun a x ->
      (match x with
      | ConstDecl(p1,(p2,ol)) ->
         List.fold_left (fun (b,cl) y ->
            (match y with
            | EqOneConstDecl(_,i,e) ->
               (*print_int i;
               print_string " -> ";
               Lsimplify_pp.pp_exp e;
               print_string "\n";*)
               ((try
                  let _ = List.assoc i b in
                  failwith ("get_global_const_reps: redeclaration!!")
               with Not_found ->
                  b @ [(i,e)]),
               cl
               )
            (* TODO - check for redeclarations in this list case *)
            | o -> (b,cl@[ConstDecl(p1,(p2,[o]))]))
         ) a ol
      )
   ) ([],[]) l
;;

let get_type_reps (p:program) : (type_rep_table * type_decl list) = match p with
| Program(_,_,LusFile(_,(_,l,_,_,_))) ->
   List.fold_left (fun a x ->
      (match x with
      | TypeDecl(p1,(p2,ol)) ->
         List.fold_left (fun (b,tl) y ->
            (match y with
            | EqOneTypeDecl(_,i,t) ->
               (*print_int i;
               print_string " ----> ";
               Lsimplify_pp.pp_ltype t;
               print_string "\n";*)
               ((try
                  let _ = List.assoc i b in
                  failwith ("get_type_reps: redeclaration!!")
               with Not_found ->
                  b @ [(i,t)]),
               tl
               )
            (* TODO - check for redeclarations in this list case *)
            | o -> (b,tl@[TypeDecl(p1,(p2,[o]))]))
         ) a ol
      )
   ) ([],[]) l
;;

let
rec replace_func_decl (vt:var_rep_table) (tt:type_rep_table) (f:func_decl) : (func_decl*bool) =
   match f with
   | FuncDecl(p,i,vl1,vl2) ->
      let (n1,f1) = replace_var_decl_list vt tt vl1 in
      let (n2,f2) = replace_var_decl_list vt tt vl2 in
      (FuncDecl(p,i,n1,n2),f1||f2)

and replace_var_decl (vt:var_rep_table) (tt:type_rep_table) (v:var_decl) : (var_decl * bool) =
   match v with
   | VarDecl(p,idl,lt) ->
       let (lt2,f) = replace_ltype vt tt lt in
         (VarDecl(p,idl,lt2),f)

and replace_var_decl_list (vt:var_rep_table) (tt:type_rep_table) (vl:var_decl_list) : (var_decl_list * bool) =
   match vl with
   | VarDeclList(p,v,(p2,vl)) ->
      let (res,f) = List.fold_right (fun x (r,flag) ->
         let (r2,found) = replace_var_decl vt tt x in
         (r2::r, flag||found)
      ) (v::vl) ([],false) in
     (VarDeclList(p,List.hd res,(p2,List.tl res)),f)

and replace_ltype (vt:var_rep_table) (tt:type_rep_table) (t:ltype) : (ltype * bool) =
   match t with
   | IdType(p,i) -> (try (List.assoc i tt, true)
                    with Not_found -> (IdType(p,i),false))
   | ArrayType(p,l,e) ->
      let (l2,f) = replace_ltype vt tt l in
      let (e2,f2) = replace_exp vt tt e in
         (ArrayType(p,l2,e2),f||f2)
   | StructType(p,TypeList(p2,l,(p3,ll))) ->
      let (res,f) = List.fold_right (fun x (r,flag) ->
         let (r2,found) = replace_ltype vt tt x in
         (r2::r, flag||found)
      ) (l::ll) ([],false) in
      (StructType(p,TypeList(p2,List.hd res,(p3,List.tl res))),f)

and replace_node (vt:var_rep_table) (tt:type_rep_table) (n:node_decl) : (node_decl*bool) =
   match n with
   | NodeDecl(p,i,il1,il2,(p2,ld),b) ->
      let (il1_2,f1) = replace_in_param_list vt tt il1 in
      let (il2_2,f2) = replace_in_param_list vt tt il2 in
      let (ld2,f3) = (match ld with
        | Some(x) -> let (x2,f5) = replace_local_decl vt tt x in
                     (Some(x2),f5)
        | None -> (None,false)) in
      let (b2,f4) = replace_body vt tt b in
      (NodeDecl(p,i,il1_2,il2_2,(p2,ld2),b2),f1||f2||f3||f4)

and replace_local_decl (vt:var_rep_table) (tt:type_rep_table) (l:local_decl) : (local_decl*bool) =
   match l with
   | LocalDecl(p,(p2,cl)) ->
      let (res,f) = List.fold_right (fun x (r,flag) ->
         let (r2,found) = replace_clocked_var_decl vt tt x in
         (r2::r, flag||found)
      ) cl ([],false) in
      (LocalDecl(p,(p2,res)),f)

and replace_clocked_var_decl (vt:var_rep_table) (tt:type_rep_table) (c:clocked_var_decl) : (clocked_var_decl*bool) =
   match c with
   | ClockedVarDecl(p,v) ->
      let (v2,f) = replace_var_decl vt tt v in
      (ClockedVarDecl(p,v2),f)
   | WhenClockedVarDecl(p,vl,i) ->
      let (vl2,f) = replace_var_decl_list vt tt vl in
      (WhenClockedVarDecl(p,vl2,i),f)

and replace_in_param_list (vt:var_rep_table) (tt:type_rep_table) (il:in_param_list) : (in_param_list*bool) =
   match il with
   | InParamList(p,i,(p2,il)) ->
      let (res,f) = List.fold_right (fun x (r,flag) ->
         let (r2,found) = replace_in_param vt tt x in
         (r2::r, flag||found)
      ) (i::il) ([],false) in
      (InParamList(p,List.hd res,(p2,List.tl res)),f)

and replace_in_param (vt:var_rep_table) (tt:type_rep_table) (i:in_param) : (in_param*bool) =
   match i with
   | InParam(p,c) ->
      let (c2,f) = replace_clocked_var_decl vt tt c in
      (InParam(p,c2),f)
   | ConstInParam(p,v) ->
      let (v2,f) = replace_var_decl vt tt v in
      (ConstInParam(p,v2),f)

and replace_body (vt:var_rep_table) (tt:type_rep_table) (b:body) : (body*bool) =
   match b with
   | Body(p,el,be) ->
      let (rel,f) = replace_equation_list vt tt el in
      (Body(p,rel,be),f)

and replace_equation_list (vt:var_rep_table) (tt:type_rep_table) (el:equation_list) : (equation_list*bool) =
   match el with
   | EquationList(p,(p2,eql)) ->
      let (res,f) = List.fold_right (fun x (r,flag) ->
         let (r2,found) = replace_equation vt tt x in
         (r2::r, flag||found)
      ) eql ([],false) in
     (EquationList(p,(p2,res)),f)

and replace_equation (vt:var_rep_table) (tt:type_rep_table) (e:equation) : (equation*bool) =
   match e with
   | AssertEquation(p,e) ->
      let (e2,f) = replace_exp vt tt e in
      (AssertEquation(p,e2),f)
   | AssignEquation(p,l,e) ->
      let (l2,f2) = replace_left_part vt tt l in
      let (e2,f) = replace_exp vt tt e in
      (AssignEquation(p,l2,e2),f||f2)
   | KindEquation(p,i,(p2,Some(e))) ->
      let (e2,f) = replace_exp vt tt e in
      (KindEquation(p,i,(p2,Some(e2))),f)
   | _ -> (e,false)

and replace_left_part (vt:var_rep_table) (tt:type_rep_table) (l:left_part) : (left_part*bool) =
   match l with
   | LeftPart(p,lel) ->
      let (lel2,f) = replace_left_elem_list vt tt lel in
      (LeftPart(p,lel2),f)
   | ParenLeftPart(p,lel) ->
      let (lel2,f) = replace_left_elem_list vt tt lel in
      (LeftPart(p,lel2),f)

and replace_left_elem_list (vt:var_rep_table) (tt:type_rep_table) (l:left_elem_list) : (left_elem_list*bool) =
   match l with
   | LeftElemList(p,l,(p2,ll)) ->
      let (res,f) = List.fold_right (fun x (r,flag) ->
         let (r2,found) = replace_left_elem vt tt x in
         (r2::r, flag||found)
      ) (l::ll) ([],false) in
      (LeftElemList(p,List.hd res,(p2,List.tl res)),f)

and exp_to_left_elem (e:exp) : left_elem =
   match e with
   | IdExp(p,id) -> IdLeftElem(p,id)
   | TupleExp(p,ExpList(p2,e,(p3,el))) ->
         let l = List.map (fun x -> exp_to_left_elem x) (e::el) in
         StructLeftElem(p,StructFilter(p,LeftElemList(p2,List.hd l,(p3,List.tl l))))
   | _ -> failwith("exp_to_left_elem: TODO cant do this yet!")


and replace_left_elem (vt:var_rep_table) (tt:type_rep_table) (l:left_elem) : (left_elem*bool) =
   match l with
   | IdLeftElem(p,i) -> (try (exp_to_left_elem (List.assoc i vt), true)
                    with Not_found -> (IdLeftElem(p,i),
                    false))
   | StructLeftElem(p,StructFilter(p2,lel)) ->
      let (lel2,f) = replace_left_elem_list vt tt lel in
      (StructLeftElem(p,StructFilter(p2,lel2)),f)
   | SliceLeftElem(p,ta) ->
      let (ta2,f) = replace_tab_access vt tt ta in
      (SliceLeftElem(p,ta2),f)

and replace_tab_access (vt:var_rep_table) (tt:type_rep_table) (ta:tab_access) : (tab_access*bool) =
   match ta with
   | TabAccess(p,i,s) ->
      let (s2,f) = replace_selector vt tt s in
      (TabAccess(p,i,s2),f)
   | MultiTabAccess(p,t,s) ->
      let (t2,f) = replace_tab_access vt tt t in
      let (s2,f2) = replace_selector vt tt s in
      (MultiTabAccess(p,t2,s2),f||f2)

and replace_selector (vt:var_rep_table) (tt:type_rep_table) (s:selector) : (selector*bool) =
   match s with
   | Selector(p,e,ss) ->
      let (e2,f) = replace_exp vt tt e in
      let (ss2,f2) = replace_sel_sub vt tt ss in
      (Selector(p,e,ss),f||f2)

and replace_exp (vt:var_rep_table) (tt:type_rep_table) (e:exp) : (exp*bool) =
   match e with
   | IdExp(p,i) -> (try (List.assoc i vt, true)
                    with Not_found -> (IdExp(p,i),
                    false))
   | NodeExp(p,i,el) ->
      let (el2,f) = replace_exp_list vt tt el in
      (NodeExp(p,i,el2),f)
   | ListExp(p,el) ->
      let (el2,f) = replace_exp_list vt tt el in
      (ListExp(p,el2),f)
   | TupleExp(p,el) ->
      let (el2,f) = replace_exp_list vt tt el in
      (TupleExp(p,el2),f)
   | NotExp(p,e) ->
      let (e2,f) = replace_exp vt tt e in
      (NotExp(p,e2),f)
   | NegExp(p,e) ->
      let (e2,f) = replace_exp vt tt e in
      (NegExp(p,e2),f)
   | PreExp(p,e) ->
      let (e2,f) = replace_exp vt tt e in
      (PreExp(p,e2),f)
   | CurrentExp(p,e) ->
      let (e2,f) = replace_exp vt tt e in
      (CurrentExp(p,e2),f)
   | ArrowExp(p,e,et) ->
      let (e2,f) = replace_exp vt tt e in
      let (et2,f2) = replace_exp vt tt et in
      (ArrowExp(p,e2,et2),f||f2)
   | WhenExp(p,e,et) ->
      let (e2,f) = replace_exp vt tt e in
      let (et2,f2) = replace_exp vt tt et in
      (WhenExp(p,e2,et2),f||f2)
   | OrExp(p,e,et) ->
      let (e2,f) = replace_exp vt tt e in
      let (et2,f2) = replace_exp vt tt et in
      (OrExp(p,e2,et2),f||f2)
   | XorExp(p,e,et) ->
      let (e2,f) = replace_exp vt tt e in
      let (et2,f2) = replace_exp vt tt et in
      (XorExp(p,e2,et2),f||f2)
   | AndExp(p,e,et) ->
      let (e2,f) = replace_exp vt tt e in
      let (et2,f2) = replace_exp vt tt et in
      (AndExp(p,e2,et2),f||f2)
   | ImpExp(p,e,et) ->
      let (e2,f) = replace_exp vt tt e in
      let (et2,f2) = replace_exp vt tt et in
      (ImpExp(p,e2,et2),f||f2)
   | EqExp(p,e,et) ->
      let (e2,f) = replace_exp vt tt e in
      let (et2,f2) = replace_exp vt tt et in
      (EqExp(p,e2,et2),f||f2)
   | DiamondExp(p,e,et) ->
      let (e2,f) = replace_exp vt tt e in
      let (et2,f2) = replace_exp vt tt et in
      (DiamondExp(p,e2,et2),f||f2)
   | LtExp(p,e,et) ->
      let (e2,f) = replace_exp vt tt e in
      let (et2,f2) = replace_exp vt tt et in
      (LtExp(p,e2,et2),f||f2)
   | GtExp(p,e,et) ->
      let (e2,f) = replace_exp vt tt e in
      let (et2,f2) = replace_exp vt tt et in
      (GtExp(p,e2,et2),f||f2)
   | LteExp(p,e,et) ->
      let (e2,f) = replace_exp vt tt e in
      let (et2,f2) = replace_exp vt tt et in
      (LteExp(p,e2,et2),f||f2)
   | GteExp(p,e,et) ->
      let (e2,f) = replace_exp vt tt e in
      let (et2,f2) = replace_exp vt tt et in
      (GteExp(p,e2,et2),f||f2)
   | PlusExp(p,e,et) ->
      let (e2,f) = replace_exp vt tt e in
      let (et2,f2) = replace_exp vt tt et in
      (PlusExp(p,e2,et2),f||f2)
   | MinusExp(p,e,et) ->
      let (e2,f) = replace_exp vt tt e in
      let (et2,f2) = replace_exp vt tt et in
      (MinusExp(p,e2,et2),f||f2)
   | StarExp(p,e,et) ->
      let (e2,f) = replace_exp vt tt e in
      let (et2,f2) = replace_exp vt tt et in
      (StarExp(p,e2,et2),f||f2)
   | SlashExp(p,e,et) ->
      let (e2,f) = replace_exp vt tt e in
      let (et2,f2) = replace_exp vt tt et in
      (SlashExp(p,e2,et2),f||f2)
   | DivExp(p,e,et) ->
      let (e2,f) = replace_exp vt tt e in
      let (et2,f2) = replace_exp vt tt et in
      (DivExp(p,e2,et2),f||f2)
   | ModExp(p,e,et) ->
      let (e2,f) = replace_exp vt tt e in
      let (et2,f2) = replace_exp vt tt et in
      (ModExp(p,e2,et2),f||f2)
   | ArrayExp(p,e,et) ->
      let (e2,f) = replace_exp vt tt e in
      let (et2,f2) = replace_exp vt tt et in
      (ArrayExp(p,e2,et2),f||f2)
   | ConcatExp(p,e,et) ->
      let (e2,f) = replace_exp vt tt e in
      let (et2,f2) = replace_exp vt tt et in
      (ConcatExp(p,e2,et2),f||f2)
   | SliceExp(p,e,et,ss) ->
      let (e2,f) = replace_exp vt tt e in
      let (et2,f2) = replace_exp vt tt et in
      let (ss2,f3) = replace_sel_sub vt tt ss in
      (SliceExp(p,e2,et2,ss2),f||f2||f3)
   | IfExp(p,e,et,es) ->
      let (e2,f) = replace_exp vt tt e in
      let (et2,f2) = replace_exp vt tt et in
      let (es2,f3) = replace_exp vt tt es in
      (IfExp(p,e2,et2,es2),f||f2||f3)
   | WithExp(p,e,et,es) ->
      let (e2,f) = replace_exp vt tt e in
      let (et2,f2) = replace_exp vt tt et in
      let (es2,f3) = replace_exp vt tt es in
      (WithExp(p,e2,et2,es2),f||f2||f3)
   | PoundExp(p,el) ->
      let (el2,f) = replace_exp_list vt tt el in
      (PoundExp(p,el2),f)
   | _ -> (e,false)

and replace_exp_list (vt:var_rep_table) (tt:type_rep_table) (el:exp_list) : (exp_list*bool) =
   match el with ExpList(p,ex,(p2,exl)) ->
      let (a,b) = List.fold_right (fun e (res,found) ->
         let (r,f) = replace_exp vt tt e in
         (r::res, found||f)
      ) (ex::exl) ([],false) in
      (ExpList(p,List.hd a,(p2,List.tl a)),b)

and replace_sel_sub (vt:var_rep_table) (tt:type_rep_table) (ss:sel_sub) : (sel_sub*bool) =
   match ss with
   | SelSub(p,(p2,Some(e1,sss))) ->
      let (e1r,f1) = replace_exp vt tt e1 in
      (match sss with
      | SelSubSub(p3,(p4,Some(e2))) ->
         let (e2r,f2) = replace_exp vt tt e2 in
         (SelSub(p,(p2,Some(e1r,SelSubSub(p3,(p4,Some(e2r)))))),f1||f2)
      | _ -> (SelSub(p,(p2,Some(e1r,sss))),f1))
   | _ -> (ss,false)
;;

let propagate_globals_and_types (p:program) : program =
   let (greps,cl2) = get_global_const_reps p in
   let (treps,tl2) = get_type_reps p in
   match p with
   | Program(a,b,LusFile(c,(d,e,f,fl,nl))) ->
      (* propagate into the functions *)
      let fl2 = List.map (fun f ->
         let (res,_) = List.fold_left (fun (fn,gr) _ ->
            let g = List.hd gr in
            let more = List.map (fun (x,y) -> (x,fst (replace_exp [g] [] y))) (List.tl gr) in
            (fst (replace_func_decl [g] [] fn), more)
         ) (f,greps) greps in
         let (res2,_) = List.fold_left (fun (fn,tr) _ ->
            let t = List.hd tr in
            let more = List.map (fun (x,y) -> (x,fst (replace_ltype [] [t] y))) (List.tl tr) in
            (fst (replace_func_decl [] [t] fn), more)
         ) (res,treps) treps in
         res2
      ) fl in
      (* propagate into the nodes *)
      let nl2 = List.map (fun n ->
         let (res,_) = List.fold_left (fun (nn,gr) _ ->
            let g = List.hd gr in
            let more = List.map (fun (x,y) -> (x,fst (replace_exp [g] [] y))) (List.tl gr) in
            (fst (replace_node [g] [] nn), more)
         ) (n,greps) greps in
         let (res2,_) = List.fold_left (fun (nn,tr) _ ->
            let t = List.hd tr in
            let more = List.map (fun (x,y) -> (x,fst (replace_ltype [] [t] y))) (List.tl tr) in
            (fst (replace_node [] [t] nn), more)
         ) (res,treps) treps in
         res2
      ) nl in
      Program(a,b,LusFile(c,(d,tl2,cl2,fl2,nl2)))
;;

(**********************************************************)
(** STEP 3  -  FLATTEN INPUT/OUTPUT/LOCAL DECLARATIONS  ***)
(**********************************************************)

let
rec flatten_decls (p:program) : program =
   match p with
   | Program(a,b,LusFile(c,(d,tl,cl,fl,nl))) ->
         (* TODO - handle functions list *)
      Program(a,b,LusFile(c,(d,tl,cl,fl,List.map (fun n ->
         flatten_decls_node_decl n) nl)))

and flatten_decls_node_decl (n:node_decl) : node_decl =
   match n with
   | NodeDecl(a,b,il1,il2,(c,loc),d) ->
      let loc2 = (match loc with
      | None -> None
      | Some(x) -> Some(flatten_decls_local_decl x)) in
   NodeDecl(a,b,flatten_decls_in_param_list il1,flatten_decls_in_param_list il2,(c,loc2),d)

and flatten_decls_local_decl (l:local_decl) : local_decl =
   match l with
   | LocalDecl(p,(p2,cl)) ->
      let l = List.fold_left (fun a x -> a@(flatten_decls_clocked_var_decl x)) [] cl in
      LocalDecl(p,(p2,l))

and flatten_decls_in_param_list (il:in_param_list) : in_param_list =
   match il with
   | InParamList(p,i,(p2,il)) ->
      let l = List.fold_left (fun a x -> a@(flatten_decls_in_param x)) [] (i::il) in
      InParamList(p,List.hd l,(p2,List.tl l))

and flatten_decls_in_param (i:in_param) : in_param list =
   match i with
   | InParam(p,c) -> List.map (fun x -> InParam(p,x)) (flatten_decls_clocked_var_decl c)
   | ConstInParam(p,v) -> List.map (fun x -> ConstInParam(p,x)) (flatten_decls_var_decl v)

and flatten_decls_clocked_var_decl (c:clocked_var_decl) : clocked_var_decl list =
   match c with
   | ClockedVarDecl(p,v) -> List.map (fun x -> ClockedVarDecl(p,x)) (flatten_decls_var_decl v)
   | WhenClockedVarDecl(p,vl,i) -> List.map (fun x ->
         WhenClockedVarDecl(p,x,i)) (flatten_decls_var_decl_list vl)

and flatten_decls_var_decl_list (vl:var_decl_list) : var_decl_list list =
   match vl with
   | VarDeclList(p,v,(p2,vs)) ->
      let l = List.fold_left (fun a x -> a@(flatten_decls_var_decl x)) [] (v::vs) in
         List.map (fun x -> VarDeclList(p,x,(p2,[]))) l

and flatten_decls_var_decl (v:var_decl) : var_decl list =
   match v with
   | VarDecl(p,VarList(p2,i,(p3,il)),lt) ->
         List.map (fun x -> VarDecl(p,VarList(p2,x,(p3,[])),lt)) (i::il)
;;

(**********************************************************)
(** STEP 4  -  EXPAND NODE CALLS                        ***)
(**********************************************************)

type parameter = (int * ltype * bool * int option);;

let
rec expand_node_calls (p:program) (n:node_decl) : program =
   match p with
   | Program(a,b,LusFile(c,(d,tl,cl,fl,nl))) ->
      let nl2 = List.map (fun x -> if x==n then (expand_node_calls_node p x) else x) nl in
      Program(a,b,LusFile(c,(d,tl,cl,fl,nl2)))

and expand_node_calls_node (p:program) (n:node_decl) : node_decl =
   match n with
   | NodeDecl(a,b,il1,il2,(c,loc),Body(d,el,be)) ->
      let (el2,cl) = expand_node_calls_equation_list p el in
      let nloc = add_to_local_decl c loc cl in
   NodeDecl(a,b,il1,il2,(c,nloc),Body(d,el2,be))

and add_to_local_decl p (ld:local_decl option) (cl:clocked_var_decl list) : local_decl option =
   match ld with
   | None ->
      (match cl with
      | [] -> None
      | _ -> Some(LocalDecl(p,(p,cl))))
   | Some(LocalDecl(p3,(p4,cl2))) -> Some(LocalDecl(p3,(p4,cl2@cl)))

and expand_node_calls_equation_list (pr:program) (ell:equation_list) : (equation_list * clocked_var_decl list) =
   match ell with
   | EquationList(p,(p2,el)) ->
   let (nel,ncl) = List.fold_left (fun (cel,ccl) e ->
      let (el3,cl3) = expand_node_calls_equation pr e in
      (cel @ el3, ccl @ cl3)
   ) ([],[]) el in
   (EquationList(p,(p2,nel)),ncl)

and expand_node_calls_equation (pr:program) (eq:equation) : (equation list * clocked_var_decl list) =
   match eq with
   | AssertEquation(p,e) ->
      let (ne,el,cl) = expand_node_calls_exp pr e in
      (el @ [AssertEquation(p,ne)], cl)
   | AssignEquation(p,l,e) ->
      let (ne,el,cl) = expand_node_calls_exp pr e in
      (el @ [AssignEquation(p,l,ne)], cl)
   | KindEquation(p,i,(p2,Some(e))) ->
      let (ne,el,cl) = expand_node_calls_exp pr e in
      (el @ [KindEquation(p,i,(p2,Some(ne)))], cl)
   | _ -> ([eq],[])

and expand_node_calls_exp (pr:program) (ex:exp) : (exp * equation list * clocked_var_decl list) =
   match ex with
   | NodeExp(p,id,el) ->
      let (exl,eql,cl) = expand_node_calls_exp_list pr el in
      (match exl with
      | ExpList(_,e,(_,es)) ->
         let (e,eql2,cl2) = expand_node33 pr (get_node pr id) (e::es) in
         (e,eql@eql2,cl@cl2))
   | ListExp(p,el) ->
      let (exl,eql,cl) = expand_node_calls_exp_list pr el in
      (ListExp(p,exl),eql,cl)
   | TupleExp(p,el) ->
      let (exl,eql,cl) = expand_node_calls_exp_list pr el in
      (TupleExp(p,exl),eql,cl)
   | NotExp(p,e) ->
      let (ex,eql,cl) = expand_node_calls_exp pr e in
      (NotExp(p,ex),eql,cl)
   | NegExp(p,e) ->
      let (ex,eql,cl) = expand_node_calls_exp pr e in
      (NegExp(p,ex),eql,cl)
   | PreExp(p,e) ->
      let (ex,eql,cl) = expand_node_calls_exp pr e in
      (PreExp(p,ex),eql,cl)
   | CurrentExp(p,e) ->
      let (ex,eql,cl) = expand_node_calls_exp pr e in
      (CurrentExp(p,ex),eql,cl)
   | ArrowExp(p,e1,e2) ->
      let (ex,eql,cl) = expand_node_calls_exp pr e1 in
      let (ex2,eql2,cl2) = expand_node_calls_exp pr e2 in
      (ArrowExp(p,ex,ex2),eql@eql2,cl@cl2)
   | WhenExp(p,e1,e2) ->
      let (ex,eql,cl) = expand_node_calls_exp pr e1 in
      let (ex2,eql2,cl2) = expand_node_calls_exp pr e2 in
      (WhenExp(p,ex,ex2),eql@eql2,cl@cl2)
   | OrExp(p,e1,e2) ->
      let (ex,eql,cl) = expand_node_calls_exp pr e1 in
      let (ex2,eql2,cl2) = expand_node_calls_exp pr e2 in
      (OrExp(p,ex,ex2),eql@eql2,cl@cl2)
   | XorExp(p,e1,e2) ->
      let (ex,eql,cl) = expand_node_calls_exp pr e1 in
      let (ex2,eql2,cl2) = expand_node_calls_exp pr e2 in
      (XorExp(p,ex,ex2),eql@eql2,cl@cl2)
   | AndExp(p,e1,e2) ->
      let (ex,eql,cl) = expand_node_calls_exp pr e1 in
      let (ex2,eql2,cl2) = expand_node_calls_exp pr e2 in
      (AndExp(p,ex,ex2),eql@eql2,cl@cl2)
   | ImpExp(p,e1,e2) ->
      let (ex,eql,cl) = expand_node_calls_exp pr e1 in
      let (ex2,eql2,cl2) = expand_node_calls_exp pr e2 in
      (ImpExp(p,ex,ex2),eql@eql2,cl@cl2)
   | EqExp(p,e1,e2) ->
      let (ex,eql,cl) = expand_node_calls_exp pr e1 in
      let (ex2,eql2,cl2) = expand_node_calls_exp pr e2 in
      (EqExp(p,ex,ex2),eql@eql2,cl@cl2)
   | DiamondExp(p,e1,e2) ->
      let (ex,eql,cl) = expand_node_calls_exp pr e1 in
      let (ex2,eql2,cl2) = expand_node_calls_exp pr e2 in
      (DiamondExp(p,ex,ex2),eql@eql2,cl@cl2)
   | LtExp(p,e1,e2) ->
      let (ex,eql,cl) = expand_node_calls_exp pr e1 in
      let (ex2,eql2,cl2) = expand_node_calls_exp pr e2 in
      (LtExp(p,ex,ex2),eql@eql2,cl@cl2)
   | GtExp(p,e1,e2) ->
      let (ex,eql,cl) = expand_node_calls_exp pr e1 in
      let (ex2,eql2,cl2) = expand_node_calls_exp pr e2 in
      (GtExp(p,ex,ex2),eql@eql2,cl@cl2)
   | LteExp(p,e1,e2) ->
      let (ex,eql,cl) = expand_node_calls_exp pr e1 in
      let (ex2,eql2,cl2) = expand_node_calls_exp pr e2 in
      (LteExp(p,ex,ex2),eql@eql2,cl@cl2)
   | GteExp(p,e1,e2) ->
      let (ex,eql,cl) = expand_node_calls_exp pr e1 in
      let (ex2,eql2,cl2) = expand_node_calls_exp pr e2 in
      (GteExp(p,ex,ex2),eql@eql2,cl@cl2)
   | PlusExp(p,e1,e2) ->
      let (ex,eql,cl) = expand_node_calls_exp pr e1 in
      let (ex2,eql2,cl2) = expand_node_calls_exp pr e2 in
      (PlusExp(p,ex,ex2),eql@eql2,cl@cl2)
   | MinusExp(p,e1,e2) ->
      let (ex,eql,cl) = expand_node_calls_exp pr e1 in
      let (ex2,eql2,cl2) = expand_node_calls_exp pr e2 in
      (MinusExp(p,ex,ex2),eql@eql2,cl@cl2)
   | StarExp(p,e1,e2) ->
      let (ex,eql,cl) = expand_node_calls_exp pr e1 in
      let (ex2,eql2,cl2) = expand_node_calls_exp pr e2 in
      (StarExp(p,ex,ex2),eql@eql2,cl@cl2)
   | SlashExp(p,e1,e2) ->
      let (ex,eql,cl) = expand_node_calls_exp pr e1 in
      let (ex2,eql2,cl2) = expand_node_calls_exp pr e2 in
      (SlashExp(p,ex,ex2),eql@eql2,cl@cl2)
   | DivExp(p,e1,e2) ->
      let (ex,eql,cl) = expand_node_calls_exp pr e1 in
      let (ex2,eql2,cl2) = expand_node_calls_exp pr e2 in
      (DivExp(p,ex,ex2),eql@eql2,cl@cl2)
   | ModExp(p,e1,e2) ->
      let (ex,eql,cl) = expand_node_calls_exp pr e1 in
      let (ex2,eql2,cl2) = expand_node_calls_exp pr e2 in
      (ModExp(p,ex,ex2),eql@eql2,cl@cl2)
   | ArrayExp(p,e1,e2) ->
      let (ex,eql,cl) = expand_node_calls_exp pr e1 in
      let (ex2,eql2,cl2) = expand_node_calls_exp pr e2 in
      (ArrayExp(p,ex,ex2),eql@eql2,cl@cl2)
   | ConcatExp(p,e1,e2) ->
      let (ex,eql,cl) = expand_node_calls_exp pr e1 in
      let (ex2,eql2,cl2) = expand_node_calls_exp pr e2 in
      (ConcatExp(p,ex,ex2),eql@eql2,cl@cl2)
   | IfExp(p,e1,e2,e3) ->
      let (ex,eql,cl) = expand_node_calls_exp pr e1 in
      let (ex2,eql2,cl2) = expand_node_calls_exp pr e2 in
      let (ex3,eql3,cl3) = expand_node_calls_exp pr e3 in
      (IfExp(p,ex,ex2,ex3),eql@eql2@eql3,cl@cl2@cl3)
   | WithExp(p,e1,e2,e3) ->
      let (ex,eql,cl) = expand_node_calls_exp pr e1 in
      let (ex2,eql2,cl2) = expand_node_calls_exp pr e2 in
      let (ex3,eql3,cl3) = expand_node_calls_exp pr e3 in
      (WithExp(p,ex,ex2,ex3),eql@eql2@eql3,cl@cl2@cl3)
   | SliceExp(p,e1,e2,ss) ->
      let (ex,eql,cl) = expand_node_calls_exp pr e1 in
      let (ex2,eql2,cl2) = expand_node_calls_exp pr e2 in
      (SliceExp(p,ex,ex2,ss),eql@eql2,cl@cl2)
   | PoundExp(p,el) ->
      let (exl,eql,cl) = expand_node_calls_exp_list pr el in
      (PoundExp(p,exl),eql,cl)
   | _ -> (ex,[],[])

and expand_node_calls_exp_list (pr:program) (el:exp_list) : (exp_list * equation list * clocked_var_decl list) =
   match el with
   | ExpList(p,e,(p2,es)) ->
      let (rel,reql,rcl) = List.fold_left (fun (nel,neql,ncl) ex ->
         let (mel,meql,mcl) = expand_node_calls_exp pr ex in
         (nel @ [mel], neql @ meql, ncl @ mcl)
      ) ([],[],[]) (e::es) in
      (ExpList(p,List.hd rel,(p2,List.tl rel)),reql,rcl)

and get_inputs_data (il:in_param_list) (el:exp list) : (var_rep_table * equation list * clocked_var_decl list) =
   match il with
   | InParamList(_,i,(_,is)) ->
      let thelist = (i::is) in
      if (List.length thelist)<>(List.length el) then failwith "get_inputs_data: incorrect number of params!";
         List.fold_left2 (fun (nvt,nel,ncl) x e ->
         (match x with
         | InParam(p,c) ->
            (match c with
            | ClockedVarDecl(p,VarDecl(p2,VarList(p3,id,p4),p5)) ->
                  let newid = create_fresh_sym id in
                  (nvt @[(id,IdExp(p,newid))],
                  nel@[AssignEquation(p,LeftPart(p,LeftElemList(p,IdLeftElem(p,newid),(p,[]))),e)],
                  ncl@[ClockedVarDecl(p,VarDecl(p2,VarList(p3,newid,p4),p5))])
            | WhenClockedVarDecl(p,VarDeclList(p2,VarDecl(p3,VarList(p4,id,p5),p6),p7),p8) ->
                  let newid = create_fresh_sym id in
                  (nvt @[(id,IdExp(p,newid))],
                  nel@[AssignEquation(p,LeftPart(p,LeftElemList(p,IdLeftElem(p,newid),(p,[]))),e)],
                  ncl@[WhenClockedVarDecl(p,VarDeclList(p2,VarDecl(p3,VarList(p4,newid,p5),p6),p7),p8)]))
         | ConstInParam(p,VarDecl(_,VarList(_,id,_),_)) ->
               (* TODO - compute this exp as a constant *)
            let newid = create_fresh_sym id in
            (nvt @ [(id,e)],nel,ncl)
         )
      ) ([],[],[]) thelist (el)

and get_outputs_data (il:in_param_list) : (var_rep_table * exp * clocked_var_decl list) =
   match il with
   | InParamList(p,i,(_,is)) -> let (rt,el,cl) = List.fold_left (fun (nvt,nel,ncl) x ->
         (match x with
         | InParam(_,c) ->
            (match c with
            | ClockedVarDecl(p,VarDecl(p1,VarList(p2,id,p3),p4)) ->
               let newid = create_fresh_sym id in
               let thex = IdExp(p,newid) in
               (nvt @ [(id,thex)],nel @ [thex],ncl@[ClockedVarDecl(p,VarDecl(p1,VarList(p2,newid,p3),p4))])
            | WhenClockedVarDecl(p,VarDeclList(p1,VarDecl(p2,VarList(p3,id,p4),p5),p6),p7) ->
               let newid = create_fresh_sym id in
               let thex = IdExp(p,newid) in
               (nvt @ [(id,thex)],nel @
               [thex],ncl@[WhenClockedVarDecl(p,VarDeclList(p1,VarDecl(p2,VarList(p3,newid,p4),p5),p6),p7)])
            )
         | ConstInParam(_,VarDecl(_,VarList(_,id,_),_)) ->
            let newid = create_fresh_sym id in
            let thex = IdExp(p,newid) in
            (nvt @ [(id,thex)],nel @ [thex],ncl ))
   ) ([],[],[]) (i::is) in
   (rt, (if (List.length el)>1 then ListExp(p,ExpList(p,List.hd el,(p,List.tl
   el))) else List.hd el),cl)

and get_locals_data (ld:local_decl option) : (var_rep_table * clocked_var_decl list) =
   match ld with
   | None -> ([],[])
   | Some(LocalDecl(_,(_,cl))) ->
      List.fold_left (fun (nvt,ncl) c ->
         match c with
         | ClockedVarDecl(p1,VarDecl(p2,VarList(p3,id,p4),p5)) ->
            let newid = create_fresh_sym id in
            (nvt@[(id,IdExp(p1,newid))],ncl@[ClockedVarDecl(p1,VarDecl(p2,VarList(p3,newid,p4),p5))])
         | WhenClockedVarDecl(p1,VarDeclList(p2,VarDecl(p3,VarList(p4,id,p5),p6),p7),p8) ->
            let newid = create_fresh_sym id in
            (nvt@[(id,IdExp(p1,newid))],ncl@[WhenClockedVarDecl(p1,VarDeclList(p2,VarDecl(p3,VarList(p4,newid,p5),p6),p7),p8)])
      ) ([],[]) cl

and get_input_equations (pl:parameter list) (el:exp list) : equation list =
   if (List.length pl)<>(List.length el) then failwith "get_input_equations: incorrect number of params!";
   []

and get_output_exp p (pl:parameter list) : exp =
   let el = List.map (fun (id,lt,c,w) ->
      IdExp(p,id)
   ) pl in
   if (List.length el)>1 then ListExp(p,ExpList(p,List.hd el,(p,List.tl el))) else List.hd el

and expand_node33 (p:program) (n:node_decl) (el:exp list) : (exp * equation list * clocked_var_decl list) =
   match n with
   | NodeDecl(a,nodeid,il1,il2,(c,loc),Body(d,EquationList(p1,(p2,bel)),be)) ->
      (*print_string ("EXPAND NODE: "^(get_sym_name nodeid)^"\n");*)
      let (inrep,ineq,incl) = get_inputs_data il1 el in
      let (outrep,outex,outcl) = get_outputs_data il2 in
      (* TODO - compile the constants in array indices!!! *)
      let (localrep,loccl) = get_locals_data loc in
      (*print_string "Inputs:\n";
      print_param_list inputs;
      print_string "Outputs:\n";
      print_param_list outputs;
      print_string "Locals:\n";
      print_int (List.length locals);
      print_string "\n";
      print_string "Called with:\n";
      List.iter (fun e -> Lsimplify_pp.pp_exp e; print_string "\n") el;*)
      let reps = inrep @ outrep @ localrep in
      let nbel = List.map (fun e -> fst (replace_equation reps [] e)) bel in
      let nloc = List.map (fun e -> fst (replace_clocked_var_decl reps [] e)) loccl in
      let (el3,cl3) = List.fold_left (fun (cel,ccl) e ->
         let (el3,cl3) = expand_node_calls_equation p e in
         (cel @ el3, ccl @ cl3)
      ) ([],[]) (ineq@nbel) in
      finish_scope nodeid;
      (outex,el3,incl@outcl@cl3@nloc)

and print_param_list (pl:parameter list) =
   List.iter (fun (id,lt,c,w) ->
      print_string "  ";
      if c then print_string "const ";
      print_string (get_sym_name id);
      print_string " : ";
      Lsimplify_pp.pp_ltype lt;
      (match w with
      | None -> ()
      | Some(i) -> print_string (" when "^(get_sym_name i)));
      print_string "\n"
   ) pl
;;

(**********************************************************)
(** STEP 5  -  EXPAND TUPLES AND ARRAYS                 ***)
(**********************************************************)

let
rec get_tuple_reps_local_decl (ld:local_decl) : (var_rep_table * local_decl) =
   match ld with
   | LocalDecl(p,(p2,cl)) -> let (vt,cl2) = List.fold_left (fun (vtl,cll) c ->
      let (vtt,clt) = get_tuple_reps_clocked_var_decl c in
      (vtl @ vtt, cll @ clt)
   ) ([],[]) cl in
   (vt,LocalDecl(p,(p2,cl2)))

and get_tuple_reps_in_param_list (il:in_param_list) : (var_rep_table * in_param_list) =
   match il with
   | InParamList(p1,i,(p2,il)) ->
         let (t,il2) = List.fold_right (fun ip (rt,tl) ->
            let (rt2,ip) = get_tuple_reps_in_param ip in
            (rt2 @ rt, ip @ tl)
         ) (i::il) ([],[]) in
         (t,InParamList(p1,List.hd il2,(p2,List.tl il2)))

and get_tuple_reps_in_param (i:in_param) : (var_rep_table * in_param list) =
   match i with
   | InParam(p,c) ->
      let (t,c2) = get_tuple_reps_clocked_var_decl c in
      (t,List.map (fun x->InParam(p,x)) c2)
   | ConstInParam(p,v) ->
      let (t,v2) = get_tuple_reps_var_decl v in
      (t,List.map (fun x->ConstInParam(p,x)) v2)

and get_tuple_reps_clocked_var_decl (c:clocked_var_decl) : (var_rep_table * clocked_var_decl list) =
   match c with
   | ClockedVarDecl(p,v) ->
      let (t,v2) = get_tuple_reps_var_decl v in
      (t,List.map (fun x -> ClockedVarDecl(p,x)) v2)
   | WhenClockedVarDecl(p,VarDeclList(p2,v,p3),i) ->
      let (t,vl) = get_tuple_reps_var_decl v in
      (t,List.map (fun v2 -> WhenClockedVarDecl(p,VarDeclList(p2,v2,p3),i)) vl)

and get_tuple_reps_var_decl (v:var_decl) : (var_rep_table * var_decl list) =
   match v with
   (* assume that this is a declaration for only one variable *)
   | VarDecl(p,VarList(p2,i,(p3,il)),lt) ->
      let (e,vl) = get_temp_reps v (get_sym_name i) in
      (*print_int i;
      print_string " -> ";
      Lsimplify_pp.pp_exp e;
      print_string "\n";*)
      ([(i,e)],vl)

   (* TODO - rename this to something that makes sense *)
and get_temp_reps (v:var_decl) (s:string) : (exp * var_decl list) =
   match v with
   | VarDecl(p1,VarList(p2,id,p3),t) ->
   (match t with
   | StructType(p,TypeList(_,lt,(_,ltl))) ->
      let newname1 = (s^"_0") in
      let newsym1 = add_sym newname1 NoScope in
      let (e1,vd1) = get_temp_reps (VarDecl(p,VarList(p,newsym1,(p,[])),lt)) (s^"_0") in
      let (e2,vd2,_) = List.fold_left (fun (e,vd,n) t ->
         let newname = (s^"_"^(string_of_int n)) in
         let newsym = add_sym newname NoScope in
         let (et,vdt) = get_temp_reps (VarDecl(p,VarList(p,newsym,(p,[])),t)) newname in
         (e @ [et], vd @ vdt, (n+1))
      ) ([],[],1) ltl in
      (TupleExp(p,ExpList(p,e1,(p,e2))), vd1 @ vd2)
   | ArrayType(p,lt,e) -> let e2 = compile_exp e in (match e2 with
      | IntExp(_,i) -> let l = duplicate_ltype lt i in
      get_temp_reps
      (VarDecl(p1,VarList(p2,id,p3),StructType(p,TypeList(p,List.hd l,(p,List.tl
      l))))) s
      | _ -> failwith("TODO get_temp_reps: array index not constant!"))
   (* array type or id type *)
   | _ -> (IdExp(p1,id),[v]))

and compile_exp (e:exp) : exp =
  let (ch,c,ce) = evaluate_exp e [] in
     if (not ch) then (
        if c then ce
        else
        failwith("compile_exp: expression not constant!")
     )
     else compile_exp ce

(* returns
      1. was there a change to the expression?
      2. was the input expression constant?
      3. the new flattened expression
*)
and evaluate_exp (e:exp) (vt:var_rep_table) : (bool*bool*exp) =
   match e with
   | IntExp(p,v) -> (false,true,e)
   | RealExp(p,v) -> (false,true,e)
   | IdExp(p,id) ->
      if (id=val_true)||(id=val_false) then
         (false,true,e)
      else
      (try let e2 = List.assoc id vt in (true,true,e2)
      with Not_found -> (false,false,e))
   | PlusExp(p,e1,e2) ->
      let (ch1,c1,e12) = evaluate_exp e1 vt in
      let (ch2,c2,e22) = evaluate_exp e2 vt in
      if c1&&c2 then ( (* if both expressions are constant, perform op *)
         match (e12,e22) with
         | (IntExp(p,v1),IntExp(_,v2)) -> (true,true,IntExp(p,v1+v2))
         | (IntExp(p,v1),RealExp(_,v2)) -> (true,true,RealExp(p,(float v1)+.v2))
         | (RealExp(p,v1),IntExp(_,v2)) -> (true,true,RealExp(p,v1+.(float v2)))
         | (RealExp(p,v1),RealExp(_,v2)) -> (true,true,RealExp(p,v1+.v2))
         | _ -> failwith("evaluate_exp: trying to add non-numbers!")
      ) else (
         (ch1||ch2,false,PlusExp(p,e12,e22))
      )
   | OrExp(p,e1,e2) ->
      let (ch1,c1,e12) = evaluate_exp e1 vt in
      let (ch2,c2,e22) = evaluate_exp e2 vt in
      if c1&&c2 then ( (* if both expressions are constant, perform op *)
         match (e12,e22) with
         | (IdExp(p,id1),IdExp(_,id2)) ->
            if (id1=val_false)&&(id2=val_false) then (true,true,IdExp(p,val_false))
            else if (id1=val_false)&&(id2=val_true) then (true,true,IdExp(p,val_true))
            else if (id1=val_true)&&(id2=val_false) then (true,true,IdExp(p,val_true))
            else if (id1=val_true)&&(id2=val_true) then (true,true,IdExp(p,val_true))
            else (ch1||ch2,false,OrExp(p,e12,e22))
         | _ -> failwith("evaluate_exp: trying to OR non-booleans!")
      ) else (
         (ch1||ch2,false,OrExp(p,e12,e22))
      )
   | AndExp(p,e1,e2) ->
      let (ch1,c1,e12) = evaluate_exp e1 vt in
      let (ch2,c2,e22) = evaluate_exp e2 vt in
      if c1&&c2 then ( (* if both expressions are constant, perform op *)
         match (e12,e22) with
         | (IdExp(p,id1),IdExp(_,id2)) ->
            if (id1=val_false)&&(id2=val_false) then (true,true,IdExp(p,val_false))
            else if (id1=val_false)&&(id2=val_true) then (true,true,IdExp(p,val_false))
            else if (id1=val_true)&&(id2=val_false) then (true,true,IdExp(p,val_false))
            else if (id1=val_true)&&(id2=val_true) then (true,true,IdExp(p,val_true))
            else (ch1||ch2,false,AndExp(p,e12,e22))
         | _ -> failwith("evaluate_exp: trying to AND non-booleans!")
      ) else (
         (ch1||ch2,false,AndExp(p,e12,e22))
      )
   (* TODO - add other cases *)
   | _ -> (false,false,e)

and duplicate_ltype (lt:ltype) (k:int) : (ltype list) =
   if k=0 then []
   else lt::(duplicate_ltype lt (k-1))

and expand_tuples (p:program) : program =
   let root = get_root_node p in
   match p with
   | Program(a,b,LusFile(c,(d,e,f,fl,nl))) ->
      Program(a,b,LusFile(c,(d,e,f,fl,
      List.map (fun n ->
         if n==root then expand_tuples_node_decl n
         else n
      ) nl)))

and expand_tuples_node_decl (n:node_decl) : node_decl =
   match n with
   | NodeDecl(p,i,il1,il2,(p2,loc),Body(p3,el,be)) ->
   let (vt,il1_2) = get_tuple_reps_in_param_list il1 in
   let (vt2,il2_2) = get_tuple_reps_in_param_list il2 in
   let (vt3,loc2) = (match loc with
      | None -> ([],loc)
      | Some(ld) -> let (vtt,ld2) = get_tuple_reps_local_decl ld in
         (vtt,Some(ld2))) in
   let (el2,_) = replace_equation_list (vt@vt2@vt3) [] el in
   NodeDecl(p,i,il1_2,il2_2,(p2,loc2),Body(p3,el2,be))
;;

(**********************************************************)
(** STEP 6  -  DO ARRAY OPERATIONS (SLICES, CONCATS...)  **)
(**********************************************************)

(*****************************************)
(*  TODO - these array ops need to happen with the structs on the left hand side
 *  *)
let rec do_array_ops (p:program) : program =
   let root = get_root_node p in
   match p with
   | Program(a,b,LusFile(c,(d,e,f,fl,nl))) ->
      Program(a,b,LusFile(c,(d,e,f,fl,
      List.map (fun n ->
         if n==root then do_array_ops_node_decl n
         else n
      ) nl)))

and do_array_ops_node_decl (n:node_decl) : node_decl =
   match n with
   | NodeDecl(p,i,il1,il2,loc,Body(p3,el,be)) ->
      let el2 = do_array_ops_equation_list el in
   NodeDecl(p,i,il1,il2,loc,Body(p3,el2,be))

and do_array_ops_equation_list (el:equation_list) : equation_list =
   match el with
   | EquationList(p,(p2,eql)) -> EquationList(p,(p2,List.map (fun e ->
      do_array_ops_equation e
   ) eql))

and do_array_ops_equation (e:equation) : equation =
   match e with
   | AssertEquation(p,ex) -> AssertEquation(p,do_array_ops_exp ex)
   (* TODO - we probably need to do this in the left_part *)
   | AssignEquation(p,lp,ex) -> AssignEquation(p,lp,do_array_ops_exp ex)
   | KindEquation(p,i,(p2,Some(ex))) -> KindEquation(p,i,(p2,Some(do_array_ops_exp ex)))
   | _ -> e

and copy_exp (e:exp) (k:int) : (exp list) =
   if k=0 then []
   else e::(copy_exp e (k-1))

and do_array_ops_exp (ex:exp) : exp =
   match ex with
   | ArrayExp(p,e1,e2) ->
      (match e2 with
      | IntExp(_,i) -> let l = copy_exp (do_array_ops_exp e1) i in
                       TupleExp(p,ExpList(p,List.hd l,(p,List.tl l)))
      | _ -> failwith("TODO: do_array_ops_exp: non-constant array index!"))
   | ConcatExp(p,e1,e2) ->
      (match (do_array_ops_exp e1,do_array_ops_exp e2) with
      | (TupleExp(p,ExpList(p2,et1,(p3,ets1))),TupleExp(_,ExpList(_,et2,(_,ets2)))) ->
         TupleExp(p,ExpList(p2,et1,(p3,(ets1)@(et2::ets2))))
      | _ -> failwith("TODO: do_array_ops_exp: trying to concat two
      non-lists!"))
         (* TODO - handle the sel_sub *)
   | SliceExp(_,e1,e2,ss) -> (match do_array_ops_exp e1 with
      | TupleExp(p,ExpList(p2,e,(p3,es))) -> (match do_array_ops_exp e2 with
         | IntExp(_,i) -> (try List.nth (e::es) i
                          with _ -> failwith("TODO: do_array_ops_exp: array slice start out of bounds!"))
         | _ -> failwith("TODO: do_array_ops_exp: array slice start not constant!"))
      | _ -> failwith("TODO: do_array_ops_exp: calling array slice on non-array!"))
   (* TODO - we need to do the array ops in all sub expressions (handle all
    * other exp cases!) *)
   | _ -> ex
;;

(**********************************************************)
(** STEP 7  -  EXPAND OPERATIONS VIA THEIR HOMOMORPHIC   **)
(**            EXTENSION                                 **)
(**********************************************************)

let rec do_homomorphic_extension (p:program) : program =
   let root = get_root_node p in
   match p with
   | Program(a,b,LusFile(c,(d,e,f,fl,nl))) ->
      Program(a,b,LusFile(c,(d,e,f,fl,
      List.map (fun n ->
         if n==root then do_homomorphic_extension_node_decl n
         else n
      ) nl)))

and do_homomorphic_extension_node_decl (n:node_decl) : node_decl =
   match n with
   | NodeDecl(p,i,il1,il2,loc,Body(p3,el,be)) ->
      let el2 = do_homomorphic_extension_equation_list el in
   NodeDecl(p,i,il1,il2,loc,Body(p3,el2,be))

and do_homomorphic_extension_equation_list (el:equation_list) : equation_list =
   match el with
   | EquationList(p,(p2,eql)) -> EquationList(p,(p2,List.map (fun e ->
      do_homomorphic_extension_equation e
   ) eql))

and do_homomorphic_extension_equation (e:equation) : equation =
   match e with
   | AssertEquation(p,ex) -> AssertEquation(p,do_homomorphic_extension_exp ex)
   (* TODO - we probably need to do this in the left_part *)
   | AssignEquation(p,lp,ex) -> AssignEquation(p,lp,do_homomorphic_extension_exp ex)
   | KindEquation(p,i,(p2,Some(ex))) -> KindEquation(p,i,(p2,Some(do_homomorphic_extension_exp ex)))
   | _ -> e

and do_homomorphic_extension_exp (ex:exp) : exp =
   match ex with
   | PlusExp(p,e1,e2) -> (match (do_homomorphic_extension_exp e1,do_homomorphic_extension_exp e2) with
      | (TupleExp(p,ExpList(p2,et1,(p3,est1))),TupleExp(_,ExpList(_,et2,(_,est2)))) ->
         (try
         let l = List.map2 (fun a b -> PlusExp(p2,a,b)) (et1::est1) (et2::est2) in
         TupleExp(p,ExpList(p2,List.hd l,(p3,List.tl l)))
         with _ -> failwith("TODO: do_homomorphic_extension: mapping failure!"))
   (* TODO - handle the other cases *)
      | (_,_) -> ex)
   | _ -> ex
;;

(**********************************************************)
(** STEP 8  -  EXPAND TUPLE AND LIST EQUALITIES          **)
(**********************************************************)

let rec equate_tuples (pr:program) =
   let root = get_root_node pr in
   match pr with
| Program(p,il,LusFile(p2,(p3,tl,cl,fl,nl))) ->
      Program(p,il,LusFile(p2,(p3,tl,cl,fl,List.map (fun x ->
         if x==root then equate_tuples_node x
         else x
      ) nl)))

and equate_tuples_node (n:node_decl) = match n with
| NodeDecl(p1,id,pl,cd,(p5,loc),Body(p2,EquationList(p3,(p4,el)),be)) ->
      NodeDecl(p1,id,pl,cd,(p5,loc),Body(p2,EquationList(p3,(p4,equate_tuples_eql el)),be))

and equate_tuples_eql (el:equation list) = match el with
| [] -> []
| a::more -> List.append (equate_tuples_eq a) (equate_tuples_eql more)

and equate_tuples_eq (e:equation) = match e with
| AssertEquation(_,_) -> [e]
| KindEquation(_,_,_) -> [e]
| AssignEquation(_,lp,ex) ->
      let leftl = (match lp with
        | LeftPart(_,LeftElemList(_,l,(_,ll))) -> (l::ll)
        | ParenLeftPart(_,LeftElemList(_,l,(_,ll))) -> (l::ll)) in
      let rightl = (match ex with
        | ListExp(_,ExpList(_,ex1,(_,ex1l))) -> (ex1::ex1l)
        | _ -> [ex]) in
      equate_tuples_assigns leftl rightl

and equate_tuples_assigns (left:left_elem list) (right:exp list) =

   if (List.length left)<>(List.length right) then
   begin
      print_int (List.length left);
      print_int (List.length right);
      failwith("tuple size error!")
   end
   else
   List.fold_left2 (fun a l r ->
      match l with
      | StructLeftElem(_,StructFilter(_,LeftElemList(_,le,(_,lel)))) ->
            let exps = (match r with TupleExp(_,ExpList(_,e,(_,el))) -> (e::el) | _ -> [r]) in
            List.append a (equate_tuples_assigns (le::lel) exps)
      | _ -> let eqn = AssignEquation((0,()),LeftPart((0,()),LeftElemList((0,()),l,((0,()),[]))),r) in
         a @ [eqn]
   ) [] left right
;;

(**********************************************************)
(** STEP 9  -  CONSTANT PROPAGATION                      **)
(**********************************************************)

let rec propagate_constants (p:program) : (program*bool) =
   let root = get_root_node p in
   match p with
   | Program(a,b,LusFile(c,(d,e,f,fl,nl))) ->
      let (nl2,flag) = List.fold_left (fun (nlt,f) n ->
         let (nn,fn) = (if n==root then propagate_constants_node_decl n
         else (n,false)) in
         (nlt @ [nn],f||fn)
      ) ([],false) nl in
      (Program(a,b,LusFile(c,(d,e,f,fl,nl2))),flag)

and propagate_constants_node_decl (n:node_decl) : (node_decl*bool) =
   match n with
   | NodeDecl(p,i,il1,il2,loc,Body(p3,EquationList(p4,(p5,el)),be)) ->
      let outputs = get_outputs_ids il2 in
      let (vt,el2,flag1) = List.fold_left (fun (vtt,elt,f1) e ->
         let (vtn,eln,f2) = (match e with
         | AssignEquation(p,lp,ex) ->
            (match lp with
            | LeftPart(p1,LeftElemList(p2,IdLeftElem(p3,id),(p4,[]))) ->
               try let _ = List.assoc id outputs in
                   let (ch1,c2,ce) = evaluate_exp ex vtt in
                   if ch1 then
                      ([],[AssignEquation(p,lp,ce)],true)
                   else
                      ([],[e],false)
               with Not_found ->
                  let (ch1,c1,ce) = evaluate_exp ex vtt in
                  if c1 then (* if we found a constant expression *)
                     ([(id,ce)],[],ch1)
                  else
                     ([],[e],ch1)

            | _ -> failwith("TODO propagate_constants_node_decl: malformed assignment!"))
            | _ -> ([],[e],false)) in
         (vtt @ vtn, elt @ eln,f1||f2)
      ) ([],[],false) el in
      let eqln = EquationList(p4,(p5,el2)) in
      let (el3,flag) = replace_equation_list vt [] eqln in
   (NodeDecl(p,i,il1,il2,loc,Body(p3,el3,be)),flag)

and get_outputs_ids (il:in_param_list) : (var_rep_table) =
   match il with
   | InParamList(p,i,(_,is)) -> List.fold_left (fun nvt x ->
         (match x with
         | InParam(_,c) ->
            (match c with
            | ClockedVarDecl(p,VarDecl(p1,VarList(p2,id,p3),p4)) ->
               (nvt @ [(id,IdExp(p,id))])
            | WhenClockedVarDecl(p,VarDeclList(p1,VarDecl(p2,VarList(p3,id,p4),p5),p6),p7) ->
               (nvt @ [(id,IdExp(p,id))])
            )
         | ConstInParam(_,VarDecl(_,VarList(_,id,_),_)) ->
            (nvt @ [(id,IdExp(p,id))]))
   ) [] (i::is)

let rec flatten_constants (p:program) : (program*bool) =
   let root = get_root_node p in
   match p with
   | Program(a,b,LusFile(c,(d,e,f,fl,nl))) ->
      let (nl2,flag) = List.fold_left (fun (nlt,f) n ->
         let (nn,fn) = (if n==root then flatten_constants_node_decl n
         else (n,false)) in
         (nlt @ [nn],f||fn)
      ) ([],false) nl in
      (Program(a,b,LusFile(c,(d,e,f,fl,nl2))),flag)

and flatten_constants_node_decl (n:node_decl) : (node_decl*bool) =
   match n with
   | NodeDecl(p,i,il1,il2,loc,Body(p3,EquationList(p4,(p5,el)),be)) ->
      let (el2,flag1) = List.fold_left (fun (elt,f1) e ->
         let (eln,f2) = (match e with
         | AssertEquation(p,ex) ->
               let (ex2,f) = flatten_constants_exp ex in
               (AssertEquation(p,ex2),f)
         | AssignEquation(p,lp,ex) ->
               let (ex2,f) = flatten_constants_exp ex in
               (AssignEquation(p,lp,ex2),f)
               (* TODO - handle the kind command case *)
         | _ -> (e,false)) in
         (elt @ [eln],f1||f2)
      ) ([],false) el in
   (NodeDecl(p,i,il1,il2,loc,Body(p3,EquationList(p4,(p5,el2)),be)),flag1)

and flatten_constants_exp (ex:exp) : (exp*bool) =
   match ex with
   | IntExp(p,v) -> (ex,false)
   | RealExp(p,v) -> (ex,false)
   | IdExp(p,v) -> (ex,false)
   | PlusExp(p,et1,et2) ->
         let (e1,f1) = flatten_constants_exp et1 in
         let (e2,f2) = flatten_constants_exp et2 in
         let (e3,f3) = (match (e1,e2) with
         | (IntExp(p,v1),IntExp(_,v2)) -> (IntExp(p,v1+v2),true)
         (* TODO - handle the other real cases, etc. *)
         | _ -> (PlusExp(p,e1,e2),false)) in
         (e3,f1||f2||f3)
   (* TODO - handle the other cases! *)
   | _ -> (ex,false)
;;

let rec propagate_and_flatten_constants (p:program) : program =
   let (p1,f1) = propagate_constants p in
   if f1 then propagate_and_flatten_constants p1
   else p1
;;
