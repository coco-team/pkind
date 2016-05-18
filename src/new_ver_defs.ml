let nvr_counter = new Counter.counter 

let nvr_prefix = "_NVR_"
  
let nvr_def_prefix = "_NDEF_"

(*nvr_id to def_term, id, type, status *)
let nvr_to_info_hash = (Hashtbl.create 1000:(string,(il_expression*int*lustre_type*bool))Hashtbl.t)

let nvr_to_def_hash = Hashtbl.create 1000 

let get_nvr_def x = Hashtbl.find nvr_to_def_hash x 
(*
  let term_to_nvr_hash = (Hashtbl.create 1000:(il_expression,string)Hashtbl.t*)

let nvr_expr nvr =
  let term,_,_,_ = Hashtbl.find nvr_to_info_hash nvr in
    term 

let mk_nvr_def nvr_id term ty =
  let id_str = string_of_int nvr_id  in
  let m_ty = if ty = L_BOOL then M_BOOL else ty in
  let nvr_str = nvr_prefix^id_str in
  let nvr_def_str = solver#get#define_const_string nvr_str ty in
  let buf = Buffer.create 100 in
  let term_buf = Lus_convert_yc.yc_expr_buffer GENERAL term in
    Hashtbl.add nvr_to_def_hash nvr_str (Buffer.contents term_buf);
  let nvr_def_term_str =  solver#get#define_fun_buffer buf 
    (nvr_def_prefix^id_str) (M_FUNC[M_NAT;m_ty])
    [(solver#get#position_var1,M_NAT)] term_buf in
  let nvr_def_term_str = (Buffer.contents buf) in
  let eq_cmd_str = "(= " ^ nvr_str ^ " (" ^ (nvr_def_prefix^id_str) ^ " 0))\n" in
  let eq_cmd = solver#get#assert_string eq_cmd_str in
    nvr_def_str,nvr_def_term_str,eq_cmd

let setup_nvr term ty =
  let nvr_id = nvr_counter#next in
  let nvr_id_str = nvr_prefix^(string_of_int nvr_id) in 
    Hashtbl.replace nvr_to_info_hash nvr_id_str (term,nvr_id,ty,true) ;
(*    Hashtbl.replace term_to_nvr_hash term nvr_id_str*)
    
   mk_nvr_def nvr_id term ty

let get_all_nvrs () =
  Hashtbl.fold (fun x y z -> x::z) nvr_to_info_hash [] 

