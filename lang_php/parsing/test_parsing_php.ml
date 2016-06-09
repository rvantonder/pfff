(*s: test_parsing_php.ml *)
open Common

module Ast = Ast_php

(*****************************************************************************)
(* Lexing/Parsing *)
(*****************************************************************************)
(*s: test_tokens_php *)
let test_tokens_php file =
  if not (file =~ ".*\\.php")
  then pr2 "warning: seems not a .php file";

  Flag_parsing_php.verbose_lexing := true;
  Flag_parsing_php.verbose_parsing := true;

  let toks = Parse_php.tokens file in
  toks +> List.iter (fun x -> pr2_gen x);
  ()

(*e: test_tokens_php *)
(*s: test_parse_php *)
let test_parse_php xs  =
  let fullxs = Lib_parsing_php.find_source_files_of_dir_or_files xs in

  let dirname_opt, fullxs =
    match xs with
    | [x] when Common2.is_directory x ->
      let skip_list =
        if Sys.file_exists (x ^ "/skip_list.txt")
        then Skip_code.load (x ^ "/skip_list.txt")
        else []
      in
      Some x,  Skip_code.filter_files skip_list x fullxs
    | _ -> None, fullxs
  in

  let stat_list = ref [] in
  (*s: initialize -parse_php regression testing hash *)
  let newscore  = Common2.empty_score () in
  (*e: initialize -parse_php regression testing hash *)

  Common2.check_stack_nbfiles (List.length fullxs);

  fullxs +> Console.progress (fun k -> List.iter (fun file ->
      k ();

      let (_xs, stat) =
        Common.save_excursion Flag_parsing_php.error_recovery true (fun () ->
            Parse_php.parse file
          )
      in
      Common.push stat stat_list;
      (*s: add stat for regression testing in hash *)
      let s = spf "bad = %d" stat.Parse_info.bad in
      if stat.Parse_info.bad = 0
      then Hashtbl.add newscore file (Common2.Ok)
      else Hashtbl.add newscore file (Common2.Pb s)
      ;
      (*e: add stat for regression testing in hash *)
    ));

  Parse_info.print_parsing_stat_list !stat_list;
  (*s: print regression testing results *)
  let score_path = Filename.concat Config_pfff.path "tmp" in
  dirname_opt +> Common.do_option (fun dirname ->
      let dirname = Common.realpath dirname in
      pr2 "--------------------------------";
      pr2 "regression testing  information";
      pr2 "--------------------------------";
      let str = Str.global_replace (Str.regexp "/") "__" dirname in
      Common2.regression_testing newscore
        (Filename.concat score_path
           ("score_parsing__" ^str ^ "php.marshalled"))
    );
  ()
(*e: print regression testing results *)
(*e: test_parse_php *)
(*****************************************************************************)
(* Export *)
(*****************************************************************************)

(*s: test_sexp_php *)
(*x: test_sexp_php *)
(*e: test_sexp_php *)
(*s: test_json_php *)
(*
let test_json_php file =
  let ast = Parse_php.parse_program file in
  let s = Export_ast_php.json_string_of_program ast in
  pr s;
  ()

let test_json_fast_php file =
  let ast = Parse_php.parse_program file in
  let s = Export_ast_php.json_string_of_program_fast ast in
  pr s;
  ()
*)
(*e: test_json_php *)

let test_dump_php file =
  let ast = Parse_php.parse_program file in
  let s = Export_ast_php.ml_pattern_string_of_program ast in
  pr s

(*****************************************************************************)
(* Test *)
(*****************************************************************************)

(** TODO
    1) only one operator at a time.
    3) https://api.github.com/search/repositories?sort=stars&order=desc&q=language:php
*)

let str_of_tok tok = Parse_info.str_of_info tok

let err_msg_of_tok tok =
  Parse_info.token_location_of_info tok
  |> fun info ->
  Printf.sprintf
    "%s:%d:%d" info.Parse_info.file
    info.Parse_info.line
    info.Parse_info.column

let print_list l =
  List.iteri (fun i (x,_,_) ->
      Printf.printf "%d: %s\n%!" i x) l

let print_lists ll =
  List.iter (fun l ->
      print_list l;
      Printf.printf "~~~\n%!") ll

let (!) = Export_ast_php.ml_pattern_string_of_expr

module M = struct
  type symbol = Ast_php.expr * Ast_php.tok option (* parent tok *)
  type bool_exp =
    | Var of symbol
    | And of bool_exp list
    | Or  of bool_exp list

  let to_string ?(z3=false) e =
    let open Printf in
    let rec to_string_exp =
      function
      | Or x -> sprintf "Or(%s)" @@ list_to_string x
      | And x -> sprintf "And(%s)" @@ list_to_string x
      | Var (e,_) ->
        (match e with
         | Ast_php.IdVar (Ast_php.DName(v,_),_) ->
           if z3 then
             sprintf "B('%s')" v
           else
             sprintf "%s" v
         | x -> sprintf "%s" !x)
    and list_to_string (l : bool_exp list) : string =
      List.fold_left (fun (c,acc) x ->
          match c with
          | 0 -> (c+1),(to_string_exp x)
          | _ -> (c+1),(acc^", "^(to_string_exp x))) (0,"") l
      |> snd
    in
    to_string_exp e
end


(** Rewrite directly nested Ors by flattening*)
let bool_exp_of_php_exp exp =
  let open Ast_php in
  let rec aux exp parent_tok =
    match exp with
    | Binary (lhs,(Logical OrBool,op_tok),rhs) ->
      M.Or [aux lhs (Some op_tok); aux rhs (Some op_tok)]
    | Binary (lhs,(Logical AndBool,op_tok),rhs) ->
      M.And [aux lhs (Some op_tok); aux rhs (Some op_tok)]
    | x -> M.Var (x,parent_tok)
  in aux exp None

(** Should get applicative to flatten Or list *)

(*let walk_or exp =
  let open M in
  let open Printf in
  let rec walk exp =
    match exp with
    | Or x ->*)


let flatten_bool_exp exp =
  let open M in
  let open Printf in
  let rec flatten exp =
    printf "Current: %s\n%!" @@ to_string exp;
    match exp with
    | Or l ->
      Or (List.fold_left (fun acc x ->
          match x with
          | Or x -> x@acc
          | Var _ as e -> acc@[e]
          | And _ as e -> acc@[flatten e]) [] l)
    | And l ->
      And (List.fold_left (fun acc x ->
          match x with
          | And x -> x@acc
          | Var _ as e -> acc@[e]
          | Or _ as e -> acc@[flatten e]) [] l)
    | x -> x in
  flatten exp

(*
    match exp with
    | Or ((Or x)::next::rest) ->
      let res = flatten next in
      Or (x@[res]@rest)
    | Or ((Var x)::next::rest) ->
      let res = flatten next in
      Or ([Var x;res]@rest)
    | Or (x::rest) ->
      let res = flatten x in
      Or (res::rest)
    | And ((And x)::next::rest) ->
      let res = flatten next in
      And (x@[res]@rest)
    | And ((Var x)::next::rest) ->
      let res = flatten next in
      And ([Var x;res]@rest)
    | And (x::rest) ->
      let res = flatten x in
      And (res::rest)
    | x -> x
  in flatten exp*)

let simplify exp =
  let open Printf in
  let bexp = bool_exp_of_php_exp exp in
  printf "Before:\n%!";
  printf "%s\n%!" @@ M.to_string ~z3:true bexp;
  let rec fp bexp =
    let bexp' = flatten_bool_exp bexp in
    (*printf "1.%s\n%!" @@ M.to_string bexp;
      printf "2.%s\n%!" @@ M.to_string bexp';*)
    if bexp = bexp' then bexp else fp bexp' in
  let final = fp bexp in
  printf "After:\n%!";
  printf "%s\n%!" @@ M.to_string final;
  ()

(* TODO: if paren on both sides in descend and merge, and both sets to
   curr, or something. see real-test/if-clone-test7 *)
let traverse_expr_tree exp for_op =
  let open Printf in
  let open Ast_php in

  (* curr is the current subexpression. acc is the collection of all *)
  let rec aux exp acc curr =
    let descend_and_merge lhs rhs op_tok = fun () ->
      let extra =
        match lhs,rhs with
        | ParenExpr _,ParenExpr _ ->
          [(!lhs,op_tok,!lhs);(!rhs,op_tok,!rhs)]
        | ParenExpr _,_ -> [(!lhs,op_tok,!lhs)]
        | _,ParenExpr _ -> [(!rhs,op_tok,!rhs)]
        | _ -> [] in
      let lacc,lcurr = traverse_side lhs op_tok acc curr in
      let racc,rcurr = traverse_side rhs op_tok acc curr in
      (lacc@racc@acc),(lcurr@rcurr@extra)
    in
    match exp with
    | Binary (lhs,(Logical OrBool,op_tok),rhs) when for_op = "||" ->
      descend_and_merge lhs rhs op_tok ()
    | Binary (lhs,(Logical AndBool,op_tok),rhs) when for_op = "&&" ->
      descend_and_merge lhs rhs op_tok ()
    | Binary (lhs,(Logical OrLog,op_tok),rhs) when for_op = "or" ->
      descend_and_merge lhs rhs op_tok ()
    | Binary (lhs,(Logical AndLog,op_tok),rhs) when for_op = "and" ->
      descend_and_merge lhs rhs op_tok ()
    | Binary (lhs,(Arith Or,op_tok),rhs) when for_op = "|" ->
      descend_and_merge lhs rhs op_tok ()
    | Binary (lhs,(Arith And,op_tok),rhs) when for_op = "&" ->
      descend_and_merge lhs rhs op_tok ()
    | Binary (lhs,(_,op_tok),rhs) ->
      (* see test4 for why we do this *)
      let lacc,disjoint_lcurr = aux lhs acc [] in
      let racc,disjoint_rcurr = aux rhs acc [] in
      (disjoint_lcurr::disjoint_rcurr::lacc@racc),[]
    | ParenExpr (_,nested_exp,_) ->
      (* *inside* a nested expression essentially means we visit it, but clear
         curr. we merge the result of this visit (curr), and
         anything collected in acc*)
      let acc,curr = aux nested_exp acc [] in
      (curr::acc),[]
    | _ -> acc,curr
  and
    traverse_side exp op_tok acc curr =
    let descend = fun () -> aux exp acc curr in
    match exp with
    | Binary (_,(Logical OrBool,_),_) when for_op = "||" -> descend ()
    | Binary (_,(Logical AndBool,_),_) when for_op = "&&" -> descend ()
    | Binary (_,(Logical OrLog,_),_) when for_op = "or" -> descend ()
    | Binary (_,(Logical AndLog,_),_) when for_op = "and" -> descend ()
    | Binary (_,(Arith Or,_),_) when for_op = "|" -> descend ()
    | Binary (_,(Arith And,_),_) when for_op = "&" -> descend ()
    | ParenExpr _ -> descend ()
    | _ -> acc,(!exp,op_tok,!exp)::curr
  in
  aux exp [] [] |> fun (acc,hd) ->
  (* don't forget to merge the last curr *)
  (hd::acc) |> fun res ->
  (*print_lists res;*)
  res

let test_micro_clones_php file =
  let open Printf in
  let open Ast_php in
  let ast = Parse_php.parse_program file in

  let hooks =
    { Visitor_php.default_visitor with
      Visitor_php.kexpr = (fun (k,_) e ->
          match e with
          | Ast_php.Sc sc -> ()
          | _ -> k e);

      Visitor_php.kstmt = (fun (k,_) s ->
          match s with
          | If (if_tok,(_,cond_exp,_),_,elseifs,_) ->
            simplify cond_exp;
            k s
          | _ -> k s)
    } in
  let visitor = Visitor_php.mk_visitor hooks in
  visitor (Ast.Program ast)

(*****************************************************************************)
(* Misc *)
(*****************************************************************************)
(*s: test_visit_php *)
let test_visit_php file =
  let ast = Parse_php.parse_program file in
  let hooks = { Visitor_php.default_visitor with
                Visitor_php.kinfo = (fun (_k, _) tok ->
                    let s = Parse_info.str_of_info tok in
                    pr2 s;
                  );

                Visitor_php.kexpr = (fun (k, _) e ->
                    match e with
                    | Ast_php.Sc _ ->
                      pr2 "scalar";
                      k e
                    | _ -> k e
                  );
              } in
  let visitor = Visitor_php.mk_visitor hooks in
  visitor (Ast.Program ast)
(*e: test_visit_php *)

let test_unparse_php file =
  let (ast2, _stat) = Parse_php.parse file in
  let tmpfile = Common.new_temp_file "unparse_php" ".php" in
  let s = Unparse_php.string_of_program_with_comments_using_transfo ast2 in
  Common.write_file ~file:tmpfile s;
  let xs = Common2.unix_diff file tmpfile in
  xs +> List.iter pr2;
  ()

let test_pretty_print_php file =
  let _ast = Parse_php.parse_program file in
  raise Todo
(* Pretty_print_php.pretty_print_program ast *)

(* note that pfff can now parse XHP files without calling xhpize *)
let test_parse_xhp_with_xhpize file =
  let pp_cmd = "xhpize" in
  let _ast = Parse_php.parse_program ~pp:(Some pp_cmd) file in
  raise Todo

let test_parse_xdebug_expr s =
  let _e = Parse_php.xdebug_expr_of_string s in
  raise Todo

let test_parse_php_fast file =
  let _ = Parse_php.parse_fast file in
  ()
(*****************************************************************************)
(* Main entry for Arg *)
(*****************************************************************************)
let actions () = [
  (*s: test_parsing_php actions *)
  "-parse_php", "   <file or dir>",
  Common.mk_action_n_arg test_parse_php;
  (*x: test_parsing_php actions *)
  "-visit_php", "   <file>",
  Common.mk_action_1_arg test_visit_php;
  (*x: test_parsing_php actions *)
  (* an alias for -sexp_php *)
(*
    "-json", "   <file> export the AST of file into JSON",
      Common.mk_action_1_arg test_json_php;
    "-json_fast", "   <file> export the AST of file into a compact JSON",
      Common.mk_action_1_arg test_json_fast_php;
*)
  (*x: test_parsing_php actions *)
  (* an alias for -sexp_php *)
  "-dump_php", "   <file>",
  Common.mk_action_1_arg test_dump_php;
  "-micro_clones_php", "   <file>",
  Common.mk_action_1_arg test_micro_clones_php;
  "-dump_php_ml", "   <file>",
  Common.mk_action_1_arg test_dump_php;
  (*x: test_parsing_php actions *)
  (*x: test_parsing_php actions *)
  (*x: test_parsing_php actions *)
  "-tokens_php", "   <file>",
  Common.mk_action_1_arg test_tokens_php;
  (*e: test_parsing_php actions *)

  "-parse_php_fast", "   <file>",
  Common.mk_action_1_arg test_parse_php_fast;
  "-unparse_php", "   <file>",
  Common.mk_action_1_arg test_unparse_php;
  "-pretty_print_php", "   <file>",
  Common.mk_action_1_arg test_pretty_print_php;
  "-parse_xdebug_expr", "   <string>",
  Common.mk_action_1_arg test_parse_xdebug_expr;
  "-parse_xhp_with_xhpize", "   <file>",
  Common.mk_action_1_arg test_parse_xhp_with_xhpize;
]
(*e: test_parsing_php.ml *)
