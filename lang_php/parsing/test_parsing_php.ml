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

let print_lists ll =
  List.iter (fun l ->
      List.iter (fun (x,_) ->
          Printf.printf "%s\n%!" x) l;
      Printf.printf "~~~\n%!") ll

let traverse_expr_tree exp =
  let open Printf in
  let open Ast_php in
  let rec aux exp acc curr =
    match exp with
    | Binary (lhs,(op,op_tok),rhs) ->
      let lacc,lcurr = aux lhs acc curr in
      let racc,rcurr = aux rhs acc curr in
      (* merge left and right accs and currs *)
      (lacc @ racc),(lcurr @ rcurr)
    | ParenExpr (_,nested_exp,_) ->
      (* start a new curr when we enter a parenth *)
      let res_acc,res_curr = aux nested_exp acc [] in
      (* merge parenth, and return previous curr *)
      res_curr::res_acc,curr
    | IdVar (DName (v,v_tok),_) ->
      acc,((v,v_tok)::curr)
    | _ -> acc,curr
  in
  aux exp [] [] |> fun (acc,hd) ->
  (* don't forget to merge the last curr *)
  (hd::acc) |> fun res ->
  print_lists res;
  res

let err_msg_of_tok tok =
  Parse_info.token_location_of_info tok
  |> fun info ->
  Printf.sprintf
    "%s:%d:%d" info.Parse_info.file
    info.Parse_info.line
    info.Parse_info.column

let check_dups ll =
  let open Printf in
  List.iter (fun l ->
      List.map fst l |> fun l' ->
      List.sort_uniq String.compare l' |> fun l'' ->
      let l',ll' =
        if List.length l' > List.length l''
        then (List.tl l'),l''
        else if List.length l' < List.length l''
        then l',(List.tl l'')
        else [],[] in
      match (l',ll') with
      | [],[] -> ()
      | l',l'' ->
        let dup_var =
          List.fold_left2 (fun acc x y ->
              if x <> y then x else acc) "" l' l'' in
        let (_,dup_tok) = List.find (fun (x,y) -> x = dup_var) l in
        let err_msg = err_msg_of_tok dup_tok in
        printf "%s\n%!" err_msg) ll

let test_micro_clones_php file =
  let open Printf in
  let open Ast_php in
  let ast = Parse_php.parse_program file in
  (*let (!) = Parse_info.str_of_info in (* tok to string *)*)


  let hooks =
    { Visitor_php.default_visitor with
      Visitor_php.kexpr = (fun (k,_) e ->
          match e with
          | Ast_php.Sc sc -> ()
          | _ -> k e);

      Visitor_php.kstmt = (fun (k,_) s ->
          match s with
          | If (if_tok,(_,cond_exp,_),_,_,_) ->
            (*check_cond if_tok exp;*)
            let res = traverse_expr_tree cond_exp in check_dups res;
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
