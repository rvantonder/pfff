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

let traverse_expr_tree exp for_op =
  let open Printf in
  let open Ast_php in
  let (!) = Export_ast_php.ml_pattern_string_of_expr in
  let rec aux exp acc curr =
    match exp with
    | Binary (lhs,(Logical OrBool,op_tok),rhs) ->
      (*| Binary (lhs,(Logical OrBool,op_tok),rhs) ->*)
      (*printf "lhs: %s " !lhs;
        printf "tok: %s " @@ str_of_tok op_tok;
        printf "rhs: %s\n" !rhs;*)
      let lacc,lcurr = aux lhs acc curr in
      let racc,rcurr = aux rhs acc curr in
      let curr = (!lhs,op_tok,!lhs)::(!rhs,op_tok,!rhs)::curr in
      (lacc@racc),(lcurr@rcurr@curr)
    | Binary (lhs,(_,op_tok),rhs) ->
      (*printf "lhs: %s " !lhs;
        printf "tok: %s " @@ str_of_tok op_tok;
        printf "rhs: %s\n" !rhs;*)
      let lacc,lcurr = aux lhs acc curr in
      let racc,rcurr = aux rhs acc curr in
      (lcurr::rcurr::lacc@racc@acc),[]
    | ParenExpr (_,nested_exp,_) ->
      (* start a new curr when we enter a parenth *)
      let res_acc,res_curr = aux nested_exp acc [] in
      (* merge parenth, and return previous curr *)
      res_curr::res_acc,curr
    | _ -> acc,curr
  in
  aux exp [] [] |> fun (acc,hd) ->
  (* don't forget to merge the last curr *)
  (hd::acc) |> fun res ->
  (*print_lists res;*)
  res

let check_dups ll =
  let open Printf in
  List.iter (fun l ->
      List.sort (fun (x,y,z) (x',y',z') -> String.compare x x') l
      |> fun l'' ->
      (*printf "Debug: find dups in\n%!";
        print_list l'';
        printf "done\n%!";*)
      let rec find_dups lll acc = match lll with
        | [] | _::[] -> acc
        | ((a,_,_) as elt)::(b,_,_)::[] ->
          (*printf "Comparing:\n%!";
            printf "a: %s\n%!" a;
            printf "b: %s\n%!" b;*)
          if a = b then elt::acc else acc
        | ((a,_,_) as elt)::((b,_,_)::_ as rest) ->
          (*printf "Comparing:\n%!";
            printf "a: %s\n%!" a;
            printf "b: %s\n%!" b;*)
          if a = b then
            ((*printf "Yes, %s = %s\n%!" a b;*)
              find_dups rest (elt::acc))
          else find_dups rest acc in
      let dups = find_dups l'' [] in
      match dups with
      | [] -> ()
      | l -> List.iter (fun (x,dup_tok,z) ->
          let err_msg = err_msg_of_tok dup_tok in
          printf "%s\n%!" err_msg)
          dups) ll

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
          | If (if_tok,(_,cond_exp,_),_,_,_) ->
            traverse_expr_tree cond_exp "&&" |> check_dups;
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
