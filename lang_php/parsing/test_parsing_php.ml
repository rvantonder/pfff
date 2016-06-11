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
  let open Printf in
  let rec aux exp parent_tok =
    match exp with
    | Binary (lhs,(Logical OrBool,op_tok),rhs) ->
      M.Or [aux lhs (Some op_tok); aux rhs (Some op_tok)]
    | Binary (lhs,(Logical AndBool,op_tok),rhs) ->
      M.And [aux lhs (Some op_tok); aux rhs (Some op_tok)]
    | ParenExpr (_,exp,_) as x ->
      (match parent_tok with
       | Some tok when str_of_tok tok = "||" ->
         M.Or [aux exp parent_tok]
       | Some tok when str_of_tok tok = "&&" ->
         M.And [aux exp parent_tok]
       | _ -> M.Var (x,parent_tok))
    | x -> M.Var (x,parent_tok)
  in aux exp None

(** Should get applicative to flatten Or list *)

(** Or(Or(a,a),a) -> Or(a,a,a) *)
(*
  let flatten list =
    let rec aux acc = function
      | [] -> acc
      | One x :: t -> aux (x :: acc) t
      | Many l :: t -> aux (aux acc l) t in
    List.rev (aux [] list);;
*)
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

let rule_dedup (dedup_exps : M.bool_exp list) =
  let (!) = M.to_string in
  List.sort (fun exp1 exp2 -> String.compare !exp1 !exp2) dedup_exps
  |> fun l ->
  let rec dedup = function
    | x1 :: (x2 :: _ as rest) -> if (M.to_string x1) = (M.to_string x2) then dedup rest
      else x1::dedup rest
    | x -> x in
  let d = dedup l in d

(** Or([And(b,c)]) -> And(b,c)
    Or([Var x]) -> Var x*)
let rule_simple =
  let open M in
  let open Printf in
  function
  | Or (x::[]) -> x
  | And (x::[]) -> x
  | x -> x

(**
   Descend down list of parent, perform deduplication, then simplify.
   If the parent can be simplified after these rewrites, do it. One
   pass should be enough. *)
let rewrite exp =
  let open M in
  let open Printf in
  let rec aux exp =
    match exp with
    | And x -> And (List.map aux x
                    |> rule_dedup
                    |> List.map rule_simple)
               |> rule_simple
    | Or x ->
      Or (List.map aux x
          |> rule_dedup
          |> List.map rule_simple)
      |> rule_simple
    | x -> x in
  aux exp

let simplify exp =
  let open Printf in
  let bexp = bool_exp_of_php_exp exp in
  printf "Before:\n%!";
  printf "%s\n%!" @@ M.to_string ~z3:true bexp;
  let rec fp bexp =
    let bexp' = flatten_bool_exp bexp in
    printf "1.%s\n%!" @@ M.to_string bexp;
    printf "2.%s\n%!" @@ M.to_string bexp';
    if bexp = bexp' then bexp else fp bexp' in
  let flat_exp = fp bexp in
  printf "After:\n%!";
  printf "%s\n%!" @@ M.to_string flat_exp;
  let final' = rewrite flat_exp in
  printf "FINAL:\n%!";
  printf "%s\n%!" @@ M.to_string final';
  ()

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
