open Common

module Ast = Ast_js
module Flag = Flag_parsing_js

(*****************************************************************************)
(* Subsystem testing *)
(*****************************************************************************)

let test_tokens_js file =
  if not (file =~ ".*\\.js")
  then pr2 "warning: seems not a .js file";

  Flag.verbose_lexing := true;
  Flag.verbose_parsing := true;

  let toks = Parse_js.tokens file in
  toks +> List.iter (fun x -> pr2_gen x);
  ()

let test_parse_js xs  =
  let fullxs =
    Lib_parsing_js.find_source_files_of_dir_or_files ~include_scripts:false xs
  in
  let stat_list = ref [] in

  fullxs +> Console.progress (fun k -> List.iter (fun file ->
      k();

      if file =~ ".*/third_party" || file =~ ".*/wiki/extensions"
      then pr2_once "IGNORING third party directory, bad unicode chars"
      else begin
        let (_xs, stat) =
          Common.save_excursion Flag.error_recovery true (fun () ->
              Common.save_excursion Flag.exn_when_lexical_error false (fun () ->
                  Parse_js.parse file
                ))
        in
        Common.push stat stat_list;
      end
    ));
  Parse_info.print_parsing_stat_list !stat_list;
  ()
(* see also:
 * git clone github.com/facebook/esprima
 * cd esprima/
 * git checkout fb-harmony
 * /home/engshare/third-party-tools/node/bin/node tools/generate-test-fixture.js "foo();"
 * /home/engshare/third-party-tools/node/bin/node tools/generate-test-fixture.js "foo();"
*)
let test_dump_js file =
  let ast = Parse_js.parse_program file in
  let v = Meta_ast_js.vof_program ast in
  let s = Ocaml.string_of_v v in
  pr s

module Boolean : sig
  (* In this module, support 6 kinds of boolean expressions in PHP *)
  type op = And  (* && *)
          | Or   (* || *)
          | LOr  (* or *)
          | LAnd (* and *)

  type 'a t = private
    | Atom of 'a
    | List of op * 'a t list

  val make : op -> 'a t -> 'a t -> 'a t

  module Lang : sig
    val (&&) : 'a t -> 'a t -> 'a t
    val (||) : 'a t -> 'a t -> 'a t
    val (+&&) : 'a t -> 'a t -> 'a t
    val (+||) : 'a t -> 'a t -> 'a t
    val v : 'a -> 'a t
  end
end = struct
  type op = And | Or | LOr | LAnd
  type 'a t =
    | Atom of 'a
    | List of op * 'a t list

  let make op x y =
    match x,y with
    | List (op1,xs), List (op2,ys) when op1 = op && op2 = op ->
      List (op, xs@ys)
    | _,List (op2,ys) when op2 = op ->
      List (op,x::ys)
    | List (op1,xs),_ when op1 = op ->
      List (op,xs@[y])
    | x,y ->
      List (op,[x;y])

  module Lang = struct
    let (&&) op1 op2 = make And op1 op2
    let (||) op1 op2 = make Or op1 op2
    let (+&&) op1 op2 = make LAnd op1 op2
    let (+||) op1 op2 = make LOr op1 op2
    let v x = Atom x
  end
end

open Boolean

(** No Unparse, and so no nice to_string for Ast_js.expr *)
type s = Ast_js.expr * Ast_js.tok option

let op_to_string = function
  | And -> "And"
  | Or -> "Or"
  | LOr -> "LOr"
  | LAnd -> "LAnd"

let string_of_any ast =
  ast +> Meta_ast_js.vof_any +> Ocaml.string_of_v

let string_of_expr x = string_of_any (Ast_js.Expr x)

let to_string exp =
  let open Printf in
  let (!) = string_of_expr in
  let rec exp_to_string =
    function
    | Atom (x,_) -> !x
    | List (op,l) -> sprintf "%s(%s)" (op_to_string op) (list_to_string l)
  and
    list_to_string (l : s t list) : string =
    List.fold_left (fun (c,acc) x ->
        match c with
        | 0 -> (c+1),(exp_to_string x)
        | _ -> (c+1),(acc^", "^(exp_to_string x))) (0,"") l |> snd
  in
  exp_to_string exp

(** create a Boolean.t expression from an AST expression *)
let bool_exp_of_php_exp exp : s Boolean.t =
  let open Ast in
  let rec aux exp parent_tok : s Boolean.t =
    match exp with
    | B (lhs,(B_and,op_tok),rhs) ->
      Boolean.Lang.(aux lhs (Some op_tok) || aux rhs (Some op_tok))
    | B (lhs,(B_or,op_tok),rhs) ->
      Boolean.Lang.(aux lhs (Some op_tok) && aux rhs (Some op_tok))
    | B (lhs,(B_bitand,op_tok),rhs) ->
      Boolean.Lang.(aux lhs (Some op_tok) +&& aux rhs (Some op_tok))
    | B (lhs,(B_bitor,op_tok),rhs) ->
      Boolean.Lang.(aux lhs (Some op_tok) +|| aux rhs (Some op_tok))
    | Paren (_,exp,_) -> aux exp parent_tok
    | x -> Boolean.Lang.v (x, parent_tok)
  in aux exp None

let str_of_tok tok = Parse_info.str_of_info tok

let err_msg_of_tok tok =
  Parse_info.token_location_of_info tok
  |> fun info ->
  Printf.sprintf
    "%s:%d:%d" info.Parse_info.file
    info.Parse_info.line
    info.Parse_info.column

(** Use the first Atom in the duplicate expression. *)
let emit_error expr =
  let open Printf in
  let res  =
    let rec aux = function
      | Atom x -> Some x
      | List (_,hd::_) -> aux hd
      | _ -> None
    in aux expr in
  match res with
  | Some (expr,Some op_tok) ->
    let err_msg = err_msg_of_tok op_tok in
    printf "%s:%s:%s\n%!" (str_of_tok op_tok) err_msg
      (string_of_expr expr)
  | _ -> ()

(** Compare expressions syntactically *)
let compare exp1 exp2 =
  String.compare (to_string exp1) (to_string exp2)

let dedup l =
  List.fold_left (fun acc x ->
      if List.exists (fun y -> compare x y = 0) acc
      then (emit_error x; acc) else x::acc) [] l |> List.rev

(** Helper function to reconstruct Boolean.t *)
let boolean_of_list op (l : s Boolean.t list) : s Boolean.t =
  let rec aux l =
    match l with
    | [Atom x] -> Lang.v x
    | x::y::[] -> make op x y
    | [List (op,hd::tl)] -> make op hd (aux tl)
    | hd::tl -> make op hd (aux tl)
    | [] -> failwith "Error: Cannot construct a Boolean from an empty list."
  in aux l

(** Rewrite rule *)
let rule_dedup (exp : s Boolean.t) : s Boolean.t =
  match exp with
  | List (op,l) -> dedup l |> boolean_of_list op
  | Atom x -> Lang.v x

(** Bottom-up exression rewriter *)
let bur_map f (exp : s Boolean.t) : s Boolean.t =
  let rec aux exp =
    match exp with
    | List (op,l) ->
      let e = List.map aux l |> boolean_of_list op in
      f e
    | x -> f x in
  aux exp

let simplify ?(verbose=false) exp =
  let open Printf in
  let exp' = bool_exp_of_php_exp exp in
  let exp'' = bur_map rule_dedup exp' in
  if verbose then
    let s' = to_string exp' in
    let s'' = to_string exp'' in
    if s' <> s'' then
      (printf "\n[+] Exp:\n\n\t%s\n" s';
       printf "\ncan be simplified:\n\n\t%s\n" s'')
    else
      printf "\n[+] Exp:\n\n\t%s\n" s'

let test_micro_clones_js file =
  let open Ast_js in
  let ast = Parse_js.parse_program file in

  let visitor = Visitor_js.mk_visitor {
      Visitor_js.default_visitor with

      Visitor_js.kstmt = (fun (k,_) s ->
          match s with
          | If (_,(_,cond_exp,_),_,(_)) ->
            List.iter simplify [cond_exp];
            k s
          | _ -> k s)
    } in
  visitor (Ast.Program ast)

(*
let test_json_js file =
  let ast = Parse_js.parse_program file in
  let s = Export_ast_js.string_json_of_program ast in
  pr s;
  ()
*)
(*
let test_esprima file =
  let json = Json_in.load_json file in
  let ast = Esprima.convert json in
  let v = Meta_ast_js.vof_program ast in
  let s = Ocaml.string_of_v v in
  pr s
*)

(*****************************************************************************)
(* Main entry for Arg *)
(*****************************************************************************)

let actions () = [
  "-tokens_js", "   <file>",
  Common.mk_action_1_arg test_tokens_js;
  "-parse_js", "   <file or dir>",
  Common.mk_action_n_arg test_parse_js;
  "-dump_js", "   <file>",
  Common.mk_action_1_arg test_dump_js;
  "-micro_clones_js", "    <file>",
  Common.mk_action_1_arg test_micro_clones_js;

(*
  "-json_js", "   <file> export the AST of file into JSON",
  Common.mk_action_1_arg test_json_js;
  "-parse_esprima_json", " <file> ",
  Common.mk_action_1_arg test_esprima;
*)
]
