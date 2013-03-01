
type type_clang = 
  | Builtin of string
  | Typename of string

  (* pointer or array *)
  | Pointer of type_clang
  | Function of type_clang

  | StructName of string
  | UnionName of string
  | EnumName of string

  | AnonStuff
  | TypeofStuff

  | Other of Parser_clang.token list

val builtin_types: string Common.hashset

val extract_type_of_sexp: 
  Ast_clang.loc -> Ast_clang.sexp -> type_clang

val extract_type_of_string: 
  Ast_clang.loc -> string -> type_clang
