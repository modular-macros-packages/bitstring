(*
 * Copyright (c) 2016 Xavier R. Guérin <xguerin@users.noreply.github.com>
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *)

open Ppxlib
open Printf
open Ast_builder.Default

(* Exception *)

let location_exn ~loc msg =
  Location.raise_errorf ~loc "%s" msg
;;

(* Type definition *)

module Entity = struct
  type t = {
    txt : string;
    exp : Parsetree.expression;
    pat : Parsetree.pattern
  }

  let mksym =
    let i = ref 1000 in
    fun name ->
      incr i; let i = !i in
      sprintf "__ppxbitstring_%s_%d" name i
  ;;

  let make ~loc v =
    let txt = mksym v in
    { txt; exp = evar ~loc txt; pat = pvar ~loc txt }
end

module Context = struct
  type t = {
    dat : Entity.t;
    off : Entity.t;
    len : Entity.t
  }

  let make ~loc =
    let dat = Entity.make ~loc "dat"
    and off = Entity.make ~loc "off"
    and len = Entity.make ~loc "len"
    in
    { dat; off; len }

  let next ~loc t =
    let off = Entity.make ~loc "off"
    and len = Entity.make ~loc "len"
    in
    { t with off; len }
end

module Type = struct
  type t =
    | Int
    | String
    | Bitstring
end

module Sign = struct
  type t =
    | Signed
    | Unsigned

  let to_string = function
    | Signed -> "signed"
    | Unsigned -> "unsigned"
end

module Endian = struct
  type t =
    | Little
    | Big
    | Native
    | Referred of Parsetree.expression

  let to_string = function
    | Little -> "le"
    | Big -> "be"
    | Native -> "ne"
    | Referred _ -> "ee"
end

module Qualifiers = struct
  type t = {
    value_type     : Type.t option;
    sign           : Sign.t option;
    endian         : Endian.t option;
    check          : Parsetree.expression option;
    bind           : Parsetree.expression option;
    map            : Parsetree.expression option;
    save_offset_to : Parsetree.expression option;
    offset         : Parsetree.expression option;
  }

  let empty = {
    value_type     = None;
    sign           = None;
    endian         = None;
    check          = None;
    bind           = None;
    map            = None;
    save_offset_to = None;
    offset         = None;
  }

  let default = {
    value_type     = Some Type.Int;
    sign           = Some Sign.Unsigned;
    endian         = Some Endian.Big;
    check          = None;
    bind           = None;
    map            = None;
    save_offset_to = None;
    offset         = None;
  }

  let set_value_type_default q =
    match q.value_type with
    | None  -> { q with value_type = Some Type.Int }
    | _     -> q
  ;;

  let set_sign_default q =
    match q.sign with
    | None  -> { q with sign = Some Sign.Unsigned }
    | _     -> q
  ;;

  let set_endian_default q =
    match q.endian with
    | None  -> { q with endian = Some Endian.Big }
    | _     -> q
  ;;

  let set_defaults v =
    v
    |> set_value_type_default
    |> set_sign_default
    |> set_endian_default
  ;;
end

module MatchField = struct
  type bitlen =
    (Parsetree.expression * int option)
  ;;

  type tuple = {
    pat : Parsetree.pattern;
    len : bitlen;
    qls : Qualifiers.t;
    opt : bool
  }

  type t =
    | Any of Parsetree.pattern
    | Tuple of tuple
  ;;

  let as_evar v = 
    match v.pat with
    | {ppat_desc = Ppat_var(v); _} -> evar ~loc:v.loc v.txt
    | {ppat_loc; _} -> location_exn ~loc:ppat_loc "Pattern is not a variable"
end

(* Helper functions *)

let split_string ~on s =
  Str.split (Str.regexp on) s
;;

let option_bind opt f =
  match opt with
  | None   -> None
  | Some v -> f v
;;

let rec process_expr_loc ~loc expr =
  match expr with
  | { pexp_desc = Pexp_ident(ident); _ } ->
    let lident = Loc.make ~loc ident.txt in
    { expr with pexp_desc = Pexp_ident(lident); pexp_loc = loc }
  | { pexp_desc = Pexp_tuple(ops); _ } ->
    let fld = List.fold_left
        (fun acc exp -> acc @ [ process_expr_loc ~loc exp ])
        []
        ops
    in { expr with pexp_desc = Pexp_tuple(fld); pexp_loc = loc }
  | { pexp_desc = Pexp_construct(ident, ops); _ } ->
    let lident = Loc.make ident.txt ~loc in
    let lops = begin match ops with
      | Some o -> Some (process_expr_loc ~loc o)
      | None    -> None
    end in
    { expr with pexp_desc = Pexp_construct(lident, lops); pexp_loc = loc }
  | { pexp_desc = Pexp_apply(ident, ops); _ } ->
    let lident = process_expr_loc ~loc ident in
    let fld = List.fold_left
        (fun acc (lbl, exp) -> acc @ [ (lbl, (process_expr_loc ~loc exp)) ])
        []
        ops
    in { expr with pexp_desc = Pexp_apply(lident, fld); pexp_loc = loc }
  | { pexp_desc = Pexp_function(params, constraint_, Pfunction_body exp); _ } ->
     let lparams = List.map (process_param_loc ~loc) params in
     let lexp = process_expr_loc ~loc exp in
     { expr with pexp_desc = Pexp_function (lparams, constraint_, Pfunction_body lexp); pexp_loc = loc }
  | _ ->
    { expr with pexp_loc = loc }

and process_param_loc ~loc (param : function_param) = match param.pparam_desc with
  | Pparam_val (ident, ops, { ppat_desc = Ppat_var pid; ppat_attributes; _ }) -> (
    let lpid = Loc.make pid.txt ~loc in
    let lpat = { ppat_desc = Ppat_var lpid; ppat_loc = loc; ppat_attributes; ppat_loc_stack = [] } in
    let lops = begin match ops with
      | Some o -> Some (process_expr_loc ~loc o)
      | None   -> None
    end in
    { param with pparam_desc = Pparam_val (ident, lops, lpat) }
  )
  | _ -> param
;;

let parse_expr expr =
  try
    Parse.expression (Lexing.from_string expr.txt)
    |> process_expr_loc ~loc:expr.loc
  with
    _ -> location_exn ~loc:expr.loc ("Parse expression error: '" ^ expr.txt ^ "'")
;;

let process_pat_loc ~loc pat =
  match pat with
  | { ppat_desc = Ppat_var(ident); ppat_loc; ppat_attributes; _ } ->
    let lident = Loc.make ident.txt ~loc in
    { ppat_desc = Ppat_var(lident); ppat_loc = loc; ppat_attributes; ppat_loc_stack = [] }
  | _ ->
    { pat with ppat_loc = loc }
;;

let parse_pattern pat =
  try
    Parse.pattern (Lexing.from_string pat.txt)
    |> process_pat_loc ~loc:pat.loc
  with
    _ -> location_exn ~loc:pat.loc ("Parse pattern error: '" ^ pat.txt ^ "'")
;;

(* Location parser and splitter *)

let find_loc_boundaries ~loc last rem =
  let open Location in
  let { loc_start; loc_end; loc_ghost } = loc in
  let xtr_lines = List.length rem in
  let xtr_char = List.fold_left (+) xtr_lines rem in
  let ne = { loc_start with
             pos_lnum = loc_start.pos_lnum + xtr_lines;
             pos_bol  = loc_start.pos_bol + xtr_char;
             pos_cnum = loc_start.pos_cnum + xtr_char + last
           }
  and ns = if xtr_lines = 0
    then { loc_start with
           pos_cnum = loc_start.pos_cnum + xtr_char + last + 1
         }
    else { loc_start with
           pos_lnum = loc_start.pos_lnum + xtr_lines;
           pos_bol  = loc_start.pos_bol + xtr_char;
           pos_cnum = loc_start.pos_cnum + xtr_char
         } in
  let tloc = { loc_start; loc_end = ne; loc_ghost } in
  let nloc = { loc_start = ns; loc_end; loc_ghost } in
  (tloc, nloc)
;;

let rec split_loc_rec ~loc = function
  | [] -> []
  | hd :: tl ->
    let line_list = split_string ~on:"\n" hd
                    |> List.rev
                    |> List.map String.length in
    begin
      match line_list with
      | [] -> []
      | last::rem ->
        let (tloc, nloc) = find_loc_boundaries ~loc last rem in
        [ tloc ] @ (split_loc_rec ~loc:nloc tl)
    end
;;

let split_loc ~loc lst =
  split_loc_rec ~loc lst
  |> List.map2 (fun e loc -> Loc.make (String.trim e) ~loc) lst
;;

(* Processing qualifiers *)

let check_map_functor sub =
  match sub with
  | [%expr (fun [%p? _] -> [%e? _])]  -> Some (sub)
  | _                                 -> None
;;

let process_qual state qual =
  let open Qualifiers in
  let loc = qual.pexp_loc in
  match qual with
  | [%expr int] ->
    begin match state.value_type with
      | Some v -> location_exn ~loc "Value type redefined"
      | None -> { state with value_type = Some Type.Int }
    end
  | [%expr string] ->
    begin match state.value_type with
      | Some v -> location_exn ~loc "Value type redefined"
      | None -> { state with value_type = Some Type.String }
    end
  | [%expr bitstring] ->
    begin match state.value_type with
      | Some v -> location_exn ~loc "Value type redefined"
      | None -> { state with value_type = Some Type.Bitstring }
    end
  | [%expr signed] ->
    begin match state.sign with
      | Some v -> location_exn ~loc "Signedness redefined"
      | None -> { state with sign = Some Sign.Signed }
    end
  | [%expr unsigned] ->
    begin match state.sign with
      | Some v -> location_exn ~loc "Signedness redefined"
      | None -> { state with sign = Some Sign.Unsigned }
    end
  | [%expr littleendian] ->
    begin match state.endian with
      | Some v -> location_exn ~loc "Endianness redefined"
      | None -> { state with endian = Some Endian.Little }
    end
  | [%expr bigendian] ->
    begin match state.endian with
      | Some v -> location_exn ~loc "Endianness redefined"
      | None -> { state with endian = Some Endian.Big }
    end
  | [%expr nativeendian] ->
    begin match state.endian with
      | Some v -> location_exn ~loc "Endianness redefined"
      | None -> { state with endian = Some Endian.Native }
    end
  | [%expr endian [%e? sub]] ->
    begin match state.endian with
      | Some v -> location_exn ~loc "Endianness redefined"
      | None -> { state with endian = Some (Endian.Referred sub) }
    end
  | [%expr bind [%e? sub]] ->
    begin match state.bind, state.map with
      | Some b, None   -> location_exn ~loc "Bind expression redefined"
      | None,   Some m -> location_exn ~loc "Map expression already defined"
      | Some b, Some m -> location_exn ~loc "Inconsistent internal state"
      | None,   None   -> { state with bind = Some sub }
    end
  | [%expr map [%e? sub]] ->
    begin match state.bind, state.map with
      | Some b, None   -> location_exn ~loc "Bind expression already defined"
      | None,   Some m -> location_exn ~loc "Map expression redefined"
      | Some b, Some m -> location_exn ~loc "Inconsistent internal state"
      | None,   None   -> begin
          match check_map_functor sub with
          | Some sub  -> { state with map = Some sub }
          | None      -> location_exn ~loc "Invalid map functor"
        end
    end
  | [%expr check [%e? sub]] ->
    begin match state.check with
      | Some v -> location_exn ~loc "Check expression redefined"
      | None -> { state with check = Some sub }
    end
  | [%expr save_offset_to [%e? sub]] ->
    begin match state.save_offset_to with
      | Some v -> location_exn ~loc "Save offset expression redefined"
      | None -> { state with save_offset_to = Some sub }
    end
  | [%expr offset [%e? sub]] ->
    begin match state.offset with
      | Some v -> location_exn ~loc "Offset expression redefined"
      | None -> { state with offset = Some sub }
    end
  | _ ->
    location_exn ~loc "Invalid qualifier"
;;

let parse_quals quals =
  let expr = parse_expr quals in
  let rec process_quals state = function
    | [] -> state
    | hd :: tl -> process_quals (process_qual state hd) tl
  in match expr with
  (* single named qualifiers *)
  | { pexp_desc = Pexp_ident (_); _ } ->
    process_qual Qualifiers.empty expr
  (* single functional qualifiers *)
  | { pexp_desc = Pexp_apply (_, _); _ } ->
    process_qual Qualifiers.empty expr
  (* multiple qualifiers *)
  | { pexp_desc = Pexp_tuple (e); _ } ->
    process_quals Qualifiers.empty e
  (* Unrecognized expression *)
  | expr ->
    location_exn ~loc:expr.pexp_loc "Invalid qualifiers list"
;;

(* Processing expression *)

let rec evaluate_expr = function
  | [%expr [%e? lhs] + [%e? rhs]] ->
    begin match evaluate_expr lhs, evaluate_expr rhs with
      | Some l, Some r -> Some (l + r)
      | _ -> None
    end
  | [%expr [%e? lhs] - [%e? rhs]] ->
    begin match evaluate_expr lhs, evaluate_expr rhs with
      | Some l, Some r -> Some (l - r)
      | _ -> None
    end
  | [%expr [%e? lhs] * [%e? rhs]] ->
    begin match evaluate_expr lhs, evaluate_expr rhs with
      | Some l, Some r -> Some (l * r)
      | _ -> None
    end
  | [%expr [%e? lhs] / [%e? rhs]] ->
    begin match evaluate_expr lhs, evaluate_expr rhs with
      | Some l, Some r -> Some (l / r)
      | _ -> None
    end
  | [%expr [%e? lhs] land [%e? rhs]] ->
    begin match evaluate_expr lhs, evaluate_expr rhs with
      | Some l, Some r -> Some (l land r)
      | _ -> None
    end
  | [%expr [%e? lhs] lor [%e? rhs]] ->
    begin match evaluate_expr lhs, evaluate_expr rhs with
      | Some l, Some r -> Some (l lor r)
      | _ -> None
    end
  | [%expr [%e? lhs] lxor [%e? rhs]] ->
    begin match evaluate_expr lhs, evaluate_expr rhs with
      | Some l, Some r -> Some (l lxor r)
      | _ -> None
    end
  | [%expr [%e? lhs] lsr [%e? rhs]] ->
    begin match evaluate_expr lhs, evaluate_expr rhs with
      | Some l, Some r -> Some (l lsr r)
      | _ -> None
    end
  | [%expr [%e? lhs] asr [%e? rhs]] ->
    begin match evaluate_expr lhs, evaluate_expr rhs with
      | Some l, Some r -> Some (l asr r)
      | _ -> None
    end
  | [%expr [%e? lhs] mod [%e? rhs]] ->
    begin match evaluate_expr lhs, evaluate_expr rhs with
      | Some l, Some r -> Some (l mod r)
      | _ -> None
    end
  | { pexp_desc = Pexp_constant (const); _ } ->
    begin match const with
      | Pconst_integer(i, _) -> Some (int_of_string i)
      | _ -> None
    end
  | _ -> None
;;

(* Parsing fields *)

let parse_match_fields str =
  let open MatchField in
  split_string ~on:":" str.txt
  |> split_loc ~loc:str.loc
  |> function
  | [ { txt = "_" ; loc } as pat ] ->
    MatchField.Any (parse_pattern pat)
  | [ spat; slen ] ->
    let qls = Qualifiers.default
    and eln = parse_expr slen
    and pat = parse_pattern spat
    and opt = false in
    let len = (eln, evaluate_expr eln) in
    MatchField.Tuple { pat; len; qls; opt }
  | [ spat; slen; sqls ] ->
    let qls = Qualifiers.set_defaults (parse_quals sqls)
    and eln = parse_expr slen
    and pat = parse_pattern spat
    and opt = false in
    let len = (eln, evaluate_expr eln) in
    MatchField.Tuple { pat; len; qls; opt }
  | [ stmt ] ->
    let pat_str = stmt.txt in
    location_exn ~loc:stmt.loc ("Invalid statement: '" ^ pat_str ^ "'")
  | _ ->
    location_exn ~loc:str.loc "Invalid number of fields in statement"
;;

(*
 * Some operators like the subtype cast operator (:>) can throw off the parser.
 * The function below resolve these ambiguities on a case-by-case basis.
 *)
let stitch_ambiguous_operators lst =
  let fn e = function
    | [] -> [ e ]
    | hd :: tl when hd = "" || e == "" -> e :: hd :: tl
    | hd :: tl when Str.first_chars hd 1 = ">" -> (e ^ ":" ^ hd) :: tl
    | l -> e :: l
  in
  List.fold_right fn lst []

let parse_const_fields str =
  let open Qualifiers in
  split_string ~on:":" str.txt
  |> stitch_ambiguous_operators
  |> split_loc ~loc:str.loc
  |> function
  | [ vl; len ] ->
    (parse_expr vl, Some (parse_expr len), Some Qualifiers.default)
  | [ vl; len; quals ] ->
    let q = Qualifiers.set_defaults (parse_quals quals) in
    begin match q.bind, q.map, q.check, q.save_offset_to with
      | Some _, _, _, _ ->
        location_exn ~loc:str.loc "Bind meaningless in constructor"
      | _, Some _, _, _ ->
        location_exn ~loc:str.loc "Map meaningless in constructor"
      | _, _, Some _, _ ->
        location_exn ~loc:str.loc "Check meaningless in constructor"
      | _, _, _, Some _ ->
        location_exn ~loc:str.loc "Saving offset meaningless in constructor"
      | None, None, None, None ->
        (parse_expr vl, Some (parse_expr len), Some (q))
    end
  | [ stmt ] ->
    let pat_str = stmt.txt in
    location_exn ~loc:stmt.loc ("Invalid statement: '" ^ pat_str ^ "'")
  | _ ->
    location_exn ~loc:str.loc "Invalid number of fields in statement"
;;

(* Match generators *)

let check_field_len ~loc fld =
  let (l, v) = fld.MatchField.len
  in
  match v, fld.MatchField.qls.Qualifiers.value_type with
  | Some (n), Some (Type.String) ->
    if n < -1 || (n > 0 && (n mod 8) <> 0) then
      location_exn ~loc "Length of string must be > 0 and multiple of 8, or the special value -1"
    else Some n
  | Some (n), Some (Type.Bitstring) ->
    if n < -1 then location_exn ~loc "Length of bitstring must be >= 0 or the special value -1"
    else Some n
  | Some (n), Some (Type.Int) ->
    if n < 1 || n > 64 then location_exn ~loc "Length of int field must be [1..64]"
    else Some n
  | None, Some (_) -> None
  | _, None -> location_exn ~loc "No type to check"
;;

let get_inttype ~loc ~fastpath = function
  | v when v > 8  && v <= 16 -> if fastpath then "int16" else "int"
  | v when v > 16 && v <= 31 -> if fastpath then "int32" else "int"
  | v when v = 32 -> "int32"
  | v when v > 32 && v <= 64 -> "int64"
  | _ -> location_exn ~loc "Invalid integer size"

let gen_int_extractor_static ~loc nxt size sign endian =
  let edat = nxt.Context.dat.Entity.exp
  and eoff = nxt.Context.off.Entity.exp
  in
  let sn = Sign.to_string sign
  and ft = get_inttype ~loc ~fastpath:true size
  and en = Endian.to_string endian in
  let fp = sprintf "Bitstring.extract_fastpath_%s_%s_%s" ft en sn
  in
    [%expr
      [%e evar ~loc fp] [%e edat] ([%e eoff] lsr 3)]
      [@metaloc loc]
;;

let gen_int_extractor_dynamic ~loc nxt size sign endian =
  let edat = nxt.Context.dat.Entity.exp
  and eoff = nxt.Context.off.Entity.exp
  and elen = nxt.Context.len.Entity.exp
  in
  let sn = Sign.to_string sign
  and it = get_inttype ~loc ~fastpath:false size
  and en = Endian.to_string endian in
  let ex = sprintf "Bitstring.extract_%s_%s_%s" it en sn
  in
  [%expr [%e evar ~loc ex] [%e edat] [%e eoff] [%e elen] [%e eint ~loc size]]
    [@metaloc loc]
;;

let gen_int_extractor ~loc nxt fld =
  let open Qualifiers in
  let (l, v) = fld.MatchField.len
  in
  let edat = nxt.Context.dat.Entity.exp
  and eoff = nxt.Context.off.Entity.exp
  and elen = nxt.Context.len.Entity.exp
  in
  match v, fld.MatchField.qls.sign, fld.MatchField.qls.endian with
    (* 1-bit type *)
    | Some (size), Some (_), Some (_) when size = 1 ->
      [%expr
        Bitstring.extract_bit [%e edat] [%e eoff] [%e elen] [%e l]]
        [@metaloc loc]
    (* 8-bit type *)
    | Some (size), Some (sign), Some (_) when size >= 2 && size <= 8 ->
      let ex = sprintf "Bitstring.extract_char_%s" (Sign.to_string sign)
      in
      [%expr
        [%e evar ~loc ex] [%e edat] [%e eoff] [%e elen] [%e eint ~loc size]]
        [@metaloc loc]
    (* 16|32|64-bit type with referred endianness *)
    | Some (size), Some (sign), Some (Endian.Referred r) ->
      let ss = Sign.to_string sign
      and it = get_inttype ~loc ~fastpath:false size in
      let ex = sprintf "Bitstring.extract_%s_ee_%s" it ss
      in
      [%expr
        [%e evar ~loc ex] ([%e r]) [%e edat] [%e eoff] [%e elen] [%e eint ~loc size]]
        [@metaloc loc]
    (* 16|32|64-bit type with immediate endianness *)
    | Some (size), Some (sign), Some (endian) ->
      if fld.MatchField.opt then
        gen_int_extractor_static ~loc nxt size sign endian
      else
        gen_int_extractor_dynamic ~loc nxt size sign endian
    (* Variable size *)
    | None, Some (sign), Some (Endian.Referred r) ->
      let ss = Sign.to_string sign in
      let ex = sprintf "Bitstring.extract_int64_ee_%s" ss in
      [%expr
        [%e evar ~loc ex] ([%e r]) [%e edat] [%e eoff] [%e elen] ([%e l])]
        [@metaloc loc]
    | None, Some (sign), Some (endian) ->
      let es = Endian.to_string endian and ss = Sign.to_string sign in
      let ex = sprintf "Bitstring.extract_int64_%s_%s" es ss in
      [%expr
        [%e evar ~loc ex] [%e edat] [%e eoff] [%e elen] ([%e l])]
        [@metaloc loc]
    (* Invalid type *)
    | _, _, _ ->
      location_exn ~loc "Invalid type"
;;

let gen_extractor ~loc nxt fld =
  let open Qualifiers in
  let (l, v) = fld.MatchField.len
  in
  let edat = nxt.Context.dat.Entity.exp
  and eoff = nxt.Context.off.Entity.exp
  and elen = nxt.Context.len.Entity.exp
  in
  match fld.MatchField.qls.value_type with
  | Some (Type.Bitstring) -> begin
      match v with
      | Some (-1) ->
        [%expr ([%e edat], [%e eoff], [%e elen])] [@metaloc loc]
      | Some (_) | None ->
        [%expr ([%e edat], [%e eoff], [%e l])] [@metaloc loc]
    end
  | Some (Type.String) ->
    [%expr
      (Bitstring.string_of_bitstring ([%e edat], [%e eoff], [%e l]))]
      [@metaloc loc]
  | Some (Type.Int) ->
    gen_int_extractor ~loc nxt fld
  | _ ->
    location_exn ~loc "Invalid type"
;;

let gen_value ~loc fld res beh =
  let open Qualifiers in
  match fld.MatchField.qls.bind, fld.MatchField.qls.map  with
  | Some b, None  ->
    [%expr let [%p fld.pat] = [%e b] in [%e beh]][@metaloc loc]
  | None, Some m  ->
    let exp = MatchField.as_evar fld in
    [%expr let [%p fld.pat] = [%e m] [%e exp] in [%e beh]][@metaloc loc]
  | _, _ -> beh
;;

let rec gen_next ~loc cur nxt fld beh fields =
  let open Entity in
  let open Context in
  let (l, v) = fld.MatchField.len in
  match v with
  | Some (-1) ->
    [%expr
      let [%p nxt.off.pat] = [%e nxt.off.exp] + [%e nxt.len.exp]
      and [%p nxt.len.pat] = 0 in
      [%e (gen_fields ~loc cur nxt beh fields)]]
      [@metaloc loc]
  | Some (_) | None ->
    [%expr
      let [%p nxt.off.pat] = [%e nxt.off.exp] + [%e l]
      and [%p nxt.len.pat] = [%e nxt.len.exp] - [%e l] in
      [%e (gen_fields ~loc cur nxt beh fields)]]
      [@metaloc loc]

and gen_next_all ~loc cur nxt beh fields =
  let open Entity in
  let open Context in
  [%expr
    let [%p nxt.off.pat] = [%e nxt.off.exp] + [%e nxt.len.exp]
    and [%p nxt.len.pat] = 0 in
    [%e (gen_fields ~loc cur nxt beh fields)]]
    [@metaloc loc]

and gen_match_check ~loc = function
  | Some chk  -> chk
  | None      -> ebool true ~loc

and gen_match ~loc cur nxt fld beh fields =
  let open Entity in
  let open Context in
  let open Qualifiers in
  let value = Entity.make ~loc "val"
  and (l, _) = fld.MatchField.len
  in
  let mcheck = gen_match_check ~loc fld.MatchField.qls.check
  and mfields = gen_fields ~loc cur nxt beh fields
  and mres = gen_extractor ~loc nxt fld
  in
  let mwrap = gen_value ~loc fld value.exp mfields
  in
  let mcase = [%expr
    begin match [%e value.exp] with
      | [%p fld.MatchField.pat] when [%e mcheck] -> [%e mwrap]
      | _ -> ()
    end][@metaloc loc]
  in
  [%expr
    let [%p value.pat]   = [%e mres]
    and [%p nxt.off.pat] = [%e nxt.off.exp] + [%e l]
    and [%p nxt.len.pat] = [%e nxt.len.exp] - [%e l] in [%e mcase]]
    [@metaloc loc]

and gen_offset ~loc cur nxt fld beh =
  let open Context in
  let open Entity in
  let open Qualifiers in
  match fld.MatchField.qls.offset with
  | Some ({ pexp_loc; _ } as off) ->
    [%expr
      let [%p nxt.off.pat] = [%e cur.off.exp] + [%e off] in [%e beh]]
      [@metaloc pexp_loc]
  | None -> beh

and gen_offset_saver ~loc cur nxt fld beh =
  let open Context in
  let open Entity in
  let open Qualifiers in
  match fld.MatchField.qls.save_offset_to with
  | Some { pexp_desc = Pexp_ident ({ txt; loc = eloc }); _ } ->
    let ptxt = pvar ~loc:eloc (Longident.last_exn txt) in
    [%expr
      let [%p ptxt] = [%e nxt.off.exp] - [%e cur.off.exp] in [%e beh]]
      [@metaloc eloc]
  | Some _ | None -> beh

and gen_unbound_string ~loc cur nxt fld beh fields =
  let p = fld.MatchField.pat
  in
  match p with
  | { ppat_desc = Ppat_var(_); _ } ->
    [%expr
      let [%p p] = [%e (gen_extractor ~loc nxt fld)] in
      [%e (gen_next_all ~loc cur nxt beh fields)]]
      [@metaloc loc]
  | [%pat? _ ] ->
    [%expr
      [%e (gen_next_all ~loc cur nxt beh fields)]]
      [@metaloc loc]
  | _ ->
    location_exn ~loc "Unbound string or bitstring can only be assigned to a variable or skipped"

and gen_bound_bitstring ~loc cur nxt fld beh fields =
  let open Entity in
  let open Context in
  let p = fld.MatchField.pat
  and (l, _) = fld.MatchField.len
  in
  match p with
  | { ppat_desc = Ppat_var(_); _ } ->
    [%expr
      if Stdlib.(>=) [%e nxt.len.exp] [%e l] then
        let [%p p] = [%e (gen_extractor ~loc nxt fld)] in
        [%e (gen_next ~loc cur nxt fld beh fields)]
      else ()]
      [@metaloc loc]
  | [%pat? _ ] ->
    [%expr
      if Stdlib.(>=) [%e nxt.len.exp] [%e l] then
        [%e (gen_next ~loc cur nxt fld beh fields)]
      else ()]
      [@metaloc loc]
  | _ ->
    location_exn ~loc "Bound bitstring can only be assigned to variables or skipped"

and gen_bound_string ~loc cur nxt fld beh fields =
  let open Entity in
  let open Context in
  let (l, _) = fld.MatchField.len
  in
  [%expr
    if Stdlib.(>=) [%e nxt.len.exp] [%e l] then
      [%e (gen_match ~loc cur nxt fld beh fields)]
    else ()]
    [@metaloc loc]

and gen_bound_int_with_size ~loc cur nxt fld beh fields =
  let open Entity in
  let open Context in
  let (l, _) = fld.MatchField.len
  in
  [%expr
    if Stdlib.(>=) [%e nxt.len.exp] [%e l] then
      [%e (gen_match ~loc cur nxt fld beh fields)]
    else ()]
    [@metaloc loc]

and gen_bound_int ~loc cur nxt fld beh fields =
  let open Entity in
  let open Context in
  let (l, _) = fld.MatchField.len
  in
  [%expr
    if Stdlib.(>=) [%e l]           1  &&
       Stdlib.(<=) [%e l]           64 &&
       Stdlib.(>=) [%e nxt.len.exp] [%e l] then
      [%e (gen_match ~loc cur nxt fld beh fields)]
    else ()]
    [@metaloc loc]

and gen_fields_with_quals_by_type ~loc cur nxt fld beh fields =
  let open Qualifiers in
  match check_field_len ~loc fld, fld.MatchField.qls.value_type with
  | Some (-1), Some (Type.Bitstring | Type.String) ->
    gen_unbound_string ~loc cur nxt fld beh fields
  | (Some (_) | None), Some (Type.Bitstring) ->
    gen_bound_bitstring ~loc cur nxt fld beh fields
  | (Some (_) | None), Some (Type.String) ->
    gen_bound_string ~loc cur nxt fld beh fields
  | Some (s), Some (Type.Int) ->
    if s >= 1 && s <= 64 then
      gen_bound_int_with_size ~loc cur nxt fld beh fields
    else
      location_exn ~loc "Invalid bit length for type Integer"
  | None, Some (Type.Int) ->
    gen_bound_int ~loc cur nxt fld beh fields
  | _, _ ->
    location_exn ~loc "No type to generate"

and gen_fields_with_quals ~loc cur nxt fld beh fields =
  gen_fields_with_quals_by_type ~loc cur nxt fld beh fields
  |> gen_offset_saver ~loc cur nxt fld
  |> gen_offset ~loc cur nxt fld

and gen_fields ~loc cur nxt beh fields =
  let (exp, alias) = beh
  in
  match fields with
  | [] ->
    begin match alias with
      | None -> exp
      | Some a -> [%expr
          let [%p pvar ~loc a] = ([%e cur.dat.exp], [%e cur.off.exp], ([%e cur.len.exp] - [%e nxt.len.exp]))
          in
          [%e exp]
        ][@metaloc loc]
    end
  | MatchField.Any (_) :: tl ->
    begin match alias with
      | None -> exp
      | Some a -> [%expr
          let [%p pvar ~loc a] = ([%e cur.dat.exp], [%e cur.off.exp], [%e cur.len.exp])
          in
          [%e exp]
        ][@metaloc loc]
    end
  | MatchField.Tuple (fld) :: tl -> gen_fields_with_quals ~loc cur nxt fld beh tl
;;

let is_field_size_open_ended = function
  | (_, Some (-1))  -> true
  | _               -> false

let check_for_open_endedness fields =
  let check init fld =
    let p = fld.MatchField.pat
    and l = fld.MatchField.len in
    let oe = is_field_size_open_ended l in
    if init || (oe && init) then
      location_exn ~loc:p.ppat_loc "Pattern is already open-ended"
    else oe
  in
  let inspect init = function
    | MatchField.Any (_) -> init && false
    | MatchField.Tuple fld -> check init fld
  in
  let rec scan init = function
    | [] -> ()
    | hd :: tl -> scan (inspect init hd) tl
  in
  scan false fields; fields
;;

let mark_optimized_fastpath fields =
  let open Qualifiers in
  let open MatchField
  in
  let check_field off tuple =
    match tuple with
    | { pat; len = (l, Some (v)); qls = { value_type = Some (Type.Int); _ }; _ } ->
      if (off land 7) = 0 && (v = 16 || v = 32 || v = 64) then
        (Some (off + v), MatchField.Tuple { tuple with opt = true })
      else
        (None, MatchField.Tuple tuple)
    | _ ->
      (None, MatchField.Tuple tuple)
  in
  let check_offset_and_field offset fld =
    match offset, fld with
    | Some (off), MatchField.Tuple (tuple) -> check_field off tuple
    | _, _ -> (None, fld)
  in
  let rec scan offset result = function
    | [] -> result
    | hd :: tl ->
      let (noff, nfld) = check_offset_and_field offset hd in
      scan noff (result @ [ nfld ]) tl
  in
  scan (Some 0) [] fields
;;

let gen_case_constant ~loc cur nxt res case value alias =
  let open Entity in
  let beh = [%expr
    [%e res.exp] := Some ([%e case.pc_rhs]);
    raise Exit][@metaloc loc]
  in
  let beh =
    match case.pc_guard with
    | None -> beh
    | Some cond -> [%expr if [%e cond] then [%e beh] else ()][@metaloc loc]
  in
  split_string ~on:";" value
  |> split_loc ~loc
  |> List.map parse_match_fields
  |> check_for_open_endedness
  |> mark_optimized_fastpath
  |> gen_fields ~loc cur nxt (beh, alias)

let gen_case cur nxt res case =
  let loc = case.pc_lhs.ppat_loc in
  match case.pc_lhs.ppat_desc with
  | Ppat_constant (Pconst_string (value, _, _)) ->
    gen_case_constant ~loc cur nxt res case value None
  | Ppat_alias ({ ppat_desc = Ppat_constant (Pconst_string (value, _, _)); _ }, { txt = a; _ }) ->
    gen_case_constant ~loc cur nxt res case value (Some a)
  | _ ->
    location_exn ~loc "Wrong pattern type"
;;

let rec gen_cases_sequence ~loc = function
  | []        -> location_exn ~loc "Empty case list"
  | [hd]      -> hd
  | hd :: tl  -> [%expr [%e hd]; [%e gen_cases_sequence ~loc tl]][@metaloc loc]
;;

let gen_cases ~loc ident cases =
  let open Entity in
  let open Context in
  let cur = Context.make ~loc
  and res = Entity.make ~loc "res"
  in
  let nxt = Context.next ~loc cur
  and tupl = [%pat? ([%p cur.dat.pat], [%p cur.off.pat], [%p cur.len.pat])][@metaloc loc]
  and fnam = estring ~loc loc.Location.loc_start.pos_fname
  and lpos = eint ~loc loc.Location.loc_start.pos_lnum
  and cpos = eint ~loc (loc.Location.loc_start.pos_cnum - loc.Location.loc_start.pos_bol)
  in
  List.fold_left
    (fun acc case -> acc @ [ gen_case cur nxt res case ])
    []
    cases
  |> gen_cases_sequence ~loc
  |> fun seq ->
  [%expr
    let [%p tupl]        = [%e ident] in
    let [%p nxt.off.pat] = [%e cur.off.exp]
    and [%p nxt.len.pat] = [%e cur.len.exp]
    and [%p res.pat]     = ref None
    in
    (try [%e seq]; with | Exit -> ());
    match ![%e res.exp] with
    | Some x -> x
    | None -> raise (Match_failure ([%e fnam], [%e lpos], [%e cpos]))]
    [@metaloc loc]
;;

let gen_function ~loc cases =
  let open Entity in
  let cas = Entity.make ~loc "case" in
  [%expr
    (fun [%p cas.pat] -> [%e (gen_cases ~loc cas.exp cases)])]
    [@metaloc loc]

(* Constructor generators *)

let gen_constructor_exn ~loc =
  let open Location in
  [%expr Bitstring.Construct_failure (
      [%e estring ~loc "Bad field value"],
        [%e estring ~loc loc.loc_start.pos_fname],
        [%e eint ~loc loc.loc_start.pos_lnum],
        [%e eint ~loc loc.loc_start.pos_cnum])]
    [@metaloc loc]
;;

let gen_constructor_bitstring ~loc sym (l, _, _ ) =
  [%expr
    Bitstring.construct_bitstring [%e sym.Entity.exp] [%e l]]
    [@metaloc loc]
;;

let gen_constructor_string ~loc sym (l, _, _) =
  [%expr
    Bitstring.construct_string [%e sym.Entity.exp] [%e l]]
    [@metaloc loc]
;;

let get_1_bit_constr_value ~loc (l, _, _) =
  match (evaluate_expr l) with
    | Some (1)        -> [%expr true][@metaloc loc]
    | Some (0)        -> [%expr false][@metaloc loc]
    | Some (_) | None -> l
;;

let gen_constructor_int ~loc sym fld =
  let open Qualifiers in
  let (l, s, q) = fld in
  let eexc = gen_constructor_exn ~loc
  and esym = sym.Entity.exp in
  let (fnc, vl, sz) = match (evaluate_expr s), q.sign, q.endian with
    (* 1-bit type *)
    | Some (size), Some (_), Some (_) when size = 1 ->
      (evar ~loc "Bitstring.construct_bit", get_1_bit_constr_value ~loc fld, [%expr 1])
    (* 8-bit type *)
    | Some (size), Some (sign), Some (_) when size >= 2 && size <= 8 ->
      let sn = Sign.to_string sign in
      let ex = sprintf "Bitstring.construct_char_%s" sn in
      (evar ~loc ex, l, eint ~loc size)
    (* 16|32|64-bit type *)
    | Some (size), Some (sign), Some (Endian.Referred r) ->
      let ss = Sign.to_string sign
      and it = get_inttype ~loc ~fastpath:false size in
      let ex = sprintf "Bitstring.construct_%s_ee_%s" it ss in
      ([%expr [%e evar ~loc ex] [%e r]], l, s)
    | Some (size), Some (sign), Some (endian) ->
      let tp = get_inttype ~loc ~fastpath:false size
      and en = Endian.to_string endian
      and sn = Sign.to_string sign in
      let ex = sprintf "Bitstring.construct_%s_%s_%s" tp en sn in
      (evar ~loc ex, l, eint ~loc size)
    (* Variable size types *)
    | None, Some (sign), Some (Endian.Referred r) ->
      let ss = Sign.to_string sign in
      let ex = sprintf "Bitstring.construct_int64_ee_%s" ss in
      ([%expr [%e evar ~loc ex] [%e r]], l, s)
    | None, Some (sign), Some (endian) ->
      let en = Endian.to_string endian
      and sn = Sign.to_string sign in
      let ex = sprintf "Bitstring.construct_int64_%s_%s" en sn in
      (evar ~loc ex, l, s)
    (* Invalid type *)
    | _, _, _ ->
      location_exn ~loc "Invalid type"
  in
  [%expr
    [%e fnc] [%e esym] [%e vl] [%e sz] [%e eexc]]
    [@metaloc loc]
;;

let gen_constructor_complete ~loc sym fld =
  let (_, _, q) = fld in
  match q.Qualifiers.value_type with
  | Some (Type.Bitstring) -> gen_constructor_bitstring ~loc sym fld
  | Some (Type.String)    -> gen_constructor_string ~loc sym fld
  | Some (Type.Int)       -> gen_constructor_int ~loc sym fld
  | _                     -> location_exn ~loc "Invalid type"
;;

let gen_constructor ~loc sym = function
  | (f, Some (s), Some (q)) -> gen_constructor_complete ~loc sym (f, s, q)
  | _ -> location_exn ~loc "Invalid field format"
;;

let gen_assignment_size_of_sized_field ~loc (f, s, q) =
  match (evaluate_expr s), option_bind q (fun q -> q.Qualifiers.value_type) with
  (* Deal with String type *)
  | Some (-1), Some (Type.String) -> [%expr (String.length [%e f] * 8)]
  | Some (v),  Some (Type.String) when v > 0 && (v mod 8) = 0 -> s
  | Some (_),  Some (Type.String) ->
      location_exn ~loc "Length of string must be > 0 and multiple of 8, or the special value -1"
  (* Deal with Bitstring type *)
  | Some (-1), Some (Type.Bitstring) -> [%expr (Bitstring.bitstring_length [%e f])]
  | Some (v),  Some (Type.Bitstring) when v > 0 -> s
  | Some (_),  Some (Type.Bitstring) ->
      location_exn ~loc "Length of bitstring must be >= 0 or the special value -1"
  (* Deal with other types *)
  | Some (v), _ when v > 0 -> s
  | Some (v), _ ->
      location_exn ~loc "Negative or null field size in constructor"
  (* Unknown field size, arbitrary expression *)
  | None, _ -> s
;;

let gen_assignment_size_of_field ~loc = function
  | (_, None, _) -> [%expr 0]
  | (f, Some (s), q) -> gen_assignment_size_of_sized_field ~loc (f, s, q)
;;

let rec gen_assignment_size ~loc = function
  | [] -> [%expr 0]
  | field :: tl ->
     let this = gen_assignment_size_of_field ~loc field in
     let next = gen_assignment_size ~loc tl in
     [%expr [%e this] + ([%e next])][@metaloc loc]
;;

let gen_assignment_behavior ~loc sym fields =
  let size = gen_assignment_size ~loc fields in
  let res = sym.Entity.exp in
  let rep = [%expr Bitstring.Buffer.contents [%e res]][@metaloc loc] in
  let len = match (evaluate_expr size) with
    | Some (v)  -> eint v ~loc
    | None      -> size
  in
  let post =
    [%expr
      let _res = [%e rep] in
      if Stdlib.(=) (Bitstring.bitstring_length _res) [%e len]
      then _res else raise Exit]
      [@metaloc loc]
  in
  let seq = List.fold_right
      (fun fld acc -> [%expr [%e (gen_constructor ~loc sym fld)]; [%e acc]])
      fields
      post
  in
  [%expr
    let [%p sym.Entity.pat] = Bitstring.Buffer.create () in
    [%e seq]]
    [@metaloc loc]
;;

let parse_assignment_behavior ~loc sym value =
  split_string ~on:";" value
  |> split_loc ~loc
  |> List.map (fun flds -> parse_const_fields flds)
  |> gen_assignment_behavior ~loc sym
;;

let gen_constructor_expr ~loc value =
  let open Entity in
  let sym = Entity.make ~loc "constructor" in
  let beh = parse_assignment_behavior ~loc sym value in
  [%expr let [%p sym.pat] = fun () -> [%e beh] in [%e sym.exp] ()]
;;

let transform_single_let ~loc ast expr =
  match ast.pvb_pat.ppat_desc, ast.pvb_expr.pexp_desc with
  | Parsetree.Ppat_var (s), Pexp_constant (Pconst_string (value, _, _)) ->
    let pat = pvar ~loc s.txt in
    let constructor_expr = gen_constructor_expr ~loc value in
    [%expr let [%p pat] = [%e constructor_expr] in [%e expr]]
  | _ -> location_exn ~loc "Invalid pattern type"
;;


let staged_mode = ref false

module StagedGen = struct
  let enc ~loc name e =
    pexp_extension ~loc
      ({ txt = name; loc }, PStr [ pstr_eval ~loc e [] ])

  let enc_quote ~loc e =
    enc ~loc Astlib.Encoding_505.Ext_name.pexp_quote e

  let enc_splice ~loc e =
    enc ~loc Astlib.Encoding_505.Ext_name.pexp_splice e

    let mentioned bound e =
    let found = Hashtbl.create 8 in
    let it =
      object
        inherit Ast_traverse.iter as super

        method! expression x =
          (match x.pexp_desc with
          | Pexp_ident { txt = Longident.Lident n; _ }
            when List.mem n bound ->
              Hashtbl.replace found n ()
          | _ -> ());
          super#expression x
      end
    in
    it#expression e;
    List.filter (fun n -> Hashtbl.mem found n) bound

    let wrap ~loc bound e =
    match mentioned bound e with
    | [] -> enc_quote ~loc e
    | ns ->
        let body =
          List.fold_right
            (fun n acc ->
              [%expr
                let [%p pvar ~loc n] = [%e enc_splice ~loc (evar ~loc n)] in
                [%e acc]])
            ns e
        in
        let body =
          {
            body with
            pexp_attributes =
              attribute ~loc ~name:{ txt = "warning"; loc }
                ~payload:(PStr [ pstr_eval ~loc (estring ~loc "-26-27") [] ])
              :: body.pexp_attributes;
          }
        in
        enc_quote ~loc body

  let sign_expr ~loc = function
    | Sign.Signed -> [%expr Bitstring_staged.Signed]
    | Sign.Unsigned -> [%expr Bitstring_staged.Unsigned]

  let endian_expr ~loc bound = function
    | Endian.Big -> [%expr Bitstring_staged.Big]
    | Endian.Little -> [%expr Bitstring_staged.Little]
    | Endian.Native -> [%expr Bitstring_staged.Native]
    | Endian.Referred r ->
        [%expr Bitstring_staged.Referred [%e wrap ~loc bound r]]

  let pattern_has_vars p =
    let found = ref false in
    let it =
      object
        inherit Ast_traverse.iter as super

        method! pattern x =
          (match x.ppat_desc with
          | Ppat_var _ | Ppat_alias _ -> found := true
          | _ -> ());
          super#pattern x
      end
    in
    it#pattern p;
    !found

  let name_of_qual_var ~loc = function
    | { pexp_desc = Pexp_ident { txt = Longident.Lident n; _ }; _ } -> n
    | _ -> location_exn ~loc "save_offset_to expects a variable"

  let rec emit_fields ~loc bound fields ((guard, rhs, alias) as gr) =
    match fields with
    | [] -> (
        let finish bound =
          let done_ =
            [%expr Bitstring_staged.Done [%e wrap ~loc bound rhs]]
          in
          match guard with
          | None -> done_
          | Some g ->
              [%expr
                Bitstring_staged.Guard ([%e wrap ~loc bound g], [%e done_])]
        in
        match alias with
        | None -> finish bound
        | Some a ->
            [%expr
              Bitstring_staged.Matched
                [%e
                  pexp_fun ~loc Nolabel None (pvar ~loc a)
                    (finish (bound @ [ a ]))]])
    | MatchField.Any p :: _ ->
        location_exn ~loc:p.ppat_loc
          "wildcard field is only supported as a whole '{| _ |}' case in \
           --staged mode"
    | MatchField.Tuple f :: rest -> emit_field ~loc bound f rest gr

  and emit_field ~loc bound (f : MatchField.tuple) rest gr =
    let floc = f.pat.ppat_loc in
    let l, v = f.len in
    let vt =
      match f.qls.Qualifiers.value_type with
      | Some t -> t
      | None -> location_exn ~loc:floc "no value type"
    in
    let sign =
      match f.qls.Qualifiers.sign with
      | Some s -> s
      | None -> Sign.Unsigned
    in
    let endian =
      match f.qls.Qualifiers.endian with
      | Some e -> e
      | None -> Endian.Big
    in
    let int_desc_expr n =
      [%expr
        {
          Bitstring_staged.size = [%e eint ~loc n];
          sign = [%e sign_expr ~loc sign];
          endian = [%e endian_expr ~loc bound endian];
        }]
    in
        let ctor =
      match (vt, v) with
      | Type.Int, Some 1 -> fun k -> [%expr Bitstring_staged.Bit [%e k]]
      | Type.Int, Some n when n >= 2 && n <= 31 ->
          fun k ->
            [%expr Bitstring_staged.Int ([%e int_desc_expr n], [%e k])]
      | Type.Int, Some 32 ->
          if sign = Sign.Signed then
            location_exn ~loc:floc
              "signed 32-bit fields are not supported in --staged mode (the \
               runtime has no signed int32 extractor)"
          else fun k ->
            [%expr
              Bitstring_staged.Int32
                ([%e endian_expr ~loc bound endian], [%e k])]
      | Type.Int, Some n when n >= 33 && n <= 64 ->
          if sign = Sign.Signed then
            location_exn ~loc:floc
              "signed fields wider than 31 bits are not supported in \
               --staged mode (the runtime has no signed int64 extractor)"
          else fun k ->
            [%expr
              Bitstring_staged.Int64
                ( {
                    Bitstring_staged.size64 =
                      Bitstring_staged.Const [%e eint ~loc n];
                    endian64 = [%e endian_expr ~loc bound endian];
                  },
                  [%e k] )]
      | Type.Int, Some _ ->
          location_exn ~loc:floc "invalid integer field size"
      | Type.Int, None ->
          if sign = Sign.Signed then
            location_exn ~loc:floc
              "signed dynamically-sized fields are not supported in --staged \
               mode (the runtime has no signed int64 extractor)"
          else fun k ->
            [%expr
              Bitstring_staged.Int64
                ( {
                    Bitstring_staged.size64 =
                      Bitstring_staged.Dyn [%e wrap ~loc bound l];
                    endian64 = [%e endian_expr ~loc bound endian];
                  },
                  [%e k] )]
      | Type.String, Some -1 ->
          fun k ->
            [%expr Bitstring_staged.String (Bitstring_staged.All, [%e k])]
      | Type.String, Some n ->
          fun k ->
            [%expr
              Bitstring_staged.String
                (Bitstring_staged.Const [%e eint ~loc n], [%e k])]
      | Type.String, None ->
          fun k ->
            [%expr
              Bitstring_staged.String
                (Bitstring_staged.Dyn [%e wrap ~loc bound l], [%e k])]
      | Type.Bitstring, Some -1 ->
          fun k ->
            [%expr Bitstring_staged.Bits (Bitstring_staged.All, [%e k])]
      | Type.Bitstring, Some n ->
          fun k ->
            [%expr
              Bitstring_staged.Bits
                (Bitstring_staged.Const [%e eint ~loc n], [%e k])]
      | Type.Bitstring, None ->
          fun k ->
            [%expr
              Bitstring_staged.Bits
                (Bitstring_staged.Dyn [%e wrap ~loc bound l], [%e k])]
    in
    let check_guard bound tail =
      match f.qls.Qualifiers.check with
      | None -> tail
      | Some c ->
          [%expr Bitstring_staged.Guard ([%e wrap ~loc bound c], [%e tail])]
    in
        let seek_wrap spec_e =
      match f.qls.Qualifiers.offset with
      | None -> spec_e
      | Some off_e ->
          let size_e =
            match evaluate_expr off_e with
            | Some n when n >= 0 ->
                [%expr Bitstring_staged.Const [%e eint ~loc n]]
            | _ -> [%expr Bitstring_staged.Dyn [%e wrap ~loc bound off_e]]
          in
          [%expr Bitstring_staged.Seek ([%e size_e], [%e spec_e])]
    in
        let body =
      let with_save bound k =
        match f.qls.Qualifiers.save_offset_to with
        | None -> k bound
        | Some v ->
            let n = name_of_qual_var ~loc:floc v in
            [%expr
              Bitstring_staged.SaveOffset
                [%e
                  pexp_fun ~loc Nolabel None (pvar ~loc n)
                    (k (bound @ [ n ]))]]
      in
      with_save bound (fun bound ->
          match f.pat.ppat_desc with
          | Ppat_var { txt = uname; _ } -> (
              match (f.qls.Qualifiers.map, f.qls.Qualifiers.bind) with
              | Some _, Some _ ->
                  location_exn ~loc:floc "map and bind are exclusive"
              | None, None ->
                  let bound' = bound @ [ uname ] in
                  let tail =
                    check_guard bound' (emit_fields ~loc bound' rest gr)
                  in
                  ctor (pexp_fun ~loc Nolabel None (pvar ~loc uname) tail)
              | Some m, None ->
                                    let fresh = Entity.mksym "raw" in
                  let bound' = bound @ [ uname ] in
                  let tail =
                    check_guard bound' (emit_fields ~loc bound' rest gr)
                  in
                  let app =
                    pexp_apply ~loc m
                      [ (Nolabel, enc_splice ~loc (evar ~loc fresh)) ]
                  in
                  ctor
                    (pexp_fun ~loc Nolabel None (pvar ~loc fresh)
                       [%expr
                         Bitstring_staged.Let
                           ( [%e wrap ~loc bound app],
                             [%e
                               pexp_fun ~loc Nolabel None (pvar ~loc uname)
                                 tail] )])
              | None, Some b ->
                                    let bound' = bound @ [ uname ] in
                  let tail =
                    check_guard bound' (emit_fields ~loc bound' rest gr)
                  in
                  ctor
                    (pexp_fun ~loc Nolabel None (ppat_any ~loc)
                       [%expr
                         Bitstring_staged.Let
                           ( [%e wrap ~loc bound b],
                             [%e
                               pexp_fun ~loc Nolabel None (pvar ~loc uname)
                                 tail] )]))
          | Ppat_any ->
              let tail = check_guard bound (emit_fields ~loc bound rest gr) in
              ctor (pexp_fun ~loc Nolabel None (ppat_any ~loc) tail)
          | Ppat_constant (Pconst_integer (lit, None))
            when (match (vt, v) with
                  | Type.Int, Some n -> n >= 2 && n <= 31
                  | _ -> false)
                 && Option.is_some (int_of_string_opt lit) ->
                            let n = match v with Some n -> n | None -> assert false in
              let lit = int_of_string lit in
              let tail = check_guard bound (emit_fields ~loc bound rest gr) in
              [%expr
                Bitstring_staged.IntLit
                  ([%e int_desc_expr n], [%e eint ~loc lit], [%e tail])]
          | _ when not (pattern_has_vars f.pat) ->
                            let n = Entity.mksym "field" in
              let test =
                pexp_match ~loc
                  (enc_splice ~loc (evar ~loc n))
                  [
                    case ~lhs:f.pat ~guard:None ~rhs:[%expr true];
                    case ~lhs:(ppat_any ~loc) ~guard:None ~rhs:[%expr false];
                  ]
              in
              let tail = check_guard bound (emit_fields ~loc bound rest gr) in
              let guarded =
                [%expr
                  Bitstring_staged.Guard ([%e enc_quote ~loc test], [%e tail])]
              in
              ctor (pexp_fun ~loc Nolabel None (pvar ~loc n) guarded)
          | _ ->
              location_exn ~loc:floc
                "patterns binding variables (other than a plain variable) \
                 are not supported in --staged mode")
    in
    seek_wrap body

    let emit_case ~loc ?alias fields guard rhs =
    emit_fields ~loc [] fields (guard, rhs, alias)

  let parse_case_fields ~loc value =
    split_string ~on:";" value
    |> split_loc ~loc
    |> List.map parse_match_fields
    |> check_for_open_endedness

  let gen_cases ~loc ident cases =
    let fnam = estring ~loc loc.Location.loc_start.pos_fname
    and lpos = eint ~loc loc.Location.loc_start.pos_lnum
    and cpos =
      eint ~loc
        (loc.Location.loc_start.pos_cnum - loc.Location.loc_start.pos_bol)
    in
    let specs, default =
      List.fold_left
        (fun (specs, default) case ->
          let cloc = case.pc_lhs.ppat_loc in
          (match default with
          | Some _ ->
              location_exn ~loc:cloc
                "unreachable case after the '{| _ |}' catch-all"
          | None -> ());
          let value, alias =
            match case.pc_lhs.ppat_desc with
            | Ppat_constant (Pconst_string (value, _, _)) -> (value, None)
            | Ppat_alias
                ( { ppat_desc = Ppat_constant (Pconst_string (value, _, _)); _ },
                  { txt = a; _ } ) ->
                (value, Some a)
            | _ -> location_exn ~loc:cloc "Wrong pattern type"
          in
          match (parse_case_fields ~loc:cloc value, case.pc_guard, alias) with
          | [ MatchField.Any _ ], None, None -> (specs, Some case.pc_rhs)
          | [ MatchField.Any _ ], guard, _ ->
              ( specs
                @ [ emit_case ~loc:cloc ?alias [] guard case.pc_rhs ],
                None )
          | fields, guard, _ ->
              ( specs @ [ emit_case ~loc:cloc ?alias fields guard case.pc_rhs ],
                None ))
        ([], None) cases
    in
    let default_body =
      match default with
      | Some rhs -> rhs
      | None ->
          [%expr raise (Match_failure ([%e fnam], [%e lpos], [%e cpos]))]
    in
    let default_expr = enc_quote ~loc [%expr fun () -> [%e default_body]] in
    enc_splice ~loc
      [%expr
        Bitstring_staged.match_
          [%e enc_quote ~loc ident]
          [%e elist ~loc specs] ~default:[%e default_expr]]

  let gen_function ~loc cases =
    let sym = Entity.mksym "subject" in
    [%expr
      fun [%p pvar ~loc sym] -> [%e gen_cases ~loc (evar ~loc sym) cases]]

  
  let emit_cfield ~loc ((f, size, quals) as fld) =
    let q = match quals with Some q -> q | None -> Qualifiers.default in
    let s =
      match size with
      | Some s -> s
      | None -> location_exn ~loc "no size given for constructor field"
    in
    let vt =
      match q.Qualifiers.value_type with Some t -> t | None -> Type.Int
    in
    let sign =
      match q.Qualifiers.sign with Some s -> s | None -> Sign.Unsigned
    in
    let endian =
      match q.Qualifiers.endian with Some e -> e | None -> Endian.Big
    in
    match (vt, evaluate_expr s) with
    | Type.Int, Some 1 ->
        [%expr
          Bitstring_staged.CBit
            [%e enc_quote ~loc (get_1_bit_constr_value ~loc fld)]]
    | Type.Int, Some n when n >= 2 && n <= 31 ->
        [%expr
          Bitstring_staged.CInt
            ( {
                Bitstring_staged.size = [%e eint ~loc n];
                sign = [%e sign_expr ~loc sign];
                endian = [%e endian_expr ~loc [] endian];
              },
              [%e enc_quote ~loc f] )]
    | Type.Int, Some 32 ->
        if sign = Sign.Signed then
          location_exn ~loc
            "signed 32-bit fields are not supported in --staged mode"
        else
          [%expr
            Bitstring_staged.CInt32
              ([%e endian_expr ~loc [] endian], [%e enc_quote ~loc f])]
    | Type.Int, Some n when n >= 33 && n <= 64 ->
        if sign = Sign.Signed then
          location_exn ~loc
            "signed fields wider than 31 bits are not supported in --staged \
             mode"
        else
          [%expr
            Bitstring_staged.CInt64
              ( {
                  Bitstring_staged.size64 =
                    Bitstring_staged.Const [%e eint ~loc n];
                  endian64 = [%e endian_expr ~loc [] endian];
                },
                [%e enc_quote ~loc f] )]
    | Type.Int, Some _ ->
        location_exn ~loc "invalid integer field size in constructor"
    | Type.Int, None ->
        if sign = Sign.Signed then
          location_exn ~loc
            "signed dynamically-sized fields are not supported in --staged \
             mode"
        else
          [%expr
            Bitstring_staged.CInt64
              ( {
                  Bitstring_staged.size64 =
                    Bitstring_staged.Dyn [%e enc_quote ~loc s];
                  endian64 = [%e endian_expr ~loc [] endian];
                },
                [%e enc_quote ~loc f] )]
    | Type.String, sz ->
        let size_e =
          match sz with
          | Some n when n >= 0 ->
              [%expr Bitstring_staged.Const [%e eint ~loc n]]
          | _ -> [%expr Bitstring_staged.Dyn [%e enc_quote ~loc s]]
        in
        [%expr Bitstring_staged.CString ([%e size_e], [%e enc_quote ~loc f])]
    | Type.Bitstring, _ ->
        [%expr Bitstring_staged.CBits [%e enc_quote ~loc f]]

  let gen_constructor_expr ~loc value =
    let fields =
      split_string ~on:";" value
      |> split_loc ~loc
      |> List.map parse_const_fields
    in
    let cfs = List.map (emit_cfield ~loc) fields in
    let size_e = gen_assignment_size ~loc fields in
    let fnam = estring ~loc loc.Location.loc_start.pos_fname
    and lpos = eint ~loc loc.Location.loc_start.pos_lnum
    and cpos =
      eint ~loc
        (loc.Location.loc_start.pos_cnum - loc.Location.loc_start.pos_bol)
    in
    enc_splice ~loc
      [%expr
        Bitstring_staged.construct_
          ~loc:([%e fnam], [%e lpos], [%e cpos])
          ~expect:[%e enc_quote ~loc size_e]
          [%e elist ~loc cfs]]

  let transform_single_let ~loc ast expr =
    match (ast.pvb_pat.ppat_desc, ast.pvb_expr.pexp_desc) with
    | Parsetree.Ppat_var s, Pexp_constant (Pconst_string (value, _, _)) ->
        let pat = pvar ~loc s.txt in
        [%expr
          let [%p pat] = [%e gen_constructor_expr ~loc value] in
          [%e expr]]
    | _ -> location_exn ~loc "Invalid pattern type"
end

let expression_expander expr =
  let loc = expr.pexp_loc in
  match expr.pexp_desc with
  | Pexp_constant (Pconst_string (value, _, (_ : string option))) ->
    if !staged_mode then StagedGen.gen_constructor_expr ~loc value
    else gen_constructor_expr ~loc value
  | Pexp_let (Nonrecursive, bindings, expr) ->
    let transform =
      if !staged_mode then StagedGen.transform_single_let
      else transform_single_let
    in
    List.fold_right
      (fun binding expr -> transform ~loc binding expr)
      bindings
      expr
  | Pexp_match (ident, cases) ->
    if !staged_mode then StagedGen.gen_cases ~loc ident cases
    else gen_cases ~loc ident cases
  | Pexp_function ([], _, Pfunction_cases (cases, _, _)) ->
    if !staged_mode then StagedGen.gen_function ~loc cases
    else gen_function ~loc cases
  | _ ->
    location_exn ~loc
      "'bitstring' can only be used with 'let', 'match', and as '[%bitstring]'"

let expression_rule =
  Extension.V3.declare
    "bitstring"
    Extension.Context.expression
    Ast_pattern.(single_expr_payload __)
    (fun ~ctxt -> expression_expander)
  |> Context_free.Rule.extension

let structure_item_rewriter ~(ctxt : Expansion_context.Extension.t) pat expr =
  let loc = Expansion_context.Extension.extension_point_loc ctxt in
  [%stri let [%p pat] = [%e expression_expander expr]]

let structure_item_rule =
  Extension.V3.declare
    "bitstring"
    Extension.Context.structure_item
    Ast_pattern.(pstr (pstr_value nonrecursive (value_binding ~constraint_:drop ~pat:__ ~expr:__ ^:: nil)  ^:: nil))
    structure_item_rewriter
  |> Context_free.Rule.extension

let () =
  Driver.add_arg "--staged" (Arg.Set staged_mode)
    ~doc:
      " emit MacoCaml splices building Bitstring_staged specs for \
       match%bitstring / function%bitstring (T28)"

let () =
  Driver.register_transformation "bitstring" ~rules:[
    expression_rule ;
    structure_item_rule ;
  ]
