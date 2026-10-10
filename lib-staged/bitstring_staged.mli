(** Typed staged backend for bitstring (T28).

    An ['r spec] describes one match case: a sequence of fields ending
    in a [Done] body.  Each field constructor carries the field's
    description and a function receiving the bound field value, so
    later field sizes and the final body can depend on earlier fields
    by ordinary closure:

    {[
      Int ({ size = 8; sign = Unsigned; endian = Big }, fun len ->
        String (Dyn << $len * 8 >>, fun payload ->
          Done << ... >>))
    ]}

    [match_] compiles a case list into a nested-if cascade over the
    packed [(data, off, len)] representation, calling the same
    [Bitstring.extract_*] primitives the classic ppx targets, with a
    single consolidated length check per fully-static case.  A run of
    consecutive cases that all begin with [IntLit] on the same field
    (equal size and sign, at most 8 bits) is not cascaded but
    dispatched with a constant-time switch on the tag's value;
    first-match-wins semantics are preserved exactly (see [IntLit]).
    [construct_] compiles a field list to either a single-allocation
    straight-line writer (fully static, packer-eligible layouts) or a
    [Bitstring.Buffer] pipeline.

    Contract: spec-builder functions must be pure — the compiler may
    apply them more than once at level -1, with placeholder arguments,
    to validate a spec and measure its static bit-length.

    Sign support mirrors the runtime's surface: signed extraction and
    construction exist for fields of up to 31 bits; the int32/int64
    primitives are unsigned only, so [Int32]/[Int64] fields carry
    endianness alone.  Dynamically-sized integer fields extract as
    [int64] (upstream semantics). *)

type sign = Unsigned | Signed
type endian = Big | Little | Native | Referred of Bitstring.endian expr

type size =
  | Const of int
  | Dyn of int expr
  | All  (** every remaining bit (the DSL's [-1]); String/Bits only *)

type int_desc = { size : int; sign : sign; endian : endian }
(** 2..31 bits *)

type int64_desc = { size64 : size; endian64 : endian }
(** 33..64 bits, or dynamically sized *)

type 'r spec =
  | Done : 'r expr -> 'r spec
  | Bit : (bool expr -> 'r spec) -> 'r spec
  | Int : int_desc * (int expr -> 'r spec) -> 'r spec
  | IntLit : int_desc * int * 'r spec -> 'r spec
      (** an [Int] field that must equal the literal; binds nothing.
          Behaves exactly like
          [Int (d, fun v -> Guard (<< $v = lit >>, rest))], but
          [match_] sees it: a run of cases led by [IntLit] on the same
          field is dispatched by one extraction of the tag and a
          constant-time switch on its value.  Within such a run,
          cases with the subject's tag are still tried in their
          original order (a failing guard or length check falls
          through as before), and a case with any other tag could not
          have matched; cases with no leading literal, or a leading
          literal on a different field, end the run and cascade as
          usual.  A literal the field cannot represent never matches. *)
  | Int32 : endian * (int32 expr -> 'r spec) -> 'r spec
  | Int64 : int64_desc * (int64 expr -> 'r spec) -> 'r spec
  | String : size * (string expr -> 'r spec) -> 'r spec
  | Bits : size * (Bitstring.t expr -> 'r spec) -> 'r spec
  | Guard : bool expr * 'r spec -> 'r spec
      (** falls through to the next case unless the condition holds;
          expresses when-clauses, non-variable field patterns, and
          the [check()] qualifier *)
  | Let : 'a expr * ('a expr -> 'r spec) -> 'r spec
      (** bind a computed value once in generated code ([bind()] and
          [map()] qualifiers) *)
  | SaveOffset : (int expr -> 'r spec) -> 'r spec
      (** binds the number of bits consumed so far
          ([save_offset_to()]) *)
  | Seek : size * 'r spec -> 'r spec
      (** set the absolute bit position (the [offset()] qualifier);
          [All] is invalid here *)
  | Matched : (Bitstring.t expr -> 'r spec) -> 'r spec
      (** binds the portion of the subject matched so far —
          [(data, off, consumed)] — which is what case [as]-aliases
          denote *)

(** Construction fields carry value expressions; construction
    introduces no bindings. *)
type cfield =
  | CBit of bool expr
  | CInt of int_desc * int expr
  | CInt32 of endian * int32 expr
  | CInt64 of int64_desc * int64 expr
  | CString of size * string expr
      (** writes the whole string; the declared size is used by the
          static fast path and the caller's [~expect] total *)
  | CBits of Bitstring.t expr

$val match_ :
  'r. Bitstring.t expr -> 'r spec list -> default:(unit -> 'r) expr ->
  'r expr

$val construct_ :
  loc:string * int * int -> ?expect:int expr -> cfield list ->
  Bitstring.t expr
(** [loc] is [(file, line, char)] for [Construct_failure]; [expect],
    when given, asserts the result's total bit length, raising [Exit]
    on mismatch (mirroring the classic ppx's final check). *)
