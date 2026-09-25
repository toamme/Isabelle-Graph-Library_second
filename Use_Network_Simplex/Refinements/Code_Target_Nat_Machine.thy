section \<open>Serialising \<open>nat\<close> to a 64-bit machine integer\<close>

theory Code_Target_Nat_Machine
  imports "HOL-Library.Code_Target_Nat" "HOL-Imperative_HOL.Array"
begin

text \<open>
  By default \<^typ>\<open>nat\<close> is code-generated through \<^typ>\<open>integer\<close> and lands on SML's
  \<open>IntInf.int\<close>, so every array index is an unbounded integer: each access unboxes and converts,
  and each loop step allocates a fresh box for the counter.  This theory serialises \<^typ>\<open>nat\<close>
  to SML's native \<open>int\<close> instead, while leaving \<^typ>\<open>int\<close> --- and hence every flow, cost,
  capacity, balance and potential --- on \<open>IntInf.int\<close>, where the exactness of the arithmetic is
  what the correctness proofs rest on.

  \<^bold>\<open>64 bits, and \<open>Int.int\<close> rather than a \<open>word\<close> type.\<close> \<open>build.sh\<close> compiles the driver with
  MLton's \<open>-default-type int64\<close>, and that flag rebinds the STRUCTURE \<open>Int\<close> itself, not merely
  the defaulting of un-annotated literals --- checked directly against this exact build
  (\<open>mlton -default-type int64\<close>, then \<^verbatim>\<open>Int.precision\<close> and \<^verbatim>\<open>Int.maxInt\<close> printed at run time):
  \<open>Int.precision = 64\<close>, \<open>Int.maxInt = 9223372036854775807 = 2\<^sup>6\<^sup>3\<close>\<open>-\<close>\<open>1\<close>. An earlier version of this
  theory used \<open>Word64.word\<close> instead, reasoning that indices are never negative so the sign bit
  \<open>Int.int\<close> spends is wasted; that reasoning was sound but no longer matters at this width, since
  either choice leaves nine orders of magnitude of headroom past what any legal instance needs
  (see the bound below). \<open>Int.int\<close> wins instead because it is EXACTLY the index/size type
  \<^verbatim>\<open>Array.sub\<close>/\<^verbatim>\<open>Array.update\<close>/\<^verbatim>\<open>Array.array\<close> already take --- so serialising \<^typ>\<open>nat\<close> to it
  removes the \<open>Word64.toInt\<close>/\<open>Word64.fromInt\<close> conversion at every array access, not just its risk.
  It also restores CHECKED arithmetic: SML's \<open>Int\<close> operations raise \<open>Overflow\<close> on overflow, where
  \<open>Word64\<close> wraps silently, so a magnitude violation of the bound below (were one ever to occur)
  fails loudly at the point it happens rather than corrupting an array index.

  \<^bold>\<open>Landmine: must print as the QUALIFIED \<open>Int.int\<close>, never the bare \<open>int\<close>.\<close> HOL's own \<^typ>\<open>int\<close>
  type --- unrelated to \<^typ>\<open>nat\<close>, but compiled into the SAME generated module --- becomes a
  local \<^verbatim>\<open>datatype int = Int_of_integer of IntInf.int\<close> inside \<open>DIMACS_Solver_Code\<close>'s own
  signature, which SHADOWS the bare identifier \<open>int\<close> for everything printed after it in that
  scope. An earlier version of this theory printed \<^typ>\<open>nat\<close> as bare \<open>"int"\<close>; it type-checked at
  the Isabelle level (\<open>code_printing\<close> does not typecheck the target-language text) but MLton
  rejected the generated \<open>DIMACS_Solver_Code.sml\<close> --- confirmed with
  \<open>mlton -stop tc DIMACS_Solver_Code.sml\<close>, e.g. \<open>isqrt_iter\<close>'s \<open>(0 : int)\<close> disagreeing with what
  \<open>Int.+\<close>/\<open>Int.<\<close> actually return (\<open>Int.int\<close>). The qualified path \<open>Int.int\<close> is unaffected because
  the shadowing only rebinds the bare alias, not the structure name \<open>Int\<close> itself. \<open>Nat_Machine\<close>
  and \<open>Array_Machine\<close> are emitted as separate top-level structures BEFORE that shadowing
  declaration, so their own signatures may safely say bare \<open>int\<close> --- the risk is only in text
  \<open>code_printing\<close> inlines INTO \<open>DIMACS_Solver_Code\<close>'s own body (every literal/annotation below).

  \<^bold>\<open>This is a trusted serialisation, not a theorem.\<close>  \<^typ>\<open>nat\<close> is unbounded in HOL and \<open>int\<close> is
  not, so the two agree only as long as no \<^typ>\<open>nat\<close> the program actually computes exceeds
  \<open>2\<^sup>6\<^sup>3\<close>\<open>-\<close>\<open>1\<close>. Nothing here proves that; it is an assumption, and it is the only one the
  executable pipeline adds beyond the code generator itself.  What justifies it:

    \<^item> in the sources, \<^typ>\<open>nat\<close> is used only for array indices, for the sizes \<open>m\<close> and \<open>n\<close>, and
      for counts derived from them (\<open>k_slack\<close>, \<open>red_m = m + k_slack + 1\<close>,
      \<open>red_steps = m + max 1 n\<close>, \<open>slack_count\<close>, \<open>slack_arc\<close>, \<open>ns_arcs = red_m + n\<close>).  Every
      quantity lives in the locale's abstract ring type \<open>'n\<close>, and no coercion between the two
      exists --- so the type discipline itself keeps magnitudes out of the index world;
    \<^item> nats are never multiplied, so they are closed under the operations that occur here at
      \<open>O(m + n)\<close>. Checked directly against the generated file, not just by name: there is exactly
      one multiplication in the whole of \<open>DIMACS_Solver_Code.sml\<close>, and it is \<open>IntInf.*\<close> (the
      value type), never the index type;
    \<^item> the DIMACS spec itself bounds \<open>n, m \<le> 2\<^sup>3\<^sup>1\<close>\<open>-\<close>\<open>1\<close> (the \<open>p min\<close> line), and the parser enforces
      exactly that bound, nothing tighter --- so no artificial cap on the input can be assumed here.
      The graph the algorithms actually run on is the REDUCTION's, not the DIMACS input's --- one
      more vertex, up to \<open>n\<close> more (slack) edges --- so the quantity that must fit is
      \<open>red_m = m + k_slack + 1 \<le> m + n + 1\<close>, not \<open>m\<close> or \<open>n\<close> alone; and the widest count actually
      computed as a \<^typ>\<open>nat\<close> is \<open>ns_arcs = red_m + n \<le> m + 2n + 1\<close>. Against the spec bound that is
      \<open>\<le> 3 \<cdot> (2\<^sup>3\<^sup>1\<close>\<open>-\<close>\<open>1) + 2 \<approx> 2\<^sup>3\<^sup>2\<close>\<open>\<^sup>.\<^sup>5\<^sup>8\<close> --- comfortably inside \<open>2\<^sup>6\<^sup>3\<close>\<open>-\<close>\<open>1\<close>, a headroom factor on
      the order of two billion, not a percentage. The verified network-simplex fallback adds no
      further vertex on top of that: its root is chosen from the graph it is given, not
      synthesised fresh.

  The first two are properties of the generated code rather than of this theory, so they are
  re-checked mechanically on every build by \<open>check_index_discipline.py\<close>, against the printed SML
  text rather than the pre-serialisation Isabelle constant names (\<open>times_nat\<close>, \<open>nat_of_integer\<close>)
  --- \<open>code_printing\<close> below replaces the latter with the former at every use site, so a check for
  the old names would never fire either way. If the check ever fails --- a nat multiplication
  appears, or something coerces an unbounded value into an index --- this serialisation stops
  being justified and must be removed.

  \<^bold>\<open>Scope of this change.\<close> This theory is the Isabelle code-generation side only: it fixes what
  \<^typ>\<open>nat\<close> compiles to inside \<open>DIMACS_Solver_Code.sml\<close>. The hand-written driver
  (\<open>mcf_main.sml\<close>, which currently declares its node/arc-endpoint arrays as \<open>Word32.word array\<close>)
  and the oracle adaptor (\<open>mcf_oracle_adaptor.sml\<close>) still assume \<open>Word32\<close> at the boundary and must
  be updated separately to match before the pipeline compiles and links end to end again ---
  tracked, not done here. The C oracle's own narrow/wide (\<open>int\<close>/\<open>int64_t\<close>/\<open>__int128\<close>) dispatch in
  \<open>mcf_dispatch.cc\<close> is untouched by this change and keeps its narrowing: that split exists for the
  untrusted solver's performance, is unrelated to what the verified checker's own indices are
  serialised to, and nothing above argues for changing it.
\<close>

subsection \<open>Helper operations\<close>

text \<open>HOL's \<open>div\<close> and \<open>mod\<close> are total, returning \<^term>\<open>0::nat\<close> at a zero divisor. SML's raise, so
      those two are routed through a small module rather than printed inline. Subtraction is
      plain \<open>Int.-\<close>, unguarded: no site in the generated code calls
      \<open>(-) :: nat \<Rightarrow> nat \<Rightarrow> nat\<close> with the subtrahend exceeding the minuend, so the truncation case
      of HOL's \<open>nat\<close> subtraction is never actually exercised, and guarding for it is dead weight,
      not a correctness requirement.\<close>

code_printing code_module Nat_Machine \<rightharpoonup> (SML)
\<open>structure Nat_Machine : sig
  val divide : int * int -> int
  val modulo : int * int -> int
end = struct
  (* HOL makes division by zero total, with m div 0 = 0 and m mod 0 = m *)
  fun divide (m, n) = if n = 0 then 0 else Int.div (m, n)
  fun modulo (m, n) = if n = 0 then m else Int.mod (m, n)
end
\<close>

text \<open>An update that hands the array back.  \<open>Array.update\<close> returns unit, whereas
      \<^const>\<open>Array.upd\<close> returns the array, and its argument order differs from the one the
      constant below takes; a serialisation cannot reorder placeholders, so the adjustment is
      made here.  Nothing here converts the index: with \<^typ>\<open>nat\<close> serialised directly to \<open>int\<close>, it
      IS the type \<^verbatim>\<open>Array.update\<close> already expects.\<close>

code_printing code_module Array_Machine \<rightharpoonup> (SML)
\<open>structure Array_Machine : sig
  val upd : 'a array * int * 'a -> 'a array
end = struct
  fun upd (a, i, x) = (Array.update (a, i, x); a)
end
\<close>

subsection \<open>The serialisation\<close>

text \<open>\<open>nat_of_integer\<close>/\<open>integer_of_nat\<close> go through \<open>LargeInt\<close>, which MLton's Basis makes the
      same type as \<open>IntInf\<close>; \<open>Int.fromLarge\<close>/\<open>Int.toLarge\<close> are the Basis's own checked
      conversions between the sized \<open>Int\<close> and \<open>LargeInt\<close> --- \<open>fromLarge\<close> raises \<open>Overflow\<close> if the
      value does not fit in 64 bits, which is exactly the loud failure mode this serialisation
      prefers over \<open>Word64\<close>'s silent wraparound.\<close>

code_printing
  type_constructor nat \<rightharpoonup> (SML) "Int.int"
| constant "0 :: nat" \<rightharpoonup> (SML) "(0 : Int.int)"
| constant "1 :: nat" \<rightharpoonup> (SML) "(1 : Int.int)"
| constant Suc \<rightharpoonup> (SML) "Int.+/ ((_),/ (1 : Int.int))"
| constant "(+) :: nat \<Rightarrow> nat \<Rightarrow> nat" \<rightharpoonup> (SML) "Int.+/ ((_),/ (_))"
| constant "(-) :: nat \<Rightarrow> nat \<Rightarrow> nat" \<rightharpoonup> (SML) "Int.-/ ((_),/ (_))"
| constant "(*) :: nat \<Rightarrow> nat \<Rightarrow> nat" \<rightharpoonup> (SML) "Int.*/ ((_),/ (_))"
| constant "(div) :: nat \<Rightarrow> nat \<Rightarrow> nat" \<rightharpoonup> (SML) "Nat'_Machine.divide/ ((_),/ (_))"
| constant "(mod) :: nat \<Rightarrow> nat \<Rightarrow> nat" \<rightharpoonup> (SML) "Nat'_Machine.modulo/ ((_),/ (_))"
| constant "HOL.equal :: nat \<Rightarrow> nat \<Rightarrow> bool" \<rightharpoonup> (SML) "!((_ : Int.int) = _)"
| constant "(\<le>) :: nat \<Rightarrow> nat \<Rightarrow> bool" \<rightharpoonup> (SML) "Int.<=/ ((_),/ (_))"
| constant "(<) :: nat \<Rightarrow> nat \<Rightarrow> bool" \<rightharpoonup> (SML) "Int.</ ((_),/ (_))"
| constant nat_of_integer \<rightharpoonup> (SML) "Int.fromLarge"
| constant integer_of_nat \<rightharpoonup> (SML) "Int.toLarge"

code_reserved (SML) Nat_Machine Array_Machine

subsection \<open>Array access without a conversion\<close>

text \<open>\<^const>\<open>Array.nth\<close> and friends are generated through \<^const>\<open>Array.nth'\<close>, which takes an
      \<^typ>\<open>integer\<close>; with the serialisation above that would round-trip the index through
      \<open>IntInf\<close> on every access, which is exactly the cost this theory exists to remove.  These
      wrappers take the \<^typ>\<open>nat\<close> directly.  Each is definitionally the original operation, so
      the code equations below are trivially sound --- the content is in the printing.\<close>

definition nth_machine :: "'a::heap array \<Rightarrow> nat \<Rightarrow> 'a Heap" where
  [simp]: "nth_machine = Array.nth"

definition upd_machine :: "'a::heap array \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a array Heap" where
  [simp]: "upd_machine a i x = Array.upd i x a"

definition new_machine :: "nat \<Rightarrow> 'a::heap \<Rightarrow> 'a array Heap" where
  [simp]: "new_machine = Array.new"

definition len_machine :: "'a::heap array \<Rightarrow> nat Heap" where
  [simp]: "len_machine = Array.len"

definition make_machine :: "nat \<Rightarrow> (nat \<Rightarrow> 'a::heap) \<Rightarrow> 'a array Heap" where
  [simp]: "make_machine = Array.make"

lemma nth_machine_code [code]: "Array.nth a i = nth_machine a i" by simp
lemma upd_machine_code [code]: "Array.upd i x a = upd_machine a i x" by simp
lemma new_machine_code [code]: "Array.new n x = new_machine n x" by simp
lemma len_machine_code [code]: "Array.len a = len_machine a" by simp
lemma make_machine_code [code]: "Array.make n f = make_machine n f" by simp

text \<open>Every one of these five crosses the \<^typ>\<open>nat\<close>/\<open>Array\<close> boundary discussed above, but none of
      them inserts a conversion any more: \<^typ>\<open>nat\<close> IS \<open>int\<close> now, the same type
      \<^verbatim>\<open>Array.sub\<close>/\<^verbatim>\<open>Array.array\<close>/\<^verbatim>\<open>Array.length\<close>/\<^verbatim>\<open>Array.tabulate\<close> already use, so the index/size
      passes straight through in both directions. \<open>make_machine\<close> no longer needs to re-wrap its
      callback either: \<^verbatim>\<open>Array.tabulate\<close> calls it with the raw \<open>int\<close> position, which is now
      exactly the \<^typ>\<open>nat\<close> the HOL type says it receives, not a distinct type needing
      \<open>Word64.fromInt\<close> in between.\<close>

code_printing
  constant nth_machine \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.sub/ ((_),/ (_)))"
| constant upd_machine \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array'_Machine.upd/ ((_),/ (_),/ (_)))"
| constant new_machine \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.array/ ((_),/ (_)))"
| constant len_machine \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.length/ _)"
| constant make_machine \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.tabulate/ ((_),/ (_)))"

end
