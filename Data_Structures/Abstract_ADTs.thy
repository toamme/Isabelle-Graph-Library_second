theory Abstract_ADTs
  imports Complex_Main
begin

section ‹Abstract interfaces used by the flow algorithms›

text ‹The data-structure locales the imperative flow algorithms are written against, and the
      numeric homomorphism that connects an executable value type to the real-valued
      specification.  They are collected here because none of them mentions graphs or flows: they
      are ordinary abstract datatypes, fixed by their operations and laws, and any implementation
      satisfying the laws may be plugged in.›

subsection ‹Arrays and sets›

locale abstract_array =
fixes K::"'a set"
and abstract_array_invar::"'array ⇒ bool"
and abstract_array_upd::"'array ⇒ 'a ⇒ 'b ⇒ 'array"
and abstract_array_lookup::"'array ⇒ 'a ⇒ 'b"
assumes abstract_array_upd:
"⋀ A k v. 
 ⟦abstract_array_invar A; k ∈ K⟧ ⟹
abstract_array_lookup (abstract_array_upd A k v) =
(abstract_array_lookup A) (k := v)"
and abstract_array_upd_invar:
"⋀ A k v. ⟦abstract_array_invar A; k ∈ K⟧ 
⟹ abstract_array_invar (abstract_array_upd A k v)"

text ‹A set datatype whose elements are drawn from a fixed universe @{term U}: the abstraction of
      any well-formed set is a subset of @{term U}, and the operations behave as expected.›

locale abstract_set =
  fixes U :: "'a set"
  and abstract_set_invar :: "'set ⇒ bool"
  and abstract_set_abstract :: "'set ⇒ 'a set"
  and abstract_set_empty :: "'set"
  and abstract_set_insert :: "'a ⇒ 'set ⇒ 'set"
  and abstract_set_delete :: "'a ⇒ 'set ⇒ 'set"
  and abstract_set_isin :: "'set ⇒ 'a ⇒ bool"
  assumes abstract_set_universe:
      "⋀ S. abstract_set_invar S ⟹ abstract_set_abstract S ⊆ U"
  and abstract_set_empty:
      "abstract_set_invar abstract_set_empty"
      "abstract_set_abstract abstract_set_empty = {}"
  and abstract_set_insert:
      "⋀ x S. ⟦abstract_set_invar S; x ∈ U⟧ ⟹ abstract_set_invar (abstract_set_insert x S)"
      "⋀ x S. ⟦abstract_set_invar S; x ∈ U⟧ ⟹
          abstract_set_abstract (abstract_set_insert x S) = insert x (abstract_set_abstract S)"
  and abstract_set_delete:
      "⋀ x S. abstract_set_invar S ⟹ abstract_set_invar (abstract_set_delete x S)"
      "⋀ x S. abstract_set_invar S ⟹
          abstract_set_abstract (abstract_set_delete x S) = abstract_set_abstract S - {x}"
  and abstract_set_isin:
      "⋀ x S. abstract_set_invar S ⟹ abstract_set_isin S x ⟷ x ∈ abstract_set_abstract S"

locale iterable_set =
  fixes iterable_set_invar::"'iset ⇒ bool"
  and iterable_set_abstract::"'iset ⇒ 'a set"
  and current_element::"'iset ⇒ 'a"
  and has_current::"'iset ⇒ bool"
  and iterated::"'iset ⇒ 'a set"
  and remaining::"'iset ⇒ 'a set"
  and move_on::"'iset ⇒ 'iset"
assumes
  iterable_set_abstract:
    "⋀ S. iterable_set_invar S ⟹
      iterated S ∩ remaining S = {}"
    "⋀ S. iterable_set_invar S ⟹
      iterated S ∪ remaining S = iterable_set_abstract S"
  and has_current:
   "⋀ S. iterable_set_invar S ⟹ has_current S ⟷ remaining S ≠ {}" 
  and current_element:
    "⋀ S. ⟦iterable_set_invar S; remaining S ≠ {}⟧ ⟹
         current_element S ∈ remaining S"
  and move_on:
    "⋀ S. ⟦iterable_set_invar S; remaining S ≠ {}⟧ ⟹
      iterable_set_abstract (move_on S) = iterable_set_abstract S"
    "⋀ S. ⟦iterable_set_invar S; remaining S ≠ {}⟧ ⟹
      remaining (move_on S) = remaining S - {current_element S}"
    "⋀ S. ⟦iterable_set_invar S; remaining S ≠ {}⟧ ⟹
      iterated (move_on S) = iterated S ∪ {current_element S}"
  and move_on_invar:
    "⋀ S. ⟦iterable_set_invar S; remaining S ≠ {}⟧ ⟹
      iterable_set_invar (move_on S)"



section ‹An Indexed Collection of Iterable Sets›

text ‹The graph implementation is now fully abstract. Rather than exposing an array of iterable
      sets (an @{locale abstract_array} into @{locale iterable_set}s), we fix a single \emph{indexed
      collection of iterable sets}: every operation first takes the collection and then the index
      (a vertex). This fuses the former array lookup with the iterator cursor, and adds an
      @{term idx_reset} primitive that rewinds the cursor at one index back to the beginning. The
      concrete two-array-of-iterators representation is no longer visible to the algorithm.›

locale indexed_iterable_set =
  fixes idx_invar     :: "'coll ⇒ bool"
    and idx_abstract  :: "'coll ⇒ 'i ⇒ 'a set"
    and idx_current   :: "'coll ⇒ 'i ⇒ 'a"
    and idx_has       :: "'coll ⇒ 'i ⇒ bool"
    and idx_iterated  :: "'coll ⇒ 'i ⇒ 'a set"
    and idx_remaining :: "'coll ⇒ 'i ⇒ 'a set"
    and idx_move      :: "'coll ⇒ 'i ⇒ 'coll"
    and idx_reset     :: "'coll ⇒ 'i ⇒ 'coll"
    and K             :: "'i set"
  assumes idx_partition_disjoint:
      "⋀C i. ⟦idx_invar C; i ∈ K⟧ ⟹ idx_iterated C i ∩ idx_remaining C i = {}"
    and idx_partition_union:
      "⋀C i.⟦idx_invar C; i ∈ K⟧  ⟹ idx_iterated C i ∪ idx_remaining C i = idx_abstract C i"
    and idx_has:
      "⋀C i. ⟦idx_invar C; i ∈ K⟧  ⟹ idx_has C i ⟷ idx_remaining C i ≠ {}"
    and idx_current:
      "⋀C i. ⟦idx_invar C; i ∈ K; idx_remaining C i ≠ {}⟧ ⟹ idx_current C i ∈ idx_remaining C i"
    and idx_move_invar:
      "⋀C i. ⟦idx_invar C; i ∈ K⟧ ⟹ idx_invar (idx_move C i)"
    and idx_move_abstract:
      "⋀C i j. ⟦idx_invar C; i ∈ K; idx_remaining C i ≠ {}⟧ ⟹ idx_abstract (idx_move C i) j = idx_abstract C j"
    and idx_move_remaining:
      "⋀C i. ⟦idx_invar C; i ∈ K; idx_remaining C i ≠ {}⟧ ⟹ idx_remaining (idx_move C i) i = idx_remaining C i - {idx_current C i}"
    and idx_move_iterated:
      "⋀C i. ⟦idx_invar C; i ∈ K; idx_remaining C i ≠ {}⟧ ⟹ idx_iterated (idx_move C i) i = idx_iterated C i ∪ {idx_current C i}"
    and idx_move_remaining_other:
      "⋀C i j. ⟦idx_invar C;i ∈ K; idx_remaining C i ≠ {}; j ≠ i⟧ ⟹ idx_remaining (idx_move C i) j = idx_remaining C j"
    and idx_move_iterated_other:
      "⋀C i j. ⟦idx_invar C;i ∈ K; idx_remaining C i ≠ {}; j ≠ i⟧ ⟹ idx_iterated (idx_move C i) j = idx_iterated C j"
    and idx_reset_invar:
      "⋀C i. ⟦idx_invar C; i ∈ K⟧ ⟹ idx_invar (idx_reset C i)"
    and idx_reset_abstract:
      "⋀C i j. ⟦idx_invar C; i ∈ K⟧ ⟹ idx_abstract (idx_reset C i) j = idx_abstract C j"
    and idx_reset_iterated:
      "⋀C i. ⟦idx_invar C; i ∈ K⟧ ⟹ idx_iterated (idx_reset C i) i = {}"
    and idx_reset_remaining:
      "⋀C i. ⟦idx_invar C; i ∈ K⟧ ⟹ idx_remaining (idx_reset C i) i = idx_abstract C i"
    and idx_reset_remaining_other:
      "⋀C i j. ⟦idx_invar C; i ∈ K; j ≠ i⟧ ⟹ idx_remaining (idx_reset C i) j = idx_remaining C j"
    and idx_reset_iterated_other:
      "⋀C i j. ⟦idx_invar C; i ∈ K; j ≠ i⟧ ⟹ idx_iterated (idx_reset C i) j = idx_iterated C j"

subsection ‹A ring embedding into the reals›

text ‹A ring embedding of the executable value type @{typ 'n} into the reals: an order-preserving
      ring homomorphism. Instantiated by @{term id} for the real program and by @{const of_int} for the
      integer program, it lets us certify the generic @{typ 'n}-program against the real specification by
      reading every executable flow @{term f} through @{term ‹h ∘ f›}.›

locale real_embedding =
  fixes h :: "'n :: linordered_idom ⇒ real"
  assumes h_add:  "⋀a b. h (a + b) = h a + h b"
      and h_mult: "⋀a b. h (a * b) = h a * h b"
      and h_one:  "h 1 = 1"
      and h_strict_mono: "⋀a b. a < b ⟹ h a < h b"
begin

lemma h_zero [simp]: "h 0 = 0"
  using h_add[of 0 0] by simp

lemma h_uminus [simp]: "h (- a) = - h a"
  using h_add[of a "- a"] by simp

lemma h_diff [simp]: "h (a - b) = h a - h b"
  using h_add[of a "- b"] by simp

lemma h_less_iff [simp]: "h a < h b ⟷ a < b"
  by (metis h_strict_mono linorder_less_linear order_less_asym order_less_irrefl)

lemma h_le_iff [simp]: "h a ≤ h b ⟷ a ≤ b"
  by (metis h_less_iff not_less)

lemma h_eq_iff [simp]: "h a = h b ⟷ a = b"
  by (metis h_le_iff order_antisym order_refl)

lemma h_one' [simp]: "h 1 = 1" by (rule h_one)

lemma h_neg_one [simp]: "h (- 1) = - 1" by simp

lemma h_mono: "a ≤ b ⟹ h a ≤ h b" by simp

lemma h_nonneg: "0 ≤ a ⟹ 0 ≤ h a" using h_le_iff[of 0 a] by simp

lemma h_less_zero [simp]: "h a < 0 ⟷ a < 0" using h_less_iff[of a 0] by simp
lemma h_zero_less [simp]: "0 < h a ⟷ 0 < a" using h_less_iff[of 0 a] by simp
lemma h_le_zero  [simp]: "h a ≤ 0 ⟷ a ≤ 0" using h_le_iff[of a 0] by simp
lemma h_zero_le  [simp]: "0 ≤ h a ⟷ 0 ≤ a" using h_le_iff[of 0 a] by simp
lemma h_eq_zero  [simp]: "h a = 0 ⟷ a = 0" using h_eq_iff[of a 0] by simp
lemma h_eq_neg1  [simp]: "h a = - 1 ⟷ a = - 1" using h_eq_iff[of a "- 1"] by simp
lemma h_neg1_eq  [simp]: "- 1 = h a ⟷ a = - 1" by (metis h_eq_neg1)

lemma h_min [simp]: "h (min a b) = min (h a) (h b)"
  by (cases "a ≤ b") (simp_all add: min_def)

lemma h_max [simp]: "h (max a b) = max (h a) (h b)"
  by (cases "a ≤ b") (simp_all add: max_def)

lemma h_sum: "h (sum f A) = (∑a∈A. h (f a))"
  by (induction A rule: infinite_finite_induct) (simp_all add: h_add)

end

end
