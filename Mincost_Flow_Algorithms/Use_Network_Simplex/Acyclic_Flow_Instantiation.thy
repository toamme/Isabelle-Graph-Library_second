theory Acyclic_Flow_Instantiation
  imports Mincost_Flow_Algorithms.Acyclic_Flow
begin

section \<open>A concrete indexed collection of iterable edge-sets\<close>

text \<open>We give a concrete, purely functional implementation of the abstract
      @{locale indexed_iterable_set}. Inspired by the compressed-sparse-row layout, the collection
      keeps a single flat \emph{edge array} @{term csr_edges} together with three \emph{pointer
      arrays} indexed by the vertex: for every vertex @{term v} a lower pointer @{term csr_lo}
      marks where its contiguous region in the edge array begins, an upper pointer @{term csr_hi}
      marks where it ends (exclusive), and a cursor @{term csr_cur} points at the current,
      not-yet-iterated edge inside that region. The regions of distinct vertices must not overlap,
      and all edges in the flat array are distinct.

      The iterable set at a vertex \<open>v\<close> is exactly the set of edges stored in the index range
      \<open>[csr_lo v, csr_hi v)\<close>; the already-iterated edges are those before the cursor, the index range
      \<open>[csr_lo v, csr_cur v)\<close>, and the remaining ones those from the cursor on, the index range
      \<open>[csr_cur v, csr_hi v)\<close>. Advancing the cursor by one implements @{term idx_move}, resetting it
      back to @{term csr_lo} implements @{term idx_reset}.\<close>

record 'e edge_csr =
  csr_edges :: "'e list"
  csr_lo    :: "nat list"
  csr_hi    :: "nat list"
  csr_cur   :: "nat list"

text \<open>The number of vertices is the common length of the three pointer arrays; a vertex out of that
      range indexes an empty region.\<close>

definition csr_n :: "'e edge_csr \<Rightarrow> nat" where
  "csr_n C = length (csr_cur C)"

text \<open>Position ranges of a vertex inside the flat edge array: the whole region, the iterated prefix
      and the remaining suffix. Out-of-range vertices get the empty range.\<close>

definition csr_seg :: "'e edge_csr \<Rightarrow> nat \<Rightarrow> nat set" where
  "csr_seg C v = (if v < csr_n C then {csr_lo C ! v ..< csr_hi C ! v} else {})"

definition csr_seg_it :: "'e edge_csr \<Rightarrow> nat \<Rightarrow> nat set" where
  "csr_seg_it C v = (if v < csr_n C then {csr_lo C ! v ..< csr_cur C ! v} else {})"

definition csr_seg_rm :: "'e edge_csr \<Rightarrow> nat \<Rightarrow> nat set" where
  "csr_seg_rm C v = (if v < csr_n C then {csr_cur C ! v ..< csr_hi C ! v} else {})"

text \<open>Well-formedness: the pointer arrays agree in length, the flat edge array has no repeats, every
      cursor sits between its bounds which in turn stay inside the edge array, and distinct vertices
      own disjoint regions.\<close>

definition csr_invar :: "'e edge_csr \<Rightarrow> bool" where
  "csr_invar C \<longleftrightarrow>
     length (csr_lo C) = csr_n C \<and>
     length (csr_hi C) = csr_n C \<and>
     distinct (csr_edges C) \<and>
     (\<forall>v < csr_n C. csr_lo C ! v \<le> csr_cur C ! v \<and>
                     csr_cur C ! v \<le> csr_hi C ! v \<and>
                     csr_hi C ! v \<le> length (csr_edges C)) \<and>
     (\<forall>u < csr_n C. \<forall>v < csr_n C. u \<noteq> v \<longrightarrow>
         {csr_lo C ! u ..< csr_hi C ! u} \<inter> {csr_lo C ! v ..< csr_hi C ! v} = {})"

subsection \<open>The abstract-view operations\<close>

definition csr_abstract :: "'e edge_csr \<Rightarrow> nat \<Rightarrow> 'e set" where
  "csr_abstract C v = (!) (csr_edges C) ` csr_seg C v"

definition csr_iterated :: "'e edge_csr \<Rightarrow> nat \<Rightarrow> 'e set" where
  "csr_iterated C v = (!) (csr_edges C) ` csr_seg_it C v"

definition csr_remaining :: "'e edge_csr \<Rightarrow> nat \<Rightarrow> 'e set" where
  "csr_remaining C v = (!) (csr_edges C) ` csr_seg_rm C v"

definition csr_has :: "'e edge_csr \<Rightarrow> nat \<Rightarrow> bool" where
  "csr_has C v \<longleftrightarrow> v < csr_n C \<and> csr_cur C ! v < csr_hi C ! v"

definition csr_current :: "'e edge_csr \<Rightarrow> nat \<Rightarrow> 'e" where
  "csr_current C v = csr_edges C ! (csr_cur C ! v)"

definition csr_move :: "'e edge_csr \<Rightarrow> nat \<Rightarrow> 'e edge_csr" where
  "csr_move C v =
     C\<lparr>csr_cur := (csr_cur C)[v := (if v < csr_n C \<and> csr_cur C ! v < csr_hi C ! v
                                     then Suc (csr_cur C ! v) else csr_cur C ! v)]\<rparr>"

definition csr_reset :: "'e edge_csr \<Rightarrow> nat \<Rightarrow> 'e edge_csr" where
  "csr_reset C v =
     C\<lparr>csr_cur := (csr_cur C)[v := (if v < csr_n C then csr_lo C ! v else csr_cur C ! v)]\<rparr>"

subsection \<open>Selectors of the two updates\<close>

text \<open>Only the cursor array is touched by @{const csr_move} / @{const csr_reset}; the edge array,
      the two bound arrays and the vertex count are untouched.\<close>

lemma csr_move_selectors [simp]:
  "csr_edges (csr_move C v) = csr_edges C"
  "csr_lo (csr_move C v) = csr_lo C"
  "csr_hi (csr_move C v) = csr_hi C"
  "csr_n (csr_move C v) = csr_n C"
  by (simp_all add: csr_move_def csr_n_def)

lemma csr_reset_selectors [simp]:
  "csr_edges (csr_reset C v) = csr_edges C"
  "csr_lo (csr_reset C v) = csr_lo C"
  "csr_hi (csr_reset C v) = csr_hi C"
  "csr_n (csr_reset C v) = csr_n C"
  by (simp_all add: csr_reset_def csr_n_def)

lemma csr_cur_move_at:
  "\<lbrakk>v < csr_n C; csr_cur C ! v < csr_hi C ! v\<rbrakk> \<Longrightarrow> csr_cur (csr_move C v) ! v = Suc (csr_cur C ! v)"
  by (simp add: csr_move_def csr_n_def nth_list_update)

lemma csr_cur_move_neq:
  "w \<noteq> v \<Longrightarrow> csr_cur (csr_move C v) ! w = csr_cur C ! w"
  by (simp add: csr_move_def)

lemma csr_cur_reset_at:
  "v < csr_n C \<Longrightarrow> csr_cur (csr_reset C v) ! v = csr_lo C ! v"
  by (simp add: csr_reset_def csr_n_def nth_list_update)

lemma csr_cur_reset_neq:
  "w \<noteq> v \<Longrightarrow> csr_cur (csr_reset C v) ! w = csr_cur C ! w"
  by (simp add: csr_reset_def)

subsection \<open>Auxiliary facts\<close>

lemma csr_lo_le_hi:
  assumes "csr_invar C" "v < csr_n C"
  shows "csr_lo C ! v \<le> csr_hi C ! v"
proof -
  have "csr_lo C ! v \<le> csr_cur C ! v" "csr_cur C ! v \<le> csr_hi C ! v"
    using assms by (auto simp: csr_invar_def)
  thus ?thesis by linarith
qed

text \<open>Injectivity of reading the flat array on the whole index range (from distinctness).\<close>

lemma csr_inj_on_edges:
  assumes "csr_invar C"
  shows "inj_on ((!) (csr_edges C)) {..< length (csr_edges C)}"
  using assms by (auto simp: csr_invar_def intro!: inj_on_nth)

lemma csr_seg_it_subset_len:
  "csr_invar C \<Longrightarrow> csr_seg_it C v \<subseteq> {..< length (csr_edges C)}"
  by (auto simp: csr_invar_def csr_seg_it_def split: if_splits)

lemma csr_seg_rm_subset_len:
  "csr_invar C \<Longrightarrow> csr_seg_rm C v \<subseteq> {..< length (csr_edges C)}"
  by (auto simp: csr_invar_def csr_seg_rm_def split: if_splits)

text \<open>Two elementary image facts driven by injectivity.\<close>

lemma image_Int_empty_of_inj:
  assumes "inj_on h U" "X \<subseteq> U" "Y \<subseteq> U" "X \<inter> Y = {}"
  shows "h ` X \<inter> h ` Y = {}"
  using assms by (auto dest: inj_onD)

lemma image_atLeastLessThan_minus_first:
  assumes inj: "inj_on ((!) xs) U" and sub: "{a..<b} \<subseteq> U" and ab: "a < b"
  shows "(!) xs ` {a..<b} - {xs ! a} = (!) xs ` {Suc a..<b}"
proof -
  have notin: "xs ! a \<notin> (!) xs ` {Suc a..<b}"
  proof
    assume "xs ! a \<in> (!) xs ` {Suc a..<b}"
    then obtain j where j: "j \<in> {Suc a..<b}" "xs ! a = xs ! j" by auto
    have "a \<in> U" "j \<in> U" using sub ab j by auto
    hence "a = j" using inj j(2) by (auto dest: inj_onD)
    thus False using j(1) by auto
  qed
  have "{a..<b} = insert a {Suc a..<b}" using ab by auto
  hence "(!) xs ` {a..<b} = insert (xs ! a) ((!) xs ` {Suc a..<b})" by simp
  thus ?thesis using notin by auto
qed

subsection \<open>The interpretation\<close>

text \<open>The concrete collection satisfies the abstract @{locale indexed_iterable_set} interface.\<close>

lemma csr_indexed_iterable_set:
  "indexed_iterable_set csr_invar csr_abstract csr_current csr_has
                        csr_iterated csr_remaining csr_move csr_reset K"
proof unfold_locales
  fix C :: "'e edge_csr" and i :: nat
  assume inv: "csr_invar C" and iK: "i \<in> K"
  \<comment> \<open>partition: disjoint\<close>
  show "csr_iterated C i \<inter> csr_remaining C i = {}"
  proof (cases "i < csr_n C")
    case True
    have inj: "inj_on ((!) (csr_edges C)) {..< length (csr_edges C)}"
      using inv by (rule csr_inj_on_edges)
    have "csr_lo C ! i \<le> csr_cur C ! i" "csr_cur C ! i \<le> csr_hi C ! i"
      using inv True by (auto simp: csr_invar_def)
    hence disj_idx: "csr_seg_it C i \<inter> csr_seg_rm C i = {}"
      using True by (auto simp: csr_seg_it_def csr_seg_rm_def)
    show ?thesis
      unfolding csr_iterated_def csr_remaining_def
      by (rule image_Int_empty_of_inj[OF inj csr_seg_it_subset_len[OF inv]
                 csr_seg_rm_subset_len[OF inv] disj_idx])
  next
    case False
    thus ?thesis by (simp add: csr_iterated_def csr_remaining_def csr_seg_it_def csr_seg_rm_def)
  qed
next
  fix C :: "'e edge_csr" and i :: nat
  assume inv: "csr_invar C" and iK: "i \<in> K"
  \<comment> \<open>partition: union\<close>
  show "csr_iterated C i \<union> csr_remaining C i = csr_abstract C i"
  proof (cases "i < csr_n C")
    case True
    have "csr_lo C ! i \<le> csr_cur C ! i" "csr_cur C ! i \<le> csr_hi C ! i"
      using inv True by (auto simp: csr_invar_def)
    hence "csr_seg_it C i \<union> csr_seg_rm C i = csr_seg C i"
      using True by (auto simp: csr_seg_it_def csr_seg_rm_def csr_seg_def)
    thus ?thesis
      by (simp add: csr_iterated_def csr_remaining_def csr_abstract_def image_Un[symmetric])
  next
    case False
    thus ?thesis
      by (simp add: csr_iterated_def csr_remaining_def csr_abstract_def
                    csr_seg_it_def csr_seg_rm_def csr_seg_def)
  qed
next
  fix C :: "'e edge_csr" and i :: nat
  assume inv: "csr_invar C" and iK: "i \<in> K"
  \<comment> \<open>has {\isasymlongleftrightarrow} remaining nonempty\<close>
  show "csr_has C i \<longleftrightarrow> csr_remaining C i \<noteq> {}"
    by (auto simp: csr_has_def csr_remaining_def csr_seg_rm_def)
next
  fix C :: "'e edge_csr" and i :: nat
  assume inv: "csr_invar C" and iK: "i \<in> K" and ne: "csr_remaining C i \<noteq> {}"
  \<comment> \<open>current in remaining\<close>
  have iN: "i < csr_n C" and lt: "csr_cur C ! i < csr_hi C ! i"
    using ne by (auto simp: csr_remaining_def csr_seg_rm_def split: if_splits)
  show "csr_current C i \<in> csr_remaining C i"
    using iN lt by (auto simp: csr_current_def csr_remaining_def csr_seg_rm_def)
next
  fix C :: "'e edge_csr" and i :: nat
  assume inv: "csr_invar C" and iK: "i \<in> K"
  \<comment> \<open>move preserves invar (unconditional)\<close>
  show "csr_invar (csr_move C i)"
    using inv
    by (auto simp: csr_invar_def csr_move_def csr_n_def nth_list_update split: if_splits)
next
  fix C :: "'e edge_csr" and i j :: nat
  assume inv: "csr_invar C" and iK: "i \<in> K" and ne: "csr_remaining C i \<noteq> {}"
  \<comment> \<open>move preserves abstract\<close>
  show "csr_abstract (csr_move C i) j = csr_abstract C j"
    by (simp add: csr_abstract_def csr_seg_def)
next
  fix C :: "'e edge_csr" and i :: nat
  assume inv: "csr_invar C" and iK: "i \<in> K" and ne: "csr_remaining C i \<noteq> {}"
  \<comment> \<open>move: remaining at i\<close>
  have iN: "i < csr_n C" and lt: "csr_cur C ! i < csr_hi C ! i"
    using ne by (auto simp: csr_remaining_def csr_seg_rm_def split: if_splits)
  have inj: "inj_on ((!) (csr_edges C)) {..< length (csr_edges C)}"
    using inv by (rule csr_inj_on_edges)
  have sub: "{csr_cur C ! i ..< csr_hi C ! i} \<subseteq> {..< length (csr_edges C)}"
    using csr_seg_rm_subset_len[OF inv, of i] iN by (simp add: csr_seg_rm_def)
  have key: "(!) (csr_edges C) ` {csr_cur C ! i ..< csr_hi C ! i} - {csr_current C i}
               = (!) (csr_edges C) ` {Suc (csr_cur C ! i) ..< csr_hi C ! i}"
    using image_atLeastLessThan_minus_first[OF inj sub lt] by (simp add: csr_current_def)
  have "csr_remaining (csr_move C i) i = (!) (csr_edges C) ` {Suc (csr_cur C ! i) ..< csr_hi C ! i}"
    using iN by (simp add: csr_remaining_def csr_seg_rm_def csr_cur_move_at[OF iN lt])
  also have "\<dots> = (!) (csr_edges C) ` {csr_cur C ! i ..< csr_hi C ! i} - {csr_current C i}"
    using key by simp
  also have "\<dots> = csr_remaining C i - {csr_current C i}"
    using iN by (simp add: csr_remaining_def csr_seg_rm_def)
  finally show "csr_remaining (csr_move C i) i = csr_remaining C i - {csr_current C i}" .
next
  fix C :: "'e edge_csr" and i :: nat
  assume inv: "csr_invar C" and iK: "i \<in> K" and ne: "csr_remaining C i \<noteq> {}"
  \<comment> \<open>move: iterated at i\<close>
  have iN: "i < csr_n C" and lt: "csr_cur C ! i < csr_hi C ! i"
    using ne by (auto simp: csr_remaining_def csr_seg_rm_def split: if_splits)
  have le: "csr_lo C ! i \<le> csr_cur C ! i"
    using inv iN by (auto simp: csr_invar_def)
  have seg: "{csr_lo C ! i ..< Suc (csr_cur C ! i)}
               = insert (csr_cur C ! i) {csr_lo C ! i ..< csr_cur C ! i}"
    using le by auto
  have "csr_iterated (csr_move C i) i = (!) (csr_edges C) ` {csr_lo C ! i ..< Suc (csr_cur C ! i)}"
    using iN by (simp add: csr_iterated_def csr_seg_it_def csr_cur_move_at[OF iN lt])
  also have "\<dots> = insert (csr_current C i) ((!) (csr_edges C) ` {csr_lo C ! i ..< csr_cur C ! i})"
    by (simp add: seg csr_current_def)
  also have "\<dots> = csr_iterated C i \<union> {csr_current C i}"
    using iN by (auto simp: csr_iterated_def csr_seg_it_def)
  finally show "csr_iterated (csr_move C i) i = csr_iterated C i \<union> {csr_current C i}" .
next
  fix C :: "'e edge_csr" and i j :: nat
  assume inv: "csr_invar C" and iK: "i \<in> K" and ne: "csr_remaining C i \<noteq> {}" and neq: "j \<noteq> i"
  \<comment> \<open>move: remaining at other index\<close>
  show "csr_remaining (csr_move C i) j = csr_remaining C j"
    by (simp add: csr_remaining_def csr_seg_rm_def csr_cur_move_neq[OF neq])
next
  fix C :: "'e edge_csr" and i j :: nat
  assume inv: "csr_invar C" and iK: "i \<in> K" and ne: "csr_remaining C i \<noteq> {}" and neq: "j \<noteq> i"
  \<comment> \<open>move: iterated at other index\<close>
  show "csr_iterated (csr_move C i) j = csr_iterated C j"
    by (simp add: csr_iterated_def csr_seg_it_def csr_cur_move_neq[OF neq])
next
  fix C :: "'e edge_csr" and i :: nat
  assume inv: "csr_invar C" and iK: "i \<in> K"
  \<comment> \<open>reset preserves invar\<close>
  show "csr_invar (csr_reset C i)"
    using inv csr_lo_le_hi[OF inv]
    by (auto simp: csr_invar_def csr_reset_def csr_n_def nth_list_update split: if_splits)
next
  fix C :: "'e edge_csr" and i j :: nat
  assume inv: "csr_invar C" and iK: "i \<in> K"
  \<comment> \<open>reset preserves abstract\<close>
  show "csr_abstract (csr_reset C i) j = csr_abstract C j"
    by (simp add: csr_abstract_def csr_seg_def)
next
  fix C :: "'e edge_csr" and i :: nat
  assume inv: "csr_invar C" and iK: "i \<in> K"
  \<comment> \<open>reset: iterated at i is empty\<close>
  show "csr_iterated (csr_reset C i) i = {}"
  proof (cases "i < csr_n C")
    case True
    thus ?thesis
      by (simp add: csr_iterated_def csr_seg_it_def csr_cur_reset_at[OF True])
  next
    case False
    thus ?thesis by (simp add: csr_iterated_def csr_seg_it_def)
  qed
next
  fix C :: "'e edge_csr" and i :: nat
  assume inv: "csr_invar C" and iK: "i \<in> K"
  \<comment> \<open>reset: remaining at i is the whole region\<close>
  show "csr_remaining (csr_reset C i) i = csr_abstract C i"
  proof (cases "i < csr_n C")
    case True
    thus ?thesis
      by (simp add: csr_remaining_def csr_seg_rm_def csr_abstract_def csr_seg_def
                    csr_cur_reset_at[OF True])
  next
    case False
    thus ?thesis
      by (simp add: csr_remaining_def csr_seg_rm_def csr_abstract_def csr_seg_def)
  qed
next
  fix C :: "'e edge_csr" and i j :: nat
  assume inv: "csr_invar C" and iK: "i \<in> K" and neq: "j \<noteq> i"
  \<comment> \<open>reset: remaining at other index\<close>
  show "csr_remaining (csr_reset C i) j = csr_remaining C j"
    by (simp add: csr_remaining_def csr_seg_rm_def csr_cur_reset_neq[OF neq])
next
  fix C :: "'e edge_csr" and i j :: nat
  assume inv: "csr_invar C" and iK: "i \<in> K" and neq: "j \<noteq> i"
  \<comment> \<open>reset: iterated at other index\<close>
  show "csr_iterated (csr_reset C i) j = csr_iterated C j"
    by (simp add: csr_iterated_def csr_seg_it_def csr_cur_reset_neq[OF neq])
qed

text \<open>Register the concrete collection as an interpretation, giving the prefixed @{text csr} rules.\<close>

interpretation csr: indexed_iterable_set
  csr_invar csr_abstract csr_current csr_has csr_iterated csr_remaining csr_move csr_reset K
  for K
  by (rule csr_indexed_iterable_set)


section \<open>The two edge-iterators over the concrete collection\<close>

text \<open>A directed multigraph presents its outgoing resp.\ ingoing adjacency through an
      @{locale indexed_iterable_set} over the vertices. Since the @{locale outgoing_edge_iterator} and
      @{locale ingoing_edge_iterator} locales add nothing to @{locale indexed_iterable_set} beyond the
      axiom-free @{locale multigraph_spec}, the concrete collection furnishes both directly, whatever
      the underlying edge set and endpoint maps.\<close>

lemma csr_outgoing_edge_iterator:
  "outgoing_edge_iterator E fs sn csr_invar csr_abstract csr_current csr_has
                          csr_iterated csr_remaining csr_move csr_reset"
  unfolding outgoing_edge_iterator_def by (rule csr_indexed_iterable_set)

lemma csr_ingoing_edge_iterator:
  "ingoing_edge_iterator E fs sn csr_invar csr_abstract csr_current csr_has
                         csr_iterated csr_remaining csr_move csr_reset"
  unfolding ingoing_edge_iterator_def by (rule csr_indexed_iterable_set)


section \<open>Building a concrete collection from the edge list\<close>

text \<open>The collection is assembled purely functionally from the data we already have: the number of
      vertices @{term n}, an (executable) endpoint map @{term key} sending each edge to its vertex
      index (@{term fst} for the outgoing collection, @{term snd} for the ingoing one), and the flat
      list @{term es} of edges. Edges are grouped by their key into blocks laid out consecutively in
      vertex order; the pointer arrays are the running block offsets, and every cursor starts at the
      beginning of its block. Everything below is code-generatable.\<close>

subsection \<open>Elementary list facts\<close>

lemma sum_list_take_le: "sum_list (take k xs) \<le> sum_list (xs::nat list)"
  by (metis append_take_drop_id le_add1 sum_list_append)

lemma sum_list_take_mono:
  "k \<le> m \<Longrightarrow> sum_list (take k xs) \<le> sum_list (take m (xs::nat list))"
  by (metis min.absorb1 sum_list_take_le take_take)

lemma map_nth_take_drop:
  assumes "off + l \<le> length ys"
  shows "map ((!) ys) [off ..< off + l] = take l (drop off ys)"
proof (rule nth_equalityI)
  show "length (map ((!) ys) [off..<off + l]) = length (take l (drop off ys))"
    using assms by simp
next
  fix k assume "k < length (map ((!) ys) [off..<off + l])"
  hence k: "k < l" by simp
  have "map ((!) ys) [off..<off + l] ! k = ys ! (off + k)" using k by simp
  moreover have "take l (drop off ys) ! k = ys ! (off + k)"
    using k assms by (simp add: add.commute)
  ultimately show "map ((!) ys) [off..<off + l] ! k = take l (drop off ys) ! k" by simp
qed

text \<open>The image of an index block of a @{const concat} is exactly the corresponding sub-list.\<close>

lemma concat_block:
  assumes v: "v < length G"
  shows "(!) (concat G) ` {length (concat (take v G)) ..<
                          length (concat (take v G)) + length (G ! v)} = set (G ! v)"
proof -
  define off where "off = length (concat (take v G))"
  have split: "concat G = concat (take v G) @ (G ! v @ concat (drop (Suc v) G))"
    using v by (metis Cons_nth_drop_Suc append_take_drop_id concat.simps(2) concat_append)
  have drop_off: "drop off (concat G) = G ! v @ concat (drop (Suc v) G)"
    unfolding off_def by (subst split) (simp add: off_def)
  have bound: "off + length (G ! v) \<le> length (concat G)"
    unfolding off_def by (subst split) simp
  have "map ((!) (concat G)) [off ..< off + length (G ! v)] = take (length (G ! v)) (drop off (concat G))"
    using bound by (rule map_nth_take_drop)
  also have "\<dots> = G ! v" using drop_off by simp
  finally have "map ((!) (concat G)) [off ..< off + length (G ! v)] = G ! v" .
  hence "(!) (concat G) ` {off ..< off + length (G ! v)} = set (G ! v)"
    by (metis set_map set_upt)
  thus ?thesis unfolding off_def .
qed

text \<open>Grouping distinct edges by (distinct) keys yields a distinct concatenation, because an edge
      lands in exactly one block.\<close>

lemma distinct_concat_group:
  assumes "distinct es" "distinct vs"
  shows "distinct (concat (map (\<lambda>v. filter (\<lambda>e. key e = v) es) vs))"
  using assms
proof (induction vs)
  case Nil thus ?case by simp
next
  case (Cons v vs)
  have disj: "set (filter (\<lambda>e. key e = v) es)
                \<inter> set (concat (map (\<lambda>v. filter (\<lambda>e. key e = v) es) vs)) = {}"
    using Cons.prems by auto
  show ?case using Cons.IH Cons.prems disj by auto
qed

subsection \<open>The constructor\<close>

definition build_csr :: "nat \<Rightarrow> ('e \<Rightarrow> nat) \<Rightarrow> 'e list \<Rightarrow> 'e edge_csr" where
  "build_csr n key es =
     (let groups = map (\<lambda>v. filter (\<lambda>e. key e = v) es) [0..<n];
          lens   = map length groups
      in edge_csr.make (concat groups)
           (map (\<lambda>v. sum_list (take v lens)) [0..<n])
           (map (\<lambda>v. sum_list (take (Suc v) lens)) [0..<n])
           (map (\<lambda>v. sum_list (take v lens)) [0..<n]))"

text \<open>The vertex blocks; the block of vertex @{term v} is exactly its keyed edges.\<close>

definition csr_groups :: "nat \<Rightarrow> ('e \<Rightarrow> nat) \<Rightarrow> 'e list \<Rightarrow> 'e list list" where
  "csr_groups n key es = map (\<lambda>v. filter (\<lambda>e. key e = v) es) [0..<n]"

lemma length_csr_groups [simp]: "length (csr_groups n key es) = n"
  by (simp add: csr_groups_def)

lemma nth_csr_groups: "v < n \<Longrightarrow> csr_groups n key es ! v = filter (\<lambda>e. key e = v) es"
  by (simp add: csr_groups_def)

lemma set_nth_csr_groups: "v < n \<Longrightarrow> set (csr_groups n key es ! v) = {e \<in> set es. key e = v}"
  by (auto simp: nth_csr_groups)

subsection \<open>Selectors of the constructed collection\<close>

lemma build_csr_n [simp]: "csr_n (build_csr n key es) = n"
  by (simp add: build_csr_def csr_n_def Let_def edge_csr.make_def)

lemma build_csr_edges [simp]: "csr_edges (build_csr n key es) = concat (csr_groups n key es)"
  by (simp add: build_csr_def csr_groups_def Let_def edge_csr.make_def)

lemma build_csr_len_lo [simp]: "length (csr_lo (build_csr n key es)) = n"
  by (simp add: build_csr_def Let_def edge_csr.make_def)

lemma build_csr_len_hi [simp]: "length (csr_hi (build_csr n key es)) = n"
  by (simp add: build_csr_def Let_def edge_csr.make_def)

lemma build_csr_lo_nth:
  "v < n \<Longrightarrow> csr_lo (build_csr n key es) ! v = sum_list (take v (map length (csr_groups n key es)))"
  by (simp add: build_csr_def csr_groups_def Let_def edge_csr.make_def map_map comp_def)

lemma build_csr_hi_nth:
  "v < n \<Longrightarrow> csr_hi (build_csr n key es) ! v = sum_list (take (Suc v) (map length (csr_groups n key es)))"
  by (simp add: build_csr_def csr_groups_def Let_def edge_csr.make_def map_map comp_def)

lemma build_csr_cur_nth:
  "v < n \<Longrightarrow> csr_cur (build_csr n key es) ! v = sum_list (take v (map length (csr_groups n key es)))"
  by (simp add: build_csr_def csr_groups_def Let_def edge_csr.make_def map_map comp_def)

lemma build_csr_lo_eq:
  "v < n \<Longrightarrow> csr_lo (build_csr n key es) ! v = length (concat (take v (csr_groups n key es)))"
  by (simp add: build_csr_lo_nth length_concat take_map)

lemma build_csr_hi_eq:
  "v < n \<Longrightarrow> csr_hi (build_csr n key es) ! v
              = length (concat (take v (csr_groups n key es))) + length (csr_groups n key es ! v)"
  by (simp add: build_csr_hi_nth length_concat take_map take_Suc_conv_app_nth)

subsection \<open>Correctness of the constructor\<close>

text \<open>At every vertex the abstract iterable set is exactly that vertex's keyed edges.\<close>

lemma build_csr_abstract:
  assumes "v < n"
  shows "csr_abstract (build_csr n key es) v = {e \<in> set es. key e = v}"
proof -
  let ?G = "csr_groups n key es"
  have seg: "csr_seg (build_csr n key es) v
               = {length (concat (take v ?G)) ..< length (concat (take v ?G)) + length (?G ! v)}"
    using assms by (simp add: csr_seg_def build_csr_lo_eq build_csr_hi_eq)
  have "csr_abstract (build_csr n key es) v = (!) (concat ?G) ` csr_seg (build_csr n key es) v"
    by (simp add: csr_abstract_def)
  also have "\<dots> = set (?G ! v)"
    unfolding seg using assms by (simp add: concat_block)
  also have "\<dots> = {e \<in> set es. key e = v}"
    using assms by (simp add: set_nth_csr_groups)
  finally show ?thesis .
qed

text \<open>Provided the edges are distinct, the constructed collection is well-formed.\<close>

lemma build_csr_invar:
  assumes "distinct es"
  shows "csr_invar (build_csr n key es)"
proof -
  let ?C = "build_csr n key es"
  let ?L = "map length (csr_groups n key es)"
  have len_edges: "length (csr_edges ?C) = sum_list ?L"
    by (simp add: length_concat)
  have lo: "\<And>v. v < n \<Longrightarrow> csr_lo ?C ! v = sum_list (take v ?L)" by (rule build_csr_lo_nth)
  have hi: "\<And>v. v < n \<Longrightarrow> csr_hi ?C ! v = sum_list (take (Suc v) ?L)" by (rule build_csr_hi_nth)
  have cur: "\<And>v. v < n \<Longrightarrow> csr_cur ?C ! v = sum_list (take v ?L)" by (rule build_csr_cur_nth)
  have dist: "distinct (csr_edges ?C)"
    using assms by (simp add: csr_groups_def distinct_concat_group)
  have hilo: "\<And>a b. a < b \<Longrightarrow> b < n \<Longrightarrow> csr_hi ?C ! a \<le> csr_lo ?C ! b"
  proof -
    fix a b assume ab: "a < b" and bn: "b < n"
    have an: "a < n" using ab bn by simp
    have "csr_hi ?C ! a = sum_list (take (Suc a) ?L)" using hi[OF an] .
    also have "\<dots> \<le> sum_list (take b ?L)" using sum_list_take_mono[of "Suc a" b ?L] ab by simp
    also have "\<dots> = csr_lo ?C ! b" using lo[OF bn] by simp
    finally show "csr_hi ?C ! a \<le> csr_lo ?C ! b" .
  qed
  have bounds: "\<forall>v<csr_n ?C. csr_lo ?C ! v \<le> csr_cur ?C ! v \<and> csr_cur ?C ! v \<le> csr_hi ?C ! v
                              \<and> csr_hi ?C ! v \<le> length (csr_edges ?C)"
  proof (intro allI impI)
    fix v assume "v < csr_n ?C" hence v: "v < n" by simp
    have "csr_lo ?C ! v \<le> csr_cur ?C ! v" using lo[OF v] cur[OF v] by simp
    moreover have "csr_cur ?C ! v \<le> csr_hi ?C ! v"
      using cur[OF v] hi[OF v] sum_list_take_mono[of v "Suc v" ?L] by simp
    moreover have "csr_hi ?C ! v \<le> length (csr_edges ?C)"
      using hi[OF v] len_edges sum_list_take_le[of "Suc v" ?L] by simp
    ultimately show "csr_lo ?C ! v \<le> csr_cur ?C ! v \<and> csr_cur ?C ! v \<le> csr_hi ?C ! v
                       \<and> csr_hi ?C ! v \<le> length (csr_edges ?C)" by simp
  qed
  have disj: "\<forall>u<csr_n ?C. \<forall>v<csr_n ?C. u \<noteq> v \<longrightarrow>
                {csr_lo ?C ! u ..< csr_hi ?C ! u} \<inter> {csr_lo ?C ! v ..< csr_hi ?C ! v} = {}"
  proof (intro allI impI)
    fix u v assume u: "u < csr_n ?C" and v: "v < csr_n ?C" and ne: "u \<noteq> v"
    from u v have un: "u < n" and vn: "v < n" by simp_all
    show "{csr_lo ?C ! u ..< csr_hi ?C ! u} \<inter> {csr_lo ?C ! v ..< csr_hi ?C ! v} = {}"
    proof (cases "u < v")
      case True
      show ?thesis using hilo[OF True vn] by auto
    next
      case False
      hence vu: "v < u" using ne by simp
      show ?thesis using hilo[OF vu un] by auto
    qed
  qed
  show ?thesis
    unfolding csr_invar_def using dist bounds disj by simp
qed

section \<open>An efficient linear-time constructor\<close>

text \<open>The clarity constructor @{const build_csr} re-scans the whole edge list once per vertex and
      recomputes every prefix sum from scratch, so it costs \<open>O(n\<cdot>m + n\<^sup>2)\<close>. Reading the pointer
      lists as genuine (constant-time) arrays, the CSR can instead be built in \<open>O(n + m)\<close> by a single
      distribution pass. \<open>bucketize\<close> walks the edges once, prepending each edge onto the bucket
      of its key (one array read and one array write per edge); \<open>psums\<close> turns the bucket sizes
      into block offsets in one left-to-right scan. We show the fast constructor is \emph{equal} to
      @{const build_csr}, so all of its correctness (well-formedness and the per-vertex abstraction)
      transfers verbatim.\<close>

subsection \<open>Bucketing the edges in one pass\<close>

definition bucketize :: "nat \<Rightarrow> ('e \<Rightarrow> nat) \<Rightarrow> 'e list \<Rightarrow> 'e list list" where
  "bucketize n key es = fold (\<lambda>e bk. bk[key e := e # bk ! (key e)]) es (replicate n [])"

lemma fold_bucket_length:
  "length (fold (\<lambda>e bk. bk[key e := e # bk ! (key e)]) es acc) = length acc"
  by (induction es arbitrary: acc) simp_all

lemma bucketize_length [simp]: "length (bucketize n key es) = n"
  by (simp add: bucketize_def fold_bucket_length)

text \<open>Prepending reverses order within a bucket, so bucket @{term v} holds @{term v}'s keyed edges
      reversed.\<close>

lemma fold_bucket_nth:
  "v < length acc \<Longrightarrow>
     fold (\<lambda>e bk. bk[key e := e # bk ! (key e)]) es acc ! v
       = rev (filter (\<lambda>e. key e = v) es) @ acc ! v"
proof (induction es arbitrary: acc)
  case Nil thus ?case by simp
next
  case (Cons e es)
  have upd: "(acc[key e := e # acc ! (key e)]) ! v = (if key e = v then e # acc ! v else acc ! v)"
    using Cons.prems by (cases "key e < length acc") (auto simp: nth_list_update list_update_beyond)
  have len': "v < length (acc[key e := e # acc ! (key e)])" using Cons.prems by simp
  have "fold (\<lambda>e bk. bk[key e := e # bk ! (key e)]) (e # es) acc ! v
          = rev (filter (\<lambda>e. key e = v) es) @ (acc[key e := e # acc ! (key e)]) ! v"
    using Cons.IH[OF len'] by simp
  also have "\<dots> = rev (filter (\<lambda>e. key e = v) (e # es)) @ acc ! v"
    by (simp add: upd)
  finally show ?case .
qed

lemma bucketize_nth:
  "v < n \<Longrightarrow> bucketize n key es ! v = rev (filter (\<lambda>e. key e = v) es)"
  by (simp add: bucketize_def fold_bucket_nth)

subsection \<open>Block offsets by a single scan\<close>

fun psums :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "psums acc [] = [acc]"
| "psums acc (x # xs) = acc # psums (acc + x) xs"

lemma psums_length: "length (psums acc xs) = Suc (length xs)"
  by (induction xs arbitrary: acc) simp_all

lemma psums_nth: "v \<le> length xs \<Longrightarrow> psums acc xs ! v = acc + sum_list (take v xs)"
  by (induction xs arbitrary: acc v) (auto simp: take_Cons' nth_Cons split: nat.split)

subsection \<open>The fast constructor\<close>

definition build_csr_fast :: "nat \<Rightarrow> ('e \<Rightarrow> nat) \<Rightarrow> 'e list \<Rightarrow> 'e edge_csr" where
  "build_csr_fast n key es =
     (let buckets = bucketize n key es;
          p = psums 0 (map length buckets)
      in edge_csr.make (concat (map rev buckets)) (butlast p) (tl p) (butlast p))"

lemma build_csr_fast_edges:
  "csr_edges (build_csr_fast n key es) = concat (map rev (bucketize n key es))"
  by (simp add: build_csr_fast_def Let_def edge_csr.make_def)

lemma build_csr_fast_lo:
  "csr_lo (build_csr_fast n key es) = butlast (psums 0 (map length (bucketize n key es)))"
  by (simp add: build_csr_fast_def Let_def edge_csr.make_def)

lemma build_csr_fast_hi:
  "csr_hi (build_csr_fast n key es) = tl (psums 0 (map length (bucketize n key es)))"
  by (simp add: build_csr_fast_def Let_def edge_csr.make_def)

lemma build_csr_fast_cur:
  "csr_cur (build_csr_fast n key es) = butlast (psums 0 (map length (bucketize n key es)))"
  by (simp add: build_csr_fast_def Let_def edge_csr.make_def)

lemma build_csr_fast_more:
  "edge_csr.more (build_csr_fast n key es) = edge_csr.more (build_csr n key es)"
  by (simp add: build_csr_fast_def build_csr_def Let_def edge_csr.make_def)

subsection \<open>Equivalence with the clarity constructor\<close>

text \<open>Reversing each bucket recovers the vertex blocks, and bucket sizes are block sizes.\<close>

lemma rev_eq: "map rev (bucketize n key es) = csr_groups n key es"
  by (rule nth_equalityI) (auto simp: bucketize_nth nth_csr_groups)

lemma len_eq: "map length (bucketize n key es) = map length (csr_groups n key es)"
proof (rule nth_equalityI)
  show "length (map length (bucketize n key es)) = length (map length (csr_groups n key es))" by simp
next
  fix i assume "i < length (map length (bucketize n key es))"
  hence i: "i < n" by simp
  thus "map length (bucketize n key es) ! i = map length (csr_groups n key es) ! i"
    by (simp add: bucketize_nth nth_csr_groups)
qed

lemma build_csr_fast_eq: "build_csr_fast n key es = build_csr n key es"
proof (rule edge_csr.equality)
  show "csr_edges (build_csr_fast n key es) = csr_edges (build_csr n key es)"
    by (simp add: build_csr_fast_edges rev_eq)
next
  show "csr_lo (build_csr_fast n key es) = csr_lo (build_csr n key es)"
  proof (rule nth_equalityI)
    show "length (csr_lo (build_csr_fast n key es)) = length (csr_lo (build_csr n key es))"
      by (simp add: build_csr_fast_lo len_eq psums_length)
  next
    fix i assume "i < length (csr_lo (build_csr_fast n key es))"
    hence i: "i < n" by (simp add: build_csr_fast_lo len_eq psums_length)
    have "csr_lo (build_csr_fast n key es) ! i = sum_list (take i (map length (csr_groups n key es)))"
      using i by (simp add: build_csr_fast_lo len_eq nth_butlast psums_length psums_nth)
    thus "csr_lo (build_csr_fast n key es) ! i = csr_lo (build_csr n key es) ! i"
      using i by (simp add: build_csr_lo_nth)
  qed
next
  show "csr_hi (build_csr_fast n key es) = csr_hi (build_csr n key es)"
  proof (rule nth_equalityI)
    show "length (csr_hi (build_csr_fast n key es)) = length (csr_hi (build_csr n key es))"
      by (simp add: build_csr_fast_hi len_eq psums_length)
  next
    fix i assume "i < length (csr_hi (build_csr_fast n key es))"
    hence i: "i < n" by (simp add: build_csr_fast_hi len_eq psums_length)
    have "csr_hi (build_csr_fast n key es) ! i = sum_list (take (Suc i) (map length (csr_groups n key es)))"
      using i by (simp add: build_csr_fast_hi len_eq nth_tl psums_length psums_nth)
    thus "csr_hi (build_csr_fast n key es) ! i = csr_hi (build_csr n key es) ! i"
      using i by (simp add: build_csr_hi_nth)
  qed
next
  show "csr_cur (build_csr_fast n key es) = csr_cur (build_csr n key es)"
  proof (rule nth_equalityI)
    show "length (csr_cur (build_csr_fast n key es)) = length (csr_cur (build_csr n key es))"
      by (simp add: build_csr_fast_cur len_eq psums_length build_csr_def Let_def edge_csr.make_def)
  next
    fix i assume "i < length (csr_cur (build_csr_fast n key es))"
    hence i: "i < n" by (simp add: build_csr_fast_cur len_eq psums_length)
    have "csr_cur (build_csr_fast n key es) ! i = sum_list (take i (map length (csr_groups n key es)))"
      using i by (simp add: build_csr_fast_cur len_eq nth_butlast psums_length psums_nth)
    thus "csr_cur (build_csr_fast n key es) ! i = csr_cur (build_csr n key es) ! i"
      using i by (simp add: build_csr_cur_nth)
  qed
next
  show "edge_csr.more (build_csr_fast n key es) = edge_csr.more (build_csr n key es)"
    by (rule build_csr_fast_more)
qed

text \<open>Correctness of the fast constructor is inherited from @{const build_csr}.\<close>

lemma build_csr_fast_n [simp]: "csr_n (build_csr_fast n key es) = n"
  by (simp add: build_csr_fast_eq)

lemma build_csr_fast_invar: "distinct es \<Longrightarrow> csr_invar (build_csr_fast n key es)"
  by (simp add: build_csr_fast_eq build_csr_invar)

lemma build_csr_fast_abstract:
  "v < n \<Longrightarrow> csr_abstract (build_csr_fast n key es) v = {e \<in> set es. key e = v}"
  by (simp add: build_csr_fast_eq build_csr_abstract)

section \<open>A two-pass counting-sort constructor\<close>

text \<open>The bucket constructor above is \<open>O(n + m)\<close> but allocates a linked list per vertex and
      makes several passes. A real high-performance, cache-friendly implementation is the textbook
      \emph{counting sort}: one pass counts the edges per key, a scan turns the counts into block
      offsets, and a second pass scatters each edge straight into its final slot in a flat array,
      advancing a running position per key. So that the imperative refinement can be proved against a
      functional model with the \emph{same} structure, we mirror exactly that algorithm here --- over
      lists that stand in for arrays --- and prove it equal to @{const build_csr} (hence to
      @{const build_csr_fast}), so all correctness transfers. Every step below is a single array read
      or write.\<close>

subsection \<open>Pass one: counting\<close>

definition ct :: "nat \<Rightarrow> ('e \<Rightarrow> nat) \<Rightarrow> 'e list \<Rightarrow> nat list" where
  "ct n key es = fold (\<lambda>e c. c[key e := Suc (c ! key e)]) es (replicate n 0)"

lemma fold_count_length:
  "length (fold (\<lambda>e c. c[key e := Suc (c ! key e)]) es acc) = length acc"
  by (induction es arbitrary: acc) simp_all

lemma ct_length [simp]: "length (ct n key es) = n"
  by (simp add: ct_def fold_count_length)

lemma fold_count_nth:
  "v < length acc \<Longrightarrow>
     fold (\<lambda>e c. c[key e := Suc (c ! key e)]) es acc ! v = length (filter (\<lambda>e. key e = v) es) + acc ! v"
proof (induction es arbitrary: acc)
  case Nil thus ?case by simp
next
  case (Cons e es)
  have upd: "(acc[key e := Suc (acc ! key e)]) ! v = (if key e = v then Suc (acc ! v) else acc ! v)"
    using Cons.prems by (cases "key e < length acc") (auto simp: nth_list_update list_update_beyond)
  have len': "v < length (acc[key e := Suc (acc ! key e)])" using Cons.prems by simp
  have "fold (\<lambda>e c. c[key e := Suc (c ! key e)]) (e # es) acc ! v
          = length (filter (\<lambda>e. key e = v) es) + (acc[key e := Suc (acc ! key e)]) ! v"
    using Cons.IH[OF len'] by simp
  also have "\<dots> = length (filter (\<lambda>e. key e = v) (e # es)) + acc ! v"
    by (simp add: upd)
  finally show ?case .
qed

lemma ct_nth: "v < n \<Longrightarrow> ct n key es ! v = length (filter (\<lambda>e. key e = v) es)"
  by (simp add: ct_def fold_count_nth)

lemma ct_eq: "ct n key es = map length (csr_groups n key es)"
  by (rule nth_equalityI) (auto simp: ct_nth nth_csr_groups)

subsection \<open>Block offsets and their arithmetic\<close>

definition sc_lo :: "nat \<Rightarrow> ('e \<Rightarrow> nat) \<Rightarrow> 'e list \<Rightarrow> nat \<Rightarrow> nat" where
  "sc_lo n key es v = sum_list (take v (ct n key es))"

lemma sc_lo_Suc: "v < n \<Longrightarrow> sc_lo n key es (Suc v) = sc_lo n key es v + ct n key es ! v"
  by (simp add: sc_lo_def take_Suc_conv_app_nth)

lemma sc_lo_mono: "u \<le> w \<Longrightarrow> sc_lo n key es u \<le> sc_lo n key es w"
  by (simp add: sc_lo_def sum_list_take_mono)

lemma length_filter_disj:
  "(\<And>x. \<not>(P x \<and> Q x)) \<Longrightarrow>
     length (filter (\<lambda>x. P x \<or> Q x) xs) = length (filter P xs) + length (filter Q xs)"
  by (induction xs) auto

lemma sum_list_count_eq:
  "(\<Sum>v\<leftarrow>[0..<n]. length (filter (\<lambda>e. key e = v) xs)) = length (filter (\<lambda>e. key e < n) xs)"
proof (induction n)
  case 0 thus ?case by simp
next
  case (Suc n)
  have f: "(\<lambda>e. key e < Suc n) = (\<lambda>e. key e < n \<or> key e = n)" by (auto simp: less_Suc_eq)
  have "length (filter (\<lambda>e. key e < n \<or> key e = n) xs)
          = length (filter (\<lambda>e. key e < n) xs) + length (filter (\<lambda>e. key e = n) xs)"
    by (rule length_filter_disj) auto
  thus ?case using Suc f by simp
qed

lemma sum_ct: "\<forall>e\<in>set es. key e < n \<Longrightarrow> sum_list (ct n key es) = length es"
proof -
  assume a: "\<forall>e\<in>set es. key e < n"
  have "sum_list (ct n key es) = (\<Sum>v\<leftarrow>[0..<n]. length (filter (\<lambda>e. key e = v) es))"
    by (simp add: ct_eq csr_groups_def comp_def)
  also have "\<dots> = length (filter (\<lambda>e. key e < n) es)" by (rule sum_list_count_eq)
  also have "\<dots> = length es" using a by (simp add: filter_id_conv)
  finally show ?thesis .
qed

lemma sc_lo_le_length:
  "\<forall>e\<in>set es. key e < n \<Longrightarrow> v \<le> n \<Longrightarrow> sc_lo n key es v \<le> length es"
  by (simp add: sc_lo_def sum_ct[symmetric] sum_list_take_le)

text \<open>Distinct vertices own disjoint slot ranges.\<close>

lemma sc_block_disj:
  assumes "w < n" "v < n" "v \<noteq> w"
      and "aw < ct n key es ! w" "av < ct n key es ! v"
    shows "sc_lo n key es w + aw \<noteq> sc_lo n key es v + av"
proof (cases "w < v")
  case True
  have "sc_lo n key es w + aw < sc_lo n key es w + ct n key es ! w" using assms(4) by simp
  also have "\<dots> = sc_lo n key es (Suc w)" using assms(1) by (simp add: sc_lo_Suc)
  also have "\<dots> \<le> sc_lo n key es v" using True by (simp add: sc_lo_mono)
  finally show ?thesis by simp
next
  case False
  hence "v < w" using assms(3) by simp
  have "sc_lo n key es v + av < sc_lo n key es v + ct n key es ! v" using assms(5) by simp
  also have "\<dots> = sc_lo n key es (Suc v)" using assms(2) by (simp add: sc_lo_Suc)
  also have "\<dots> \<le> sc_lo n key es w" using \<open>v < w\<close> by (simp add: sc_lo_mono)
  finally show ?thesis by simp
qed

subsection \<open>Pass two: scattering, and its loop invariant\<close>

definition scatter_body :: "('e \<Rightarrow> nat) \<Rightarrow> 'e \<Rightarrow> ('e list \<times> nat list) \<Rightarrow> ('e list \<times> nat list)" where
  "scatter_body key = (\<lambda>e (ed, ps). (ed[ps ! key e := e], ps[key e := Suc (ps ! key e)]))"

text \<open>Invariant after scattering a prefix @{term dn} of the edges: each running position sits one past
      the block start by the number of that key seen, and each already-written slot holds the right
      edge.\<close>

definition sc_inv :: "nat \<Rightarrow> ('e \<Rightarrow> nat) \<Rightarrow> 'e list \<Rightarrow> 'e list \<Rightarrow> nat list \<Rightarrow> 'e list \<Rightarrow> bool" where
  "sc_inv n key es ed ps done \<longleftrightarrow>
     (\<forall>v<n. ps ! v = sc_lo n key es v + length (filter (\<lambda>e. key e = v) done)) \<and>
     (\<forall>v<n. \<forall>j<length (filter (\<lambda>e. key e = v) done).
          ed ! (sc_lo n key es v + j) = filter (\<lambda>e. key e = v) done ! j)"

lemma sc_inv_step:
  assumes valid: "\<forall>e\<in>set es. key e < n"
      and split: "es = done @ e # rest"
      and led: "length ed = length es"
      and lps: "length ps = n"
      and inv: "sc_inv n key es ed ps done"
    shows "sc_inv n key es (ed[ps ! key e := e]) (ps[key e := Suc (ps ! key e)]) (done @ [e])"
proof -
  define w where "w = key e"
  have wn: "w < n" using valid split w_def by auto
  have psw: "ps ! w = sc_lo n key es w + length (filter (\<lambda>x. key x = w) done)"
    using inv wn by (simp add: sc_inv_def)
  have cntw_lt: "length (filter (\<lambda>x. key x = w) done) < ct n key es ! w"
    using split w_def wn by (auto simp: ct_nth)
  have pos_lt: "ps ! w < length es"
  proof -
    have "ps ! w < sc_lo n key es w + ct n key es ! w" using psw cntw_lt by simp
    also have "\<dots> = sc_lo n key es (Suc w)" using wn by (simp add: sc_lo_Suc)
    also have "\<dots> \<le> length es" using valid wn by (simp add: sc_lo_le_length)
    finally show ?thesis .
  qed
  have ps'_conj: "\<forall>v<n. (ps[w := Suc (ps ! w)]) ! v
                        = sc_lo n key es v + length (filter (\<lambda>x. key x = v) (done @ [e]))"
  proof (intro allI impI)
    fix v assume vn: "v < n"
    have psv: "ps ! v = sc_lo n key es v + length (filter (\<lambda>x. key x = v) done)"
      using inv vn by (simp add: sc_inv_def)
    show "(ps[w := Suc (ps ! w)]) ! v = sc_lo n key es v + length (filter (\<lambda>x. key x = v) (done @ [e]))"
    proof (cases "v = w")
      case True thus ?thesis using psw lps wn w_def by (simp add: nth_list_update)
    next
      case False thus ?thesis using psv lps vn w_def by (simp add: nth_list_update)
    qed
  qed
  have ed'_conj: "\<forall>v<n. \<forall>j<length (filter (\<lambda>x. key x = v) (done @ [e])).
        (ed[ps ! w := e]) ! (sc_lo n key es v + j) = filter (\<lambda>x. key x = v) (done @ [e]) ! j"
  proof (intro allI impI)
    fix v j assume vn: "v < n" and jlt: "j < length (filter (\<lambda>x. key x = v) (done @ [e]))"
    show "(ed[ps ! w := e]) ! (sc_lo n key es v + j) = filter (\<lambda>x. key x = v) (done @ [e]) ! j"
    proof (cases "v = w")
      case True
      hence filt: "filter (\<lambda>x. key x = v) (done @ [e]) = filter (\<lambda>x. key x = w) done @ [e]"
        using w_def by simp
      show ?thesis
      proof (cases "j < length (filter (\<lambda>x. key x = w) done)")
        case True
        have "sc_lo n key es v + j \<noteq> ps ! w" using psw True \<open>v = w\<close> by simp
        hence "(ed[ps ! w := e]) ! (sc_lo n key es v + j) = ed ! (sc_lo n key es v + j)"
          by (simp add: nth_list_update)
        also have "\<dots> = filter (\<lambda>x. key x = v) done ! j"
          using inv vn True \<open>v = w\<close> by (simp add: sc_inv_def)
        also have "\<dots> = filter (\<lambda>x. key x = v) (done @ [e]) ! j"
          unfolding filt using True \<open>v = w\<close> by (simp add: nth_append)
        finally show ?thesis .
      next
        case False
        have jeq: "j = length (filter (\<lambda>x. key x = w) done)"
          using jlt[unfolded filt] False by simp
        have "sc_lo n key es v + j = ps ! w" using psw jeq \<open>v = w\<close> by simp
        hence "(ed[ps ! w := e]) ! (sc_lo n key es v + j) = e"
          using pos_lt led by (simp add: nth_list_update)
        also have "\<dots> = filter (\<lambda>x. key x = v) (done @ [e]) ! j"
          unfolding filt using jeq by (simp add: nth_append)
        finally show ?thesis .
      qed
    next
      case False
      have jle: "j < length (filter (\<lambda>x. key x = v) done)" using jlt False w_def by simp
      have jct: "j < ct n key es ! v"
      proof -
        have "j < length (filter (\<lambda>x. key x = v) done)" using jle .
        also have "\<dots> \<le> length (filter (\<lambda>x. key x = v) es)" using split by simp
        also have "\<dots> = ct n key es ! v" using vn by (simp add: ct_nth)
        finally show ?thesis by simp
      qed
      have "sc_lo n key es v + j \<noteq> ps ! w"
        using sc_block_disj[OF wn vn False cntw_lt jct] psw by simp
      hence "(ed[ps ! w := e]) ! (sc_lo n key es v + j) = ed ! (sc_lo n key es v + j)"
        by (simp add: nth_list_update)
      also have "\<dots> = filter (\<lambda>x. key x = v) done ! j"
        using inv vn jle by (simp add: sc_inv_def)
      also have "\<dots> = filter (\<lambda>x. key x = v) (done @ [e]) ! j"
        using False jle w_def by (simp add: nth_append)
      finally show ?thesis .
    qed
  qed
  show ?thesis
    unfolding sc_inv_def w_def[symmetric]
    by (rule conjI[OF ps'_conj ed'_conj])
qed

lemma scatter_body_cons:
  "fold (scatter_body key) (e # rest) (ed, ps)
     = fold (scatter_body key) rest (ed[ps ! key e := e], ps[key e := Suc (ps ! key e)])"
  by (simp add: scatter_body_def)

lemma sc_inv_fold:
  assumes "\<forall>e\<in>set es. key e < n" "es = dn @ rest" "length ed = length es" "length ps = n"
          "sc_inv n key es ed ps dn"
  shows "sc_inv n key es (fst (fold (scatter_body key) rest (ed, ps)))
                        (snd (fold (scatter_body key) rest (ed, ps))) es"
  using assms
proof (induction rest arbitrary: ed ps dn)
  case Nil
  thus ?case by simp
next
  case (Cons e rest)
  have split: "es = dn @ e # rest" using Cons.prems(2) by simp
  have split': "es = (dn @ [e]) @ rest" using Cons.prems(2) by simp
  have step: "sc_inv n key es (ed[ps ! key e := e]) (ps[key e := Suc (ps ! key e)]) (dn @ [e])"
    by (rule sc_inv_step[OF Cons.prems(1) split Cons.prems(3) Cons.prems(4) Cons.prems(5)])
  have led': "length (ed[ps ! key e := e]) = length es" using Cons.prems(3) by simp
  have lps': "length (ps[key e := Suc (ps ! key e)]) = n" using Cons.prems(4) by simp
  show ?case
    using Cons.IH[OF Cons.prems(1) split' led' lps' step] by (simp add: scatter_body_def)
qed

subsection \<open>The scattered edge array equals the grouped edges\<close>

definition scatter_edges :: "nat \<Rightarrow> ('e \<Rightarrow> nat) \<Rightarrow> 'e list \<Rightarrow> 'e \<Rightarrow> 'e list" where
  "scatter_edges n key es dflt =
     fst (fold (scatter_body key) es (replicate (length es) dflt, butlast (psums 0 (ct n key es))))"

lemma scatter_init_inv:
  "sc_inv n key es (replicate (length es) dflt) (butlast (psums 0 (ct n key es))) []"
  unfolding sc_inv_def
proof (intro conjI allI impI)
  fix v assume v: "v < n"
  have "butlast (psums 0 (ct n key es)) ! v = psums 0 (ct n key es) ! v"
    using v by (simp add: nth_butlast psums_length)
  also have "\<dots> = sc_lo n key es v" using v by (simp add: psums_nth sc_lo_def)
  finally show "butlast (psums 0 (ct n key es)) ! v
                  = sc_lo n key es v + length (filter (\<lambda>e. key e = v) [])" by simp
next
  fix v j assume "v < n" "j < length (filter (\<lambda>e. key e = v) [])"
  thus "replicate (length es) dflt ! (sc_lo n key es v + j) = filter (\<lambda>e. key e = v) [] ! j" by simp
qed

lemma scatter_final_inv:
  assumes "\<forall>e\<in>set es. key e < n"
  shows "sc_inv n key es (scatter_edges n key es dflt)
                        (snd (fold (scatter_body key) es
                               (replicate (length es) dflt, butlast (psums 0 (ct n key es))))) es"
  unfolding scatter_edges_def
  by (rule sc_inv_fold[OF assms _ _ _ scatter_init_inv]) (simp_all add: psums_length)

lemma fold_scatter_fst_length: "length (fst (fold (scatter_body key) es st)) = length (fst st)"
  by (induction es arbitrary: st) (auto simp: scatter_body_def split: prod.split)

lemma scatter_edges_length [simp]: "length (scatter_edges n key es dflt) = length es"
  by (simp add: scatter_edges_def fold_scatter_fst_length)

lemma scatter_edges_nth:
  assumes "\<forall>e\<in>set es. key e < n" "v < n" "j < ct n key es ! v"
  shows "scatter_edges n key es dflt ! (sc_lo n key es v + j) = csr_groups n key es ! v ! j"
proof -
  have jl: "j < length (filter (\<lambda>e. key e = v) es)" using assms(3) assms(2) by (simp add: ct_nth)
  have "scatter_edges n key es dflt ! (sc_lo n key es v + j) = filter (\<lambda>e. key e = v) es ! j"
    using scatter_final_inv[OF assms(1)] assms(2) jl by (simp add: sc_inv_def)
  also have "\<dots> = csr_groups n key es ! v ! j" using assms(2) by (simp add: nth_csr_groups)
  finally show ?thesis .
qed

lemma nth_concat_csr_groups:
  assumes "v < n" "j < length (csr_groups n key es ! v)"
  shows "concat (csr_groups n key es) ! (sc_lo n key es v + j) = csr_groups n key es ! v ! j"
proof -
  let ?G = "csr_groups n key es"
  have lo: "sc_lo n key es v = length (concat (take v ?G))"
  proof -
    have "sc_lo n key es v = sum_list (take v (ct n key es))" by (simp add: sc_lo_def)
    also have "\<dots> = sum_list (map length (take v ?G))" by (simp add: ct_eq take_map)
    also have "\<dots> = length (concat (take v ?G))" by (simp add: length_concat)
    finally show ?thesis .
  qed
  have split: "concat ?G = concat (take v ?G) @ (?G ! v @ concat (drop (Suc v) ?G))"
    using assms(1)
    by (metis Cons_nth_drop_Suc append_take_drop_id concat.simps(2) concat_append length_csr_groups)
  show ?thesis unfolding lo split using assms(2) by (simp add: nth_append)
qed

lemma prefix_block_decomp:
  "p < sum_list (cs :: nat list) \<Longrightarrow>
     \<exists>v<length cs. sum_list (take v cs) \<le> p \<and> p < sum_list (take v cs) + cs ! v"
proof (induction cs rule: rev_induct)
  case Nil thus ?case by simp
next
  case (snoc c cs)
  show ?case
  proof (cases "p < sum_list cs")
    case True
    then obtain v where v: "v < length cs" "sum_list (take v cs) \<le> p"
                          "p < sum_list (take v cs) + cs ! v"
      using snoc.IH by blast
    have "v < length (cs @ [c]) \<and> sum_list (take v (cs @ [c])) \<le> p
            \<and> p < sum_list (take v (cs @ [c])) + (cs @ [c]) ! v"
      using v by (simp add: nth_append)
    thus ?thesis by blast
  next
    case False
    hence "length cs < length (cs @ [c]) \<and> sum_list (take (length cs) (cs @ [c])) \<le> p
             \<and> p < sum_list (take (length cs) (cs @ [c])) + (cs @ [c]) ! (length cs)"
      using snoc.prems by (simp add: nth_append)
    thus ?thesis by blast
  qed
qed

lemma scatter_edges_eq_concat:
  assumes "\<forall>e\<in>set es. key e < n"
  shows "scatter_edges n key es dflt = concat (csr_groups n key es)"
proof (rule nth_equalityI)
  have lc: "length (concat (csr_groups n key es)) = length es"
    by (simp add: length_concat ct_eq[symmetric] sum_ct[OF assms])
  show "length (scatter_edges n key es dflt) = length (concat (csr_groups n key es))"
    by (simp add: lc)
next
  fix p assume "p < length (scatter_edges n key es dflt)"
  hence p: "p < length es" by simp
  have "p < sum_list (ct n key es)" using p sum_ct[OF assms] by simp
  then obtain v where v: "v < n" "sc_lo n key es v \<le> p" "p < sc_lo n key es v + ct n key es ! v"
    using prefix_block_decomp[of p "ct n key es"] by (auto simp: sc_lo_def ct_length)
  define j where "j = p - sc_lo n key es v"
  have pj: "p = sc_lo n key es v + j" using v(2) j_def by simp
  have jct: "j < ct n key es ! v" using v(3) pj by simp
  have jg: "j < length (csr_groups n key es ! v)"
    using jct v(1) by (simp add: nth_csr_groups ct_nth)
  have "scatter_edges n key es dflt ! p = csr_groups n key es ! v ! j"
    unfolding pj by (rule scatter_edges_nth[OF assms v(1) jct])
  also have "\<dots> = concat (csr_groups n key es) ! p"
    unfolding pj by (rule nth_concat_csr_groups[OF v(1) jg, symmetric])
  finally show "scatter_edges n key es dflt ! p = concat (csr_groups n key es) ! p" .
qed

subsection \<open>The counting-sort constructor and its correctness\<close>

text \<open>Tight two-pass build: the counts \<open>ct\<close> and their prefix sums \<open>p\<close> are computed \<^emph>\<open>once\<close>; the block
      starts \<open>lo = butlast p\<close> serve simultaneously as the scatter's initial write cursor and as the
      record's \<open>lo\<close>/\<open>cur\<close> fields, so nothing beyond the four stored arrays (\<open>edges\<close>, \<open>lo\<close>, \<open>hi\<close>, \<open>cur\<close>)
      persists and the edge list is swept exactly twice --- once by \<open>ct\<close> (count) and once by the scatter
      \<open>fold\<close>. The intermediate counts/prefix-sum arrays are the inherent working memory of a counting
      sort and touch only the length-\<open>n\<close> key range, never re-scanning the edges.\<close>

definition build_csr_scatter :: "nat \<Rightarrow> ('e \<Rightarrow> nat) \<Rightarrow> 'e list \<Rightarrow> 'e \<Rightarrow> 'e edge_csr" where
  "build_csr_scatter n key es dflt =
     (let p  = psums 0 (ct n key es);
          lo = butlast p
      in edge_csr.make
           (fst (fold (scatter_body key) es (replicate (length es) dflt, lo)))
           lo (tl p) lo)"

lemma ct_eq_bucketize: "ct n key es = map length (bucketize n key es)"
  by (simp add: ct_eq len_eq)

text \<open>Selector views: the shared \<open>lo\<close> makes the \<open>edges\<close> field defeq to @{const scatter_edges} (same
      initial cursor) and the \<open>lo\<close>/\<open>hi\<close>/\<open>cur\<close> fields the same offset slices as before, so the equality
      with the bucket constructor and every downstream fact are unchanged.\<close>

lemma build_csr_scatter_edges [simp]:
  "csr_edges (build_csr_scatter n key es dflt) = scatter_edges n key es dflt"
  by (simp add: build_csr_scatter_def scatter_edges_def Let_def edge_csr.make_def)

lemma build_csr_scatter_lo_sel [simp]:
  "csr_lo (build_csr_scatter n key es dflt) = butlast (psums 0 (ct n key es))"
  by (simp add: build_csr_scatter_def Let_def edge_csr.make_def)

lemma build_csr_scatter_hi_sel [simp]:
  "csr_hi (build_csr_scatter n key es dflt) = tl (psums 0 (ct n key es))"
  by (simp add: build_csr_scatter_def Let_def edge_csr.make_def)

lemma build_csr_scatter_cur_sel [simp]:
  "csr_cur (build_csr_scatter n key es dflt) = butlast (psums 0 (ct n key es))"
  by (simp add: build_csr_scatter_def Let_def edge_csr.make_def)

lemma build_csr_scatter_more_sel [simp]:
  "edge_csr.more (build_csr_scatter n key es dflt) = edge_csr.more (build_csr_fast n key es)"
  by (simp add: build_csr_scatter_def build_csr_fast_def Let_def edge_csr.make_def)

text \<open>Same offsets as the bucket constructor (same block sizes) and, once the keys are valid, the same
      flat edge array, so the two constructors coincide.\<close>

lemma build_csr_scatter_eq_fast:
  assumes "\<forall>e\<in>set es. key e < n"
  shows "build_csr_scatter n key es dflt = build_csr_fast n key es"
proof (rule edge_csr.equality)
  show "csr_edges (build_csr_scatter n key es dflt) = csr_edges (build_csr_fast n key es)"
    by (simp add: build_csr_fast_edges scatter_edges_eq_concat[OF assms] rev_eq)
next
  show "csr_lo (build_csr_scatter n key es dflt) = csr_lo (build_csr_fast n key es)"
    by (simp add: build_csr_fast_lo ct_eq_bucketize)
next
  show "csr_hi (build_csr_scatter n key es dflt) = csr_hi (build_csr_fast n key es)"
    by (simp add: build_csr_fast_hi ct_eq_bucketize)
next
  show "csr_cur (build_csr_scatter n key es dflt) = csr_cur (build_csr_fast n key es)"
    by (simp add: build_csr_fast_cur ct_eq_bucketize)
next
  show "edge_csr.more (build_csr_scatter n key es dflt) = edge_csr.more (build_csr_fast n key es)"
    by simp
qed

lemma build_csr_scatter_eq:
  "\<forall>e\<in>set es. key e < n \<Longrightarrow> build_csr_scatter n key es dflt = build_csr n key es"
  by (simp add: build_csr_scatter_eq_fast build_csr_fast_eq)

lemma build_csr_scatter_n:
  "\<forall>e\<in>set es. key e < n \<Longrightarrow> csr_n (build_csr_scatter n key es dflt) = n"
  by (simp add: build_csr_scatter_eq)

lemma build_csr_scatter_invar:
  "\<lbrakk>distinct es; \<forall>e\<in>set es. key e < n\<rbrakk> \<Longrightarrow> csr_invar (build_csr_scatter n key es dflt)"
  by (simp add: build_csr_scatter_eq build_csr_invar)

lemma build_csr_scatter_abstract:
  "\<lbrakk>\<forall>e\<in>set es. key e < n; v < n\<rbrakk>
     \<Longrightarrow> csr_abstract (build_csr_scatter n key es dflt) v = {e \<in> set es. key e = v}"
  by (simp add: build_csr_scatter_eq build_csr_abstract)

text \<open>For the \<open>Network_Simplex_Initial_Basis\<close> inputs the edges are the indices @{term \<open>[0..<m]\<close>}
      (already distinct) and the key is an @{term nth} into the tail resp.\ head list, a constant-time
      array read. Every endpoint is a vertex index below \<open>n\<close>, so the well-formed-keys assumption
      @{term \<open>\<forall>e\<in>set es. key e < n\<close>} holds and @{thm build_csr_scatter_invar} /
      @{thm build_csr_scatter_abstract} apply: the outgoing collection is
      @{term \<open>build_csr_scatter n (nth fst_list) [0..<m] dflt\<close>} and the ingoing one
      @{term \<open>build_csr_scatter n (nth snd_list) [0..<m] dflt\<close>}, each built in \<open>O(n + m)\<close> by the
      cache-friendly two-pass counting sort mirrored above.\<close>

end
