theory CSR_Buildup_Simple
  imports CSR_Graph_Simple
begin

lemma fold_fst_heleper:"fold (\<lambda>p dl. dl[fst p := Suc (dl ! fst p)]) a b
= fold (\<lambda>(u, uu) dl. dl[u := Suc (dl ! u)]) a b"
  by(induction a arbitrary: b) auto

lemma four_parallel_fold:"fold
          (\<lambda>v (si_a, ei_a, of_a, tot).
              (f1 v si_a, f2 v ei_a, f3 v of_a, f4 v tot))
       xs (si_a, ei_a, of_a, tot) = 
      (fold f1 xs si_a, fold f2 xs ei_a, fold f3 xs of_a, fold f4 xs tot)"
 by(induction xs arbitrary: si_a ei_a of_a tot) auto

section \<open>Building a CSR Graph from an Edge List\<close>

subsection \<open>Abstract Construction\<close>

text \<open>Neighbours of vertex v in edge list es.\<close>
definition nbrs :: "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat list" where
  "nbrs es v = map snd (filter (\<lambda>e. fst e = v) es)"

text \<open>
Number of vertices: 0 for the empty edge list, otherwise one more than the
largest source vertex.
\<close>
definition nverts :: "(nat \<times> nat) list \<Rightarrow> nat" where
  "nverts es =
     (if es = [] then 0
      else Suc (foldl (\<lambda>m e. max m (fst e)) 0 es))"

text \<open>Start offset of vertex v in the flat neighbour array.\<close>
definition start_off :: "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat" where
  "start_off es v = sum_list (map (\<lambda>u. length (nbrs es u)) [0..<v])"

text \<open>Flat neighbour array (as an Isabelle list).\<close>
definition build_nha :: "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat list" where
  "build_nha es n = concat (map (nbrs es) [0..<n])"

text \<open>Start-index list for the CSR representation.\<close>
definition build_sindices :: "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat list" where
  "build_sindices es n =
     map (\<lambda>v. if nbrs es v = [] then 1 else start_off es v) [0..<n]"

text \<open>End-index list for the CSR representation.\<close>
definition build_eindices :: "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat list" where
  "build_eindices es n =
     map (\<lambda>v. if nbrs es v = [] then 0
               else start_off es v + length (nbrs es v) - 1) [0..<n]"

text \<open>
Abstract neighbour-list map (the nhlists argument of CSR\_assn\_raw at line 546
of CSR\_Graph\_Simple.thy).
\<close>
definition build_nhlists :: "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat list option" where
  "build_nhlists es v =
     (if nbrs es v = [] then None else Some (nbrs es v))"

subsection \<open>Basic Properties\<close>

lemma length_build_sindices [simp]: "length (build_sindices es n) = n"
  unfolding build_sindices_def by simp

lemma length_build_eindices [simp]: "length (build_eindices es n) = n"
  unfolding build_eindices_def by simp

lemma length_build_nha: "length (build_nha es n) = start_off es n"
  unfolding build_nha_def start_off_def
  by (simp add: length_concat comp_def)

lemma start_off_zero [simp]: "start_off es 0 = 0"
  unfolding start_off_def by simp

lemma start_off_Suc:
  "start_off es (Suc v) = start_off es v + length (nbrs es v)"
  unfolding start_off_def by simp

lemma build_nhlists_dom:
  "dom (build_nhlists es) = {v. nbrs es v \<noteq> []}"
  unfolding build_nhlists_def by (auto split: if_split)

lemma build_nhlists_val:
  "v \<in> dom (build_nhlists es) \<Longrightarrow> the (build_nhlists es v) = nbrs es v"
  by(auto simp add: build_nhlists_def)

subsection \<open>Vertex Bounds\<close>

lemma foldl_max_ge_acc:
  "foldl (\<lambda>m (e :: nat \<times> nat). max m (fst e)) acc xs \<ge> acc"
  apply (induction xs arbitrary: acc)
   apply (auto simp: le_max_iff_disj )
  using max.bounded_iff by blast

lemma foldl_max_fst_ge:
  "(u, v::nat) \<in> set es \<Longrightarrow>
   foldl (\<lambda>(m::nat) e. max m (fst e)) acc es \<ge> u"
proof (induction es arbitrary: acc)
  case Nil thus ?case by simp
next
  case (Cons e es')
  show ?case
  proof (cases "(u, v) = e")
    case True
    then have "fst e = u" by auto
    thus ?thesis
      using foldl_max_ge_acc[of "max acc (fst e)" es']
      by (auto simp: le_max_iff_disj intro: order_trans)
  next
    case False
    with Cons.prems have "(u, v) \<in> set es'" by simp
    with Cons.IH show ?thesis by simp
  qed
qed

lemma nverts_source_upper:
  "(u, v) \<in> set es \<Longrightarrow> u < nverts es"
  using foldl_max_fst_ge[of u v es 0]
  unfolding nverts_def by (auto simp: less_Suc_eq_le)

lemma build_nhlists_dom_subset:
  "dom (build_nhlists es) \<subseteq> {0..<nverts es}"
proof
  fix v assume hv: "v \<in> dom (build_nhlists es)"
  have hne: "nbrs es v \<noteq> []"
    using hv unfolding build_nhlists_dom by simp
  have "\<exists>e \<in> set es. fst e = v"
    using hne unfolding nbrs_def
    by (auto simp: filter_empty_conv)
  then obtain e where he: "e \<in> set es" "fst e = v" by blast
  obtain w where "e = (v, w)"
    using he(2) by (cases e) auto
  then have "(v, w) \<in> set es" using he(1) by simp
  thus "v \<in> {0..<nverts es}"
    using nverts_source_upper[of v w es] by simp
qed

subsection \<open>Monotonicity of start\_off\<close>

lemma start_off_mono:
  "v \<le> n \<Longrightarrow> start_off es v \<le> start_off es n"
  by (induction n) (auto simp: start_off_Suc le_Suc_eq)

lemma start_off_lt_total:
  assumes "v < n" "nbrs es v \<noteq> []"
  shows "start_off es v < start_off es n"
proof -
  have "start_off es (Suc v) = start_off es v + length (nbrs es v)"
    by (simp add: start_off_Suc)
  moreover have "start_off es (Suc v) \<le> start_off es n"
    using assms(1) by (intro start_off_mono) simp
  ultimately show ?thesis using assms(2)
    using nat_less_le by fastforce
qed

lemma start_off_end_lt_total:
  assumes "v < n" "nbrs es v \<noteq> []"
  shows "start_off es v + length (nbrs es v) - 1 < start_off es n"
  using start_off_lt_total[OF assms] assms(2) 
  by (metis One_nat_def Suc_le_eq add_gr_0 assms(1)
      length_greater_0_conv nz_le_conv_less start_off_Suc
      start_off_mono)

subsection \<open>The Key Indexing Lemma\<close>

text \<open>
The strict-interval segment at vertex v in the flat array equals nbrs es v.
Proof: split the list at v using id\_take\_nth\_drop, then use
nths\_intervall\_strict\_as\_drop\_and\_take.
\<close>

lemma build_nha_nths_vertex:
  assumes "v < n"
  shows "nths (build_nha es n)
              {start_off es v ..< start_off es v + length (nbrs es v)}
         = nbrs es v"
proof -
  let ?A = "concat (map (nbrs es) [0..<v])"
  let ?xs = "nbrs es v"
  let ?B = "concat (map (nbrs es) [Suc v..<n])"
  have list_split: "[0..<n] = [0..<v] @ v # [Suc v..<n]"
    using assms id_take_nth_drop[of v "[0..<n]"] by simp
  have split: "build_nha es n = ?A @ ?xs @ ?B"
    unfolding build_nha_def by (simp add: list_split)
  have lenA: "length ?A = start_off es v"
    unfolding start_off_def by (simp add: length_concat comp_def)
  show ?thesis
    unfolding nths_intervall_strict_as_drop_and_take
    by (simp add: split lenA[symmetric])
  qed

lemma build_nha_nths_vertex_incl:
  assumes "v < n" "nbrs es v \<noteq> []"
  shows "nths (build_nha es n)
              {start_off es v .. start_off es v + length (nbrs es v) - 1}
         = nbrs es v"
proof -
  let ?s = "start_off es v"
  let ?l = "length (nbrs es v)"
  have pos: "0 < ?l" using assms(2) by simp
  have set_eq: "{?s .. ?s + ?l - 1} = {?s ..< ?s + ?l}"
    using pos by (cases ?l) (simp_all add: atLeastLessThanSuc_atLeastAtMost)
  thus ?thesis using build_nha_nths_vertex[OF assms(1)] by simp
qed

subsection \<open>Correctness of the Abstract Construction\<close>

theorem build_CSR_inv:
  assumes n_def: "n = nverts es"
  shows
    "dom (build_nhlists es) \<subseteq> {0..<length (build_sindices es n)} \<and>
     dom (build_nhlists es) \<subseteq> {0..<length (build_eindices es n)} \<and>
     length (build_sindices es n) = length (build_eindices es n) \<and>
     (\<forall>v \<in> dom (build_nhlists es).
         build_sindices es n ! v < length (build_nha es n) \<and>
         build_eindices es n ! v < length (build_nha es n) \<and>
         the (build_nhlists es v) =
           nths (build_nha es n)
                {build_sindices es n ! v .. build_eindices es n ! v}) \<and>
     (\<forall>v. v \<notin> dom (build_nhlists es) \<and> v < n \<longrightarrow>
         build_eindices es n ! v < build_sindices es n ! v)"
proof (intro conjI)
  show "dom (build_nhlists es) \<subseteq> {0..<length (build_sindices es n)}"
       "dom (build_nhlists es) \<subseteq> {0..<length (build_eindices es n)}"
    using build_nhlists_dom_subset n_def by simp_all
  show "length (build_sindices es n) = length (build_eindices es n)"
    by simp
  show "\<forall>v \<in> dom (build_nhlists es).
           build_sindices es n ! v < length (build_nha es n) \<and>
           build_eindices es n ! v < length (build_nha es n) \<and>
           the (build_nhlists es v) =
             nths (build_nha es n)
                  {build_sindices es n ! v .. build_eindices es n ! v}"
  proof
    fix v assume hv: "v \<in> dom (build_nhlists es)"
    have hn: "nbrs es v \<noteq> []"
      using hv by (simp add: build_nhlists_dom)
    have hv_lt: "v < n"
      unfolding n_def
      using build_nhlists_dom_subset hv
      by force
    have si_val: "build_sindices es n ! v = start_off es v"
      unfolding build_sindices_def using hn hv_lt by simp
    have ei_val: "build_eindices es n ! v = start_off es v + length (nbrs es v) - 1"
      unfolding build_eindices_def using hn hv_lt by simp
    have si_lt: "build_sindices es n ! v < length (build_nha es n)"
      using start_off_lt_total[OF hv_lt hn]
      unfolding length_build_nha si_val by assumption
    have ei_lt: "build_eindices es n ! v < length (build_nha es n)"
      using start_off_end_lt_total[OF hv_lt hn]
      unfolding length_build_nha ei_val by assumption
    have nths_eq:
      "the (build_nhlists es v) =
       nths (build_nha es n)
            {build_sindices es n ! v .. build_eindices es n ! v}"
      unfolding si_val ei_val build_nhlists_def
      using hn apply (simp add: build_nha_nths_vertex_incl[OF hv_lt hn])
      using One_nat_def build_nha_nths_vertex_incl hv_lt
      by presburger
      
      from si_lt ei_lt nths_eq show
      "build_sindices es n ! v < length (build_nha es n) \<and>
       build_eindices es n ! v < length (build_nha es n) \<and>
       the (build_nhlists es v) =
         nths (build_nha es n)
              {build_sindices es n ! v .. build_eindices es n ! v}"
      by blast
  qed
  show "\<forall>v. v \<notin> dom (build_nhlists es) \<and> v < n \<longrightarrow>
            build_eindices es n ! v < build_sindices es n ! v"
  proof (intro allI impI, elim conjE)
    fix v assume hdom: "v \<notin> dom (build_nhlists es)" "v < n"
    then have hn: "nbrs es v = []"
      unfolding build_nhlists_dom by simp
    show "build_eindices es n ! v < build_sindices es n ! v"
      unfolding build_sindices_def build_eindices_def
      using hn hdom(2) by simp
  qed
qed

subsection \<open>Imperative Implementation\<close>

text \<open>
Phase 3 helper: fill the flat neighbour array by walking the edge list.
The running-offset array offs tracks the next free write position per vertex.
\<close>
partial_function (heap) fill_nha where
  "fill_nha es nha offs =
    (case es of
       [] \<Rightarrow> return nha
     | (u, w) # rest \<Rightarrow>
         do { pos   \<leftarrow> Array.nth offs u;
              nha'  \<leftarrow> Array.upd pos w nha;
              offs' \<leftarrow> Array.upd u (pos + 1) offs;
              fill_nha rest nha' offs' })"

text \<open>
Main construction in three phases:
(1) Count out-degrees.
(2) Prefix-sum sweep: compute start and end indices and total edge count.
(3) Allocate the flat array and fill it with fill\_nha.
Vertices with no outgoing edges retain the dummy pair sindices[v]=1,
eindices[v]=0 (start greater than end).
\<close>
definition build_CSR ::
    "(nat \<times> nat) list \<Rightarrow> (nat array \<times> nat array \<times> nat array) Heap"
  where
  "build_CSR es \<equiv>
    let n = nverts es in
    do {
      deg   \<leftarrow> Array.new n (0 :: nat);
      deg   \<leftarrow> foldM (\<lambda>(u, _) a.
                        do { d \<leftarrow> Array.nth a u;
                             Array.upd u (d + 1) a }) es deg;
      si_arr \<leftarrow> Array.new n (1 :: nat);
      ei_arr \<leftarrow> Array.new n (0 :: nat);
      offs   \<leftarrow> Array.new n (0 :: nat);
      res    \<leftarrow> foldM
                  (\<lambda>v state.
                     do { let (si, ei, off_a, tot) = state;
                          d      \<leftarrow> Array.nth deg v;
                          si'    \<leftarrow> (if d = 0 then return si
                                     else Array.upd v tot si);
                          ei'    \<leftarrow> (if d = 0 then return ei
                                     else Array.upd v (tot + d - 1) ei);
                          off_a' \<leftarrow> (if d = 0 then return off_a
                                     else Array.upd v tot off_a);
                          return (si', ei', off_a', tot + d) })
                  [0..<n] (si_arr, ei_arr, offs, 0 :: nat);
      let (si_arr', ei_arr', offs', total) = res;
      nha   \<leftarrow> Array.new total (0 :: nat);
      nha   \<leftarrow> fill_nha es nha offs';
      return (nha, si_arr', ei_arr')
    }"

subsection \<open>Correctness of the Imperative Implementation\<close>

subsection \<open>Helper Lemmas for fill\_nha\<close>

lemma nbrs_append [simp]:
  "nbrs (xs @ ys) v = nbrs xs v @ nbrs ys v"
  unfolding nbrs_def by (simp add: filter_append)

lemma nbrs_singleton:
  "nbrs [(u, w)] v = (if u = v then [w] else [])"
  unfolding nbrs_def by simp

lemma start_off_lt_of_lt:
  "\<lbrakk>v1 < v2; i1 < length (nbrs es v1)\<rbrakk> \<Longrightarrow> start_off es v1 + i1 < start_off es v2"
proof -
  assume h1: "v1 < v2" and h2: "i1 < length (nbrs es v1)"
  have "start_off es v1 + i1 < start_off es (Suc v1)"
    using h2 by (simp add: start_off_Suc)
  also have "\<dots> \<le> start_off es v2"
    using h1 by (intro start_off_mono) simp
  finally show ?thesis .
qed

lemma build_nha_nth:
  assumes "v < n" "i < length (nbrs es v)"
  shows "build_nha es n ! (start_off es v + i) = nbrs es v ! i"
proof -
  have eq: "drop (start_off es v) (take (start_off es v + length (nbrs es v)) (build_nha es n)) = nbrs es v"
    using build_nha_nths_vertex[OF assms(1)] unfolding nths_intervall_strict_as_drop_and_take .
  have len: "start_off es v + length (nbrs es v) \<le> length (build_nha es n)"
    unfolding length_build_nha
    by (metis Suc_le_eq assms(1) start_off_Suc start_off_mono)
  have "(drop (start_off es v) (take (start_off es v + length (nbrs es v)) (build_nha es n))) ! i
        = build_nha es n ! (start_off es v + i)"
    using assms(2) len by (simp add: nth_drop nth_take)
  thus ?thesis using eq by simp
qed

lemma start_off_partition:
  "i < start_off es n \<Longrightarrow> \<exists>v < n. \<exists>j < length (nbrs es v). start_off es v + j = i"
proof (induction n)
  case 0 then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "i < start_off es n")
    case True
    then obtain v j where "v < n" "j < length (nbrs es v)" "start_off es v + j = i"
      using Suc.IH by blast
    thus ?thesis using less_Suc_eq by blast
  next
    case False
    have hlt: "i < start_off es n + length (nbrs es n)"
      using Suc.prems by (simp add: start_off_Suc)
    show ?thesis
      using False hlt
      by (intro exI[where x=n] exI[where x="i - start_off es n"]) arith
  qed
qed

lemma nha_list_eq_build_nha:
  assumes "length xs = start_off es n"
          "\<forall>v < n. \<forall>i < length (nbrs es v). xs ! (start_off es v + i) = nbrs es v ! i"
  shows "xs = build_nha es n"
proof (rule nth_equalityI)
  show "length xs = length (build_nha es n)"
    using assms(1) length_build_nha by simp
next
  fix i assume hi: "i < length xs"
  obtain v j where hvj: "v < n" "j < length (nbrs es v)" "start_off es v + j = i"
    using start_off_partition[of i es n] assms(1) length_build_nha hi by auto
  then show "xs ! i = build_nha es n ! i"
    using assms(2) build_nha_nth[of v n j es] by (auto simp: add.commute)
qed

text \<open>
Generalised correctness lemma for fill\_nha: the invariant is parameterised by
the already-processed prefix \<open>done\<close> and the remaining suffix \<open>todo\<close> with
\<open>done @ todo = es\<close>.
\<close>
lemma fill_nha_rule_gen:
  "\<lbrakk>length offs_list = nverts es;
    \<forall>v < nverts es. nbrs es v \<noteq> [] \<longrightarrow>
       offs_list ! v = start_off es v + length (nbrs dones v);
    \<forall>v < nverts es. \<forall>i < length (nbrs dones v).
       nha_list ! (start_off es v + i) = nbrs es v ! i;
    length nha_list = start_off es (nverts es);
    \<forall>(u, w) \<in> set todo. u < nverts es;
    dones @ todo = es\<rbrakk>
   \<Longrightarrow>   <nha_arr \<mapsto>\<^sub>a nha_list * offs_arr \<mapsto>\<^sub>a offs_list>
   fill_nha todo nha_arr offs_arr
   <\<lambda>r. r \<mapsto>\<^sub>a build_nha es (nverts es)>"
proof (induction todo arbitrary: dones nha_list offs_list nha_arr offs_arr)
  case Nil
  note prems = Nil.prems
  have done_eq: "dones = es" using prems(6) by simp
  show ?case
  proof -
    have nha_eq: "nha_list = build_nha es (nverts es)"
      using nha_list_eq_build_nha prems(4) prems(3)[unfolded done_eq] by simp
    show ?case
      apply (subst fill_nha.simps, simp)
      using nha_eq by sep_auto
  qed
next
  case (Cons h todo')
  obtain u w where h_eq: "h = (u, w)" by (cases h) auto
  note prems = Cons.prems
  note IH = Cons.IH
  have u_lt: "u < nverts es" using prems(5) h_eq by auto
  have nbrs_u_ne: "nbrs es u \<noteq> []"
    using prems(6) h_eq 
    by (auto simp: set_append nbrs_singleton nbrs_def)
  have pos_val: "offs_list ! u = start_off es u + length (nbrs dones u)"
    using prems(2) u_lt nbrs_u_ne by simp
  have done'_todo': "(dones @ [(u, w)]) @ todo' = es"
    using prems(6) h_eq by simp
  have nbrs_done'_ne_u: "\<And>v. v \<noteq> u 
      \<Longrightarrow> nbrs (dones @ [(u, w)]) v = nbrs dones v"
    by (simp add: nbrs_singleton)
  have nbrs_es_decomp: "nbrs es u = nbrs dones u @ [w] @ nbrs todo' u"
  proof -
    have "nbrs es u = nbrs ((dones @ [(u, w)]) @ todo') u" using done'_todo' by simp
    thus ?thesis apply (simp add: nbrs_singleton)
      by (metis append_Cons nbrs_append append_self_conv2 nbrs_singleton)
  qed
  have u_lt': "u < length offs_list" using prems(1) u_lt by simp
  have pos_lt: "offs_list ! u < length nha_list"
  proof -
    have "start_off es u + length (nbrs dones u) < start_off es (Suc u)"
      using start_off_Suc by (simp add: nbrs_es_decomp)
    also have "\<dots> \<le> start_off es (nverts es)"
      using u_lt by (intro start_off_mono) simp
    finally show ?thesis using prems(4) pos_val by simp
  qed
  have ih_A2: "\<forall>v < nverts es. nbrs es v \<noteq> [] \<longrightarrow>
      (offs_list[u := offs_list ! u + 1]) ! v =
      start_off es v + length (nbrs (dones @ [(u, w)]) v)"
  proof (intro allI impI)
    fix v assume hv: "v < nverts es" and hne: "nbrs es v \<noteq> []"
    show "(offs_list[u := offs_list ! u + 1]) ! v =
          start_off es v + length (nbrs (dones @ [(u, w)]) v)"
    proof (cases "v = u")
      case True
      thus ?thesis using pos_val u_lt' by (simp add: nbrs_singleton)
    next
      case False
      thus ?thesis using prems(2) hv hne nbrs_done'_ne_u by simp
    qed
  qed
  have ih_A3: "\<forall>v < nverts es. \<forall>i < length (nbrs (dones @ [(u, w)]) v).
      (nha_list[offs_list ! u := w]) ! (start_off es v + i) = nbrs es v ! i"
  proof (intro allI impI)
    fix v i
    assume hv: "v < nverts es" and hi: "i < length (nbrs (dones @ [(u, w)]) v)"
    show "(nha_list[offs_list ! u := w]) ! (start_off es v + i) = nbrs es v ! i"
    proof (cases "start_off es v + i = offs_list ! u")
      case True
      have vu: "v = u"
      proof (rule ccontr)
        assume "v \<noteq> u"
        hence hi': "i < length (nbrs dones v)"
          using hi nbrs_done'_ne_u by simp
        have hi_es: "i < length (nbrs es v)"
        proof -
          have "nbrs es v = nbrs dones v @ nbrs [(u, w)] v @ nbrs todo' v"
            by (metis done'_todo' append_assoc nbrs_append nbrs_singleton)
          thus ?thesis using hi' by (simp add: length_append)
        qed
        show False
        proof (cases "v < u")
          case True
          have "start_off es v + i < start_off es u"
            using start_off_lt_of_lt[OF True hi_es] .
          thus False using \<open>start_off es v + i = offs_list ! u\<close> pos_val by linarith
        next
          case False
          then have "u < v" using \<open>v \<noteq> u\<close> by simp
          have "offs_list ! u < start_off es v"
          proof -
            have "offs_list ! u < start_off es (Suc u)"
              using pos_val by (simp add: start_off_Suc nbrs_es_decomp)
            also have "\<dots> \<le> start_off es v"
              using \<open>u < v\<close> by (intro start_off_mono) simp
            finally show ?thesis .
          qed
          thus False using \<open>start_off es v + i = offs_list ! u\<close> by linarith
        qed
      qed
      have ieq: "i = length (nbrs dones u)"
        using True vu pos_val by simp
      have "(nha_list[offs_list ! u := w]) ! (start_off es v + i) = w"
        using True pos_lt prems(4) by simp
      also have "w = nbrs es u ! length (nbrs dones u)"
        by (simp add: nbrs_es_decomp nth_append)
      finally show ?thesis using vu ieq by simp
    next
      case False
      have hilen: "i < length (nbrs dones v)"
      proof (cases "v = u")
        case True
        have hlt: "i < length (nbrs dones u) + 1"
          using hi by (simp add: True nbrs_singleton)
        have "i \<noteq> length (nbrs dones u)"
        proof
          assume "i = length (nbrs dones u)"
          then have "start_off es v + i = offs_list ! u" using True pos_val by simp
          with False show False by simp
        qed
        thus ?thesis using hlt True by simp
      next
        case neq: False
        thus ?thesis using hi nbrs_done'_ne_u[OF neq] by simp
      qed
      have "(nha_list[offs_list ! u := w]) ! (start_off es v + i) =
            nha_list ! (start_off es v + i)"
        using False by simp
      also have "\<dots> = nbrs es v ! i" using prems(3) hv hilen by simp
      finally show ?thesis .
    qed
  qed
  have inst_A1: "length (offs_list[u := offs_list ! u + 1]) = nverts es"
    by (simp add: prems(1))
  have inst_A3: "\<forall>v < nverts es. \<forall>i < length (nbrs (dones @ [(u,w)]) v).
      (nha_list[offs_list ! u := w]) ! (start_off es v + i) = nbrs es v ! i"
    using ih_A3 by blast
  have inst_A4: "length (nha_list[offs_list ! u := w]) = start_off es (nverts es)"
    by (simp add: prems(4))
  have inst_A5: "\<forall>(u', w') \<in> set todo'. u' < nverts es"
    using prems(5) h_eq by (auto simp: set_append)
  note IH_inst = IH[where dones = "dones @ [(u, w)]"
                        and nha_list = "nha_list[offs_list ! u := w]"
                        and offs_list = "offs_list[u := offs_list ! u + 1]",
                    OF inst_A1 ih_A2 inst_A3 inst_A4 inst_A5 done'_todo']
  show ?case
    using IH_inst
    apply (subst fill_nha.simps, simp only: h_eq list.case)
    by (sep_auto  simp: u_lt' pos_lt)
qed

text \<open>
Correctness of fill\_nha from the initial state: offs holds the exact start
offsets and nha is initialised to all-zeros.
\<close>
lemma fill_nha_rule:

  assumes
    "length offs_list = nverts es"
    "\<forall>v < nverts es. nbrs es v \<noteq> [] \<longrightarrow> offs_list ! v = start_off es v"
    "length nha_list = start_off es (nverts es)"
    "\<forall>(u, w) \<in> set es. u < nverts es"
  shows
    "<nha_arr \<mapsto>\<^sub>a nha_list * offs_arr \<mapsto>\<^sub>a offs_list>
     fill_nha es nha_arr offs_arr
     <\<lambda>r. r \<mapsto>\<^sub>a build_nha es (nverts es)>"
  apply(rule fill_nha_rule_gen[where dones = "[]"])
  using assms nbrs_append[of "[]" undefined]
  by auto
 

text \<open>
Helper lemmas: equality of concrete lists with the abstract build functions.
\<close>

lemma build_sindices_list_eq:
  assumes "length xs = n"
          "\<forall>v < n. xs ! v = (if nbrs es v = [] then 1 else start_off es v)"
  shows "xs = build_sindices es n"
  unfolding build_sindices_def
  by (rule nth_equalityI) (use assms in simp_all)

lemma build_eindices_list_eq:
  assumes "length xs = n"
          "\<forall>v < n. xs ! v = (if nbrs es v = [] then 0
                               else start_off es v + length (nbrs es v) - 1)"
  shows "xs = build_eindices es n"
  unfolding build_eindices_def
  by (rule nth_equalityI) (use assms in simp_all)

lemma fold_update_length:
  "length (fold (\<lambda>v a. if P v then a else a[v := f v]) xs acc) = length acc"
  by (induction xs arbitrary: acc) simp_all

lemma fold_update_nth:
  assumes "distinct xs" "\<forall>v \<in> set xs. v < length acc" "w < length acc"
  shows "(fold (\<lambda>v a. if P v then a else a[v := f v]) xs acc) ! w
       = (if w \<in> set xs then (if P w then acc ! w else f w) else acc ! w)"
  using assms
proof (induction xs arbitrary: acc)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  let ?acc' = "if P x then acc else acc[x := f x]"
  have ih: "(fold (\<lambda>v a. if P v then a else a[v := f v]) xs ?acc') ! w
          = (if w \<in> set xs then (if P w then ?acc' ! w else f w) else ?acc' ! w)"
    by (rule Cons.IH) (use Cons.prems in auto)
  show ?case
  proof (cases "w = x")
    case True
    hence "w \<notin> set xs" using Cons.prems by simp
    have acc'_w: "?acc' ! w = (if P w then acc ! w else f w)"
      using True Cons.prems by (cases "P x") (simp_all add: nth_list_update_eq)
    thus ?thesis using True ih \<open>w \<notin> set xs\<close> acc'_w by simp
  next
    case False
    have acc'_w: "?acc' ! w = acc ! w"
      using False Cons.prems by (cases "P x") (simp_all add: nth_list_update_neq)
    thus ?thesis using False ih acc'_w by simp
  qed
qed

lemma fold_sindices_nth_aux:
  assumes "distinct xs" "\<forall>v \<in> set xs. v < length acc" "w < length acc"
  shows "(fold (\<lambda>v a. if filter (\<lambda>e. fst e = v) es = [] then a else a[v := start_off es v]) xs acc) ! w
       = (if w \<in> set xs then (if filter (\<lambda>e. fst e = w) es = [] then acc ! w else start_off es w) else acc ! w)"
  using assms
proof (induction xs arbitrary: acc)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  let ?acc' = "if filter (\<lambda>e. fst e = x) es = [] then acc else acc[x := start_off es x]"
  have ih: "(fold (\<lambda>v a. if filter (\<lambda>e. fst e = v) es = [] then a else a[v := start_off es v]) xs ?acc') ! w
          = (if w \<in> set xs then (if filter (\<lambda>e. fst e = w) es = [] then ?acc' ! w else start_off es w) else ?acc' ! w)"
    by (rule Cons.IH) (use Cons.prems in auto)
  show ?case
  proof (cases "w = x")
    case True
    hence "w \<notin> set xs" using Cons.prems by simp
    have acc'_w: "?acc' ! w = (if filter (\<lambda>e. fst e = w) es = [] then acc ! w else start_off es w)"
      using True Cons.prems by (simp add: nth_list_update_eq split: if_split)
    thus ?thesis using True ih \<open>w \<notin> set xs\<close> acc'_w by simp
  next
    case False
    have acc'_w: "?acc' ! w = acc ! w"
      using False Cons.prems by (simp add: nth_list_update_neq split: if_split)
    thus ?thesis using False ih acc'_w by simp
  qed
qed

lemma fold_sindices_eq:
  "fold (\<lambda>v si_a. if filter (\<lambda>e. fst e = v) es = [] then si_a else si_a[v := start_off es v]) [0..<nverts es]
     (replicate (nverts es) (Suc 0)) =
   map (\<lambda>v. if filter (\<lambda>e. fst e = v) es = [] then 1 else start_off es v) [0..<nverts es]"
proof (rule nth_equalityI)
  let ?n = "nverts es"
  let ?res = "fold (\<lambda>v si_a. if filter (\<lambda>e. fst e = v) es = [] then si_a else si_a[v := start_off es v])
                   [0..<?n] (replicate ?n (Suc 0))"
  show "length ?res = length (map (\<lambda>v. if filter (\<lambda>e. fst e = v) es = [] then 1
                                        else start_off es v) [0..<?n])"
    by (simp add: fold_update_length)
  fix i assume "i < length ?res"
  hence hi: "i < ?n" by (simp add: fold_update_length)
  have step: "?res ! i = (if i \<in> set [0..<?n]
                           then (if filter (\<lambda>e. fst e = i) es = [] then replicate ?n (Suc 0) ! i
                                 else start_off es i)
                           else replicate ?n (Suc 0) ! i)"
    by (rule fold_sindices_nth_aux) (simp_all add: hi distinct_upt)
  thus "?res ! i = map (\<lambda>v. if filter (\<lambda>e. fst e = v) es = [] then 1
                              else start_off es v) [0..<?n] ! i"
    using hi by simp
qed

lemma fold_eindices_eq:
  "fold
     (\<lambda>v ei_a.
         if filter (\<lambda>e. fst e = v) es = [] then ei_a else ei_a[v := start_off es v + length (nbrs es v) - 1])
     [0..<nverts es] (replicate (nverts es) 0) =
   map (\<lambda>v. if filter (\<lambda>e. fst e = v) es = [] then 0 else start_off es v + length (nbrs es v) - 1)
       [0..<nverts es]"
proof (rule nth_equalityI)
  let ?n = "nverts es"
  let ?res = "fold (\<lambda>v ei_a. if filter (\<lambda>e. fst e = v) es = [] then ei_a
                              else ei_a[v := start_off es v + length (nbrs es v) - 1])
                   [0..<?n] (replicate ?n 0)"
  show "length ?res = length (map (\<lambda>v. if filter (\<lambda>e. fst e = v) es = [] then 0
                                        else start_off es v + length (nbrs es v) - 1) [0..<?n])"
    by (simp add: fold_update_length)
  fix i assume "i < length ?res"
  hence hi: "i < ?n" by (simp add: fold_update_length)
  have step: "?res ! i = (if i \<in> set [0..<?n]
                           then (if filter (\<lambda>e. fst e = i) es = [] then replicate ?n 0 ! i
                                 else start_off es i + length (nbrs es i) - 1)
                           else replicate ?n 0 ! i)"
    by (rule fold_update_nth) (simp_all add: hi distinct_upt)
  thus "?res ! i = map (\<lambda>v. if filter (\<lambda>e. fst e = v) es = [] then 0
                              else start_off es v + length (nbrs es v) - 1) [0..<?n] ! i"
    using hi by simp
qed


text \<open>
Helper: nths of nha\_list over the range of vertex v equals its neighbour list,
given that each position in that range has the correct value.
\<close>
lemma fill_nha_nths:
  assumes hlen:  "length nha = start_off es (nverts es)"
      and hfill: "\<forall>v < nverts es. \<forall>i < length (nbrs es v).
                    nha ! (start_off es v + i) = nbrs es v ! i"
      and hn:    "v < nverts es"
      and hnn:   "nbrs es v \<noteq> []"
  shows "nths nha {start_off es v .. start_off es v + length (nbrs es v) - 1}
         = nbrs es v"
proof -
  let ?k = "length (nbrs es v)"
  have kpos: "0 < ?k" using hnn by simp
  have hend: "start_off es v + ?k \<le> start_off es (nverts es)"
    using start_off_end_lt_total[OF hn hnn] by auto
  have set_eq: "{start_off es v .. start_off es v + ?k - 1}
              = {start_off es v ..< start_off es v + ?k}"
    using kpos by (cases ?k) auto
  have "nths nha {start_off es v .. start_off es v + ?k - 1}
      = drop (start_off es v) (take (start_off es v + ?k) nha)"
    unfolding set_eq nths_intervall_strict_as_drop_and_take ..
  also have "\<dots> = nbrs es v"
  proof (rule nth_equalityI)
    show "length (drop (start_off es v) (take (start_off es v + ?k) nha)) = ?k"
      using hend hlen by simp
    fix i assume hi: "i < length
              (drop (start_off es v)
                (take (start_off es v + length (nbrs es v)) nha))"
    have "drop (start_off es v) (take (start_off es v + ?k) nha) ! i
         = nbrs es v ! i"
      using hfill hn hi hend hlen by simp
    thus "drop (start_off es v)
          (take (start_off es v + length (nbrs es v)) nha) !
         i =
         nbrs es v ! i"
      by presburger
  qed
  finally show ?thesis .
qed

text \<open>
Main correctness theorem: build\_CSR produces three arrays satisfying
CSR\_assn for build\_nhlists es.
\<close>
theorem build_CSR_correct:
  "<emp>
   build_CSR es
   <\<lambda>(nha_arr, si_arr, ei_arr).
      CSR_assn_raw (build_nhlists es) nha_arr si_arr ei_arr
           (build_nha es (nverts es)) (build_sindices es (nverts es)) (build_eindices es (nverts es))>"
proof -
  define n where n_def: "n = nverts es"
  have all_u_lt: "\<forall>(u, w) \<in> set es. u < n"
    unfolding n_def using nverts_source_upper by auto

  (* \<midarrow>\<midarrow> Phase 1 step: reading and incrementing a degree entry \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)
  have phase1_step:
    "\<And>xs\<^sub>1 u w' xs\<^sub>2 deg_abs deg_arr.
     \<lbrakk>length deg_abs = n;
      \<forall>v < n. deg_abs ! v = length (nbrs xs\<^sub>1 v);
      es = xs\<^sub>1 @ (u, w') # xs\<^sub>2\<rbrakk>
     \<Longrightarrow>
     <deg_arr \<mapsto>\<^sub>a deg_abs>
     do { d \<leftarrow> Array.nth deg_arr u; Array.upd u (d + 1) deg_arr }
     <\<lambda>deg_arr'. deg_arr' \<mapsto>\<^sub>a (deg_abs[u := deg_abs ! u + 1]) *
      \<up>(length (deg_abs[u := deg_abs ! u + 1]) = n \<and>(
         \<forall>v < n. (deg_abs[u := deg_abs ! u + 1]) ! v =
                  length (nbrs (xs\<^sub>1 @ [(u, w')]) v)))>"
  proof -
    fix xs\<^sub>1 u w' xs\<^sub>2 deg_abs deg_arr
    assume hlen: "length deg_abs = n"
       and hinv: "\<forall>v < n. deg_abs ! v = length (nbrs xs\<^sub>1 v)"
       and hes:  "es = xs\<^sub>1 @ (u, w') # xs\<^sub>2"
    have hu: "u < n"
      using hes all_u_lt by (auto simp: set_append)
    have hinv_upd: "\<forall>v < n. (deg_abs[u := deg_abs ! u + 1]) ! v =
                              length (nbrs (xs\<^sub>1 @ [(u, w')]) v)"
    proof (intro allI impI)
      fix v assume hv: "v < n"
      show "(deg_abs[u := deg_abs ! u + 1]) ! v =
             length (nbrs (xs\<^sub>1 @ [(u, w')]) v)"
      proof (cases "v = u")
        case True
        thus ?thesis using hinv hv hu hlen by (simp add: nbrs_singleton)
      next
        case False
        thus ?thesis using hinv hv hu hlen by (simp add: nbrs_singleton)
      qed
    qed
    show "<deg_arr \<mapsto>\<^sub>a deg_abs>
          do { d \<leftarrow> Array.nth deg_arr u; Array.upd u (d + 1) deg_arr }
          <\<lambda>deg_arr'. deg_arr' \<mapsto>\<^sub>a (deg_abs[u := deg_abs ! u + 1]) *
           \<up>(length (deg_abs[u := deg_abs ! u + 1]) = n \<and>(
              \<forall>v < n. (deg_abs[u := deg_abs ! u + 1]) ! v =
                       length (nbrs (xs\<^sub>1 @ [(u, w')]) v)))>"
      using hu hlen hinv_upd
      by sep_auto
  qed

  (* \<midarrow>\<midarrow> Phase 2 step: computing si/ei/offs for one vertex \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)
  have phase2_step:
    "\<And>xs\<^sub>1 v xs\<^sub>2 deg_abs deg_arr si_abs ei_abs offs_abs tot
         si_arr ei_arr offs_arr.
     \<lbrakk>[0..<n] = xs\<^sub>1 @ v # xs\<^sub>2;
      length deg_abs = n;
      \<forall>w < n. deg_abs ! w = length (nbrs es w);
      length si_abs = n; length ei_abs = n; length offs_abs = n;
      tot = start_off es (length xs\<^sub>1);
      \<forall>w < length xs\<^sub>1.
        si_abs ! w = (if deg_abs ! w = 0 then 1 else start_off es w) \<and>
        ei_abs ! w = (if deg_abs ! w = 0 then 0
                      else start_off es w + deg_abs ! w - 1) \<and>
        offs_abs ! w = (if deg_abs ! w = 0 then 0 else start_off es w);
      \<forall>w \<in> set xs\<^sub>2. si_abs ! w = 1 \<and> ei_abs ! w = 0 \<and> offs_abs ! w = 0\<rbrakk>
     \<Longrightarrow>
     < si_arr \<mapsto>\<^sub>a si_abs * ei_arr \<mapsto>\<^sub>a ei_abs * offs_arr \<mapsto>\<^sub>a offs_abs *
      deg_arr \<mapsto>\<^sub>a deg_abs>
     do { let (si, ei, off_a, tot') = (si_arr, ei_arr, offs_arr, tot);
          d      \<leftarrow> Array.nth deg_arr v;
          si'    \<leftarrow> (if d = 0 then return si else Array.upd v tot' si);
          ei'    \<leftarrow> (if d = 0 then return ei
                     else Array.upd v (tot' + d - 1) ei);
          off_a' \<leftarrow> (if d = 0 then return off_a
                     else Array.upd v tot' off_a);
          return (si', ei', off_a', tot' + d) }
     <\<lambda>(si_arr', ei_arr', offs_arr', tot').
        si_arr' \<mapsto>\<^sub>a (if deg_abs ! v = 0 then si_abs
                      else si_abs[v := start_off es v]) *
        ei_arr' \<mapsto>\<^sub>a (if deg_abs ! v = 0 then ei_abs
                      else ei_abs[v := start_off es v + deg_abs ! v - 1]) *
        offs_arr' \<mapsto>\<^sub>a (if deg_abs ! v = 0 then offs_abs
                        else offs_abs[v := start_off es v]) *
        deg_arr \<mapsto>\<^sub>a deg_abs *
        \<up>(tot' = start_off es (Suc (length xs\<^sub>1)) \<and>
           length (if deg_abs ! v = 0 then si_abs else si_abs[v := start_off es v]) = n \<and>
           length (if deg_abs ! v = 0 then ei_abs
                   else ei_abs[v := start_off es v + deg_abs ! v - 1]) = n \<and>
           length (if deg_abs ! v = 0 then offs_abs else offs_abs[v := start_off es v]) = n)>"
  proof -
    fix xs\<^sub>1 v xs\<^sub>2 deg_abs deg_arr si_abs ei_abs offs_abs tot
        si_arr ei_arr offs_arr
    assume hrs: "[0..<n] = xs\<^sub>1 @ v # xs\<^sub>2"
       and hlen_deg: "length deg_abs = n"
       and hdeg: "\<forall>w < n. deg_abs ! w = length (nbrs es w)"
       and hlen_si: "length si_abs = n"
       and hlen_ei: "length ei_abs = n"
       and hlen_of: "length offs_abs = n"
       and htot: "tot = start_off es (length xs\<^sub>1)"
       and hinv: "\<forall>w < length xs\<^sub>1.
                    si_abs ! w = (if deg_abs ! w = 0 then 1 else start_off es w) \<and>
                    ei_abs ! w = (if deg_abs ! w = 0 then 0
                                  else start_off es w + deg_abs ! w - 1) \<and>
                    offs_abs ! w = (if deg_abs ! w = 0 then 0 else start_off es w)"
       and hxs2: "\<forall>w \<in> set xs\<^sub>2. si_abs ! w = 1 \<and> ei_abs ! w = 0 \<and> offs_abs ! w = 0"
    have hv_lt: "v < n"
    proof -
      have "v \<in> set [0..<n]" using hrs by simp
      thus ?thesis by simp
    qed
    have hlen_xs1_eq: "length xs\<^sub>1 = v"
    proof -
      have hlt: "length xs\<^sub>1 < n"
        by (metis hrs upt_eq_lel_conv length_upt diff_zero)
      have "[0..<n] ! length xs\<^sub>1 = v"
        using hrs by (simp add: nth_append)
      moreover have "[0..<n] ! length xs\<^sub>1 = length xs\<^sub>1"
        using hlt by simp
      ultimately show ?thesis by simp
    qed
    have htot_eq: "start_off es (length xs\<^sub>1) = start_off es v"
      using hlen_xs1_eq by simp
    have htot': "tot = start_off es v"
      using htot htot_eq hlen_xs1_eq by simp
    have htot_new: "start_off es v + deg_abs ! v = start_off es (Suc v)"
      using hdeg hv_lt by (simp add: start_off_Suc)
    show "< si_arr \<mapsto>\<^sub>a si_abs * ei_arr \<mapsto>\<^sub>a ei_abs * offs_arr \<mapsto>\<^sub>a offs_abs *
          deg_arr \<mapsto>\<^sub>a deg_abs>
          do { let (si, ei, off_a, tot') = (si_arr, ei_arr, offs_arr, tot);
               d      \<leftarrow> Array.nth deg_arr v;
               si'    \<leftarrow> (if d = 0 then return si else Array.upd v tot' si);
               ei'    \<leftarrow> (if d = 0 then return ei else Array.upd v (tot' + d - 1) ei);
               off_a' \<leftarrow> (if d = 0 then return off_a else Array.upd v tot' off_a);
               return (si', ei', off_a', tot' + d) }
          <\<lambda>(si_arr', ei_arr', offs_arr', tot').
             si_arr' \<mapsto>\<^sub>a (if deg_abs ! v = 0 then si_abs
                           else si_abs[v := start_off es v]) *
             ei_arr' \<mapsto>\<^sub>a (if deg_abs ! v = 0 then ei_abs
                           else ei_abs[v := start_off es v + deg_abs ! v - 1]) *
             offs_arr' \<mapsto>\<^sub>a (if deg_abs ! v = 0 then offs_abs
                             else offs_abs[v := start_off es v]) *
             deg_arr \<mapsto>\<^sub>a deg_abs *
             \<up>(tot' = start_off es (Suc (length xs\<^sub>1)) \<and>
                length (if deg_abs ! v = 0 then si_abs
                         else si_abs[v := start_off es v]) = n \<and>
                length (if deg_abs ! v = 0 then ei_abs
                         else ei_abs[v := start_off es v + deg_abs ! v - 1]) = n \<and>
                length (if deg_abs ! v = 0 then offs_abs
                         else offs_abs[v := start_off es v]) = n)>"
      using hv_lt hlen_deg hlen_si hlen_ei hlen_of htot' htot_new hlen_xs1_eq
      by (sep_auto simp: add.commute)
  qed

  (* \<midarrow>\<midarrow> Main proof \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)
  show ?thesis
    unfolding build_CSR_def CSR_assn_raw_def Let_def n_def[symmetric]
    (* Allocate deg array *)
    apply (rule ht_bind[OF new_rule])
    (* Phase 1: count degrees with foldM *)
    subgoal for n0s
    apply(rule ht_cons_pre[OF _ ht_bind[OF foldM_refine[where
        f  = "\<lambda>(u, _) dl. dl[u := dl ! u + 1]"
        and I = "\<lambda>xs\<^sub>1 xs\<^sub>2 deg_abs deg_arr.
                   deg_arr \<mapsto>\<^sub>a deg_abs *
                   \<up>(length deg_abs = n \<and>(
                      \<forall>v < n. deg_abs ! v = length (nbrs xs\<^sub>1 v)))"
        and si = n0s and s = "replicate n 0"]]])
      subgoal
        by (sep_auto simp: nbrs_def)
    subgoal for xs\<^sub>1 x xs\<^sub>2 s si
      using phase1_step[of s xs\<^sub>1 "fst x" "snd x" xs\<^sub>2 si] all_u_lt
      by(cases x)  (sep_auto simp: nbrs_singleton)
    (* Allocate si_arr, ei_arr, offs arrays *)
    apply(rule ht_bind[OF ht_frame[OF new_rule, simplified assn_one_left]])
    apply(rule ht_bind[OF ht_frame[OF new_rule, simplified assn_one_left]])
    apply(rule ht_bind[OF ht_frame[OF new_rule, simplified assn_one_left]])
    (* Phase 2: compute prefix sums with foldM.
       Abstract fold function: f v (si_a,ei_a,of_a,tot) updates one vertex. *)
    subgoal for x xa xb xc
    apply (rule ht_cons_pre[OF _ ht_bind[OF foldM_refine[where
        f  = "\<lambda>v (si_a, ei_a, of_a, tot).
               let d = length (nbrs es v) in
               (if d = 0 then si_a else si_a[v := start_off es v],
                if d = 0 then ei_a else ei_a[v := start_off es v + d - 1],
                if d = 0 then of_a else of_a[v := start_off es v],
                tot + d)"
        and I = "\<lambda>xs\<^sub>1 xs\<^sub>2 (si_a, ei_a, of_a, tot_a) (si_arr, ei_arr, of_arr, tot_c).
                   
                     si_arr \<mapsto>\<^sub>a si_a * ei_arr \<mapsto>\<^sub>a ei_a * of_arr \<mapsto>\<^sub>a of_a *
                     x \<mapsto>\<^sub>a fold (\<lambda>(u, uu) dl. dl[u := Suc (dl ! u)]) es (replicate n 0) *
                     \<up>(length (fold (\<lambda>(u, uu) dl. dl[u := Suc (dl ! u)]) es (replicate n 0)) = n \<and>
                        (\<forall>v < n. (fold (\<lambda>(u, uu) dl. dl[u := Suc (dl ! u)]) es (replicate n 0)) ! v = length (nbrs es v)) \<and>
                        length si_a = n \<and> length ei_a = n \<and> length of_a = n \<and>
                        tot_c = tot_a \<and>
                        tot_a = start_off es (length xs\<^sub>1) \<and>
                        (\<forall>v < length xs\<^sub>1. 
                           si_a ! v = (if nbrs es v = [] then 1 else start_off es v) \<and>
                           ei_a ! v = (if nbrs es v = [] then 0
                                       else start_off es v + length (nbrs es v) - 1) \<and>
                           of_a ! v = (if nbrs es v = [] then 0 else start_off es v)) \<and>
                        (\<forall>v \<in> set xs\<^sub>2. si_a ! v = 1 \<and> ei_a ! v = 0 
                        \<and> of_a ! v = 0))"]], 
           where s2 = "(replicate n 1,replicate n 0,replicate n 0,0)"])
    subgoal 
      by sep_auto
    (* Phase 2 step subgoal *)
    subgoal for xs\<^sub>1 xx xs\<^sub>2 s si
    proof -
      obtain si_a ei_a of_a tot_a
        where s_eq: "s = (si_a, ei_a, of_a, tot_a)" by (cases s) auto
      obtain si_arr ei_arr of_arr tot_c
        where si_eq: "si = (si_arr, ei_arr, of_arr, tot_c)" by (cases si) auto
      show ?thesis
        unfolding s_eq si_eq case_prod_beta fst_conv snd_conv ex_assn_move_out
          unfolding semigroup_mult_class.mult.assoc
          unfolding merge_pure_star
          unfolding semigroup_mult_class.mult.assoc[symmetric]
          apply(rule ht_extract_pre_pure(1))
          apply(rule ht_cons_prec)
            defer 
          defer
          apply(rule phase2_step[ simplified, where deg_arr = x and v = xx and si_arr = si_arr
           and tot=tot_c and ei_arr = ei_arr and offs_arr = of_arr
            and xs\<^sub>1 = xs\<^sub>1 and xs\<^sub>2 = xs\<^sub>2
               and deg_abs = "fold (\<lambda>(u, uu) dl. dl[u := Suc (dl ! u)]) es (replicate n 0)" and si_abs = si_a and ei_abs = ei_a
              and offs_abs = of_a])
          subgoal
            by sep_auto
          subgoal 
             by (auto simp add: fold_fst_heleper)
           subgoal
               by (auto simp add: fold_fst_heleper)
          subgoal
            by sep_auto
          subgoal
            by sep_auto
          subgoal
            by sep_auto
          subgoal
            by sep_auto
          subgoal
            apply (auto simp add: fold_fst_heleper) 
            apply (metis (no_types, lifting) bot_nat_0.not_eq_extremum diff_zero length_append length_upt
                list.size(3) trans_less_add1)
            apply (metis (no_types, lifting) bot_nat_0.not_eq_extremum diff_zero length_append length_upt
                list.size(3) trans_less_add1)
            apply (metis (no_types, lifting) bot_nat_0.not_eq_extremum diff_zero length_append length_upt
                list.size(3) trans_less_add1)
            by (metis (no_types, lifting) length_0_conv length_append length_map map_nth
                trans_less_add1)+
          subgoal
            by auto
          subgoal
            by (sep_auto simp: fold_fst_heleper)
          subgoal
            apply(auto simp add: fold_fst_heleper upt_eq_lel_conv start_off_Suc Let_def  nth_list_update
                   split!: prod.split)
                  apply sep_auto
            by(metis One_nat_def not_less_less_Suc_eq)+
          done
    qed
    (* After both foldMs: allocate nha, fill it, and return. *)
    using nverts_source_upper
    apply (simp only: Let_def case_prod_beta)
    apply (sep_auto
      heap: fill_nha_rule new_rule
      simp: n_def CSR_assn_def CSR_assn_raw_def
            build_nhlists_dom_subset build_nhlists_dom build_nhlists_val four_parallel_fold
            start_off_lt_total start_off_end_lt_total all_u_lt mod_pure_star_dist)
      apply(sep_auto simp: build_nha_def build_sindices_def build_eindices_def nbrs_def 
                           start_off_def fold_sindices_eq  fold_eindices_eq)
    using build_CSR_inv[where n="nverts es", OF refl]  build_nhlists_val
      by (auto simp: build_nhlists_dom filter_empty_conv)
    done
  done
qed

end