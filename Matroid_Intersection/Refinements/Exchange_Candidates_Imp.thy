theory Exchange_Candidates_Imp
  imports Exchange_Oracles_Imp "Graph_Algorithms_Dev.BFS_Instantiation"
begin

section \<open>The Candidate Graph from Exchange Partners\<close>

text \<open>The constant candidate graph of the exchange graph search, built once from the partner
  lists of the two oracles: the neighbours of an element are the union of its partners in both
  matroids, in ascending order. It contains every exchange edge of every solution. The time
  is linear in the size of the partner lists, plus that of @{const build_CSR}.\<close>

subsection \<open>Code\<close>

fun merge_uniq :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "merge_uniq [] ys = ys"
| "merge_uniq xs [] = xs"
| "merge_uniq (x # xs) (y # ys) = 
     (if x < y then x # merge_uniq xs (y # ys) 
      else if y < x then y # merge_uniq (x # xs) ys 
      else x # merge_uniq xs ys)"

definition cand_list :: "(nat \<Rightarrow> nat list) \<Rightarrow> (nat \<Rightarrow> nat list) \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "cand_list p1 p2 n = concat (map (\<lambda> u. map (Pair u) (merge_uniq (p1 u) (p2 u))) [0..<n])"

fun cand_loop :: "('h1 \<Rightarrow> nat \<Rightarrow> nat list Heap) \<Rightarrow> ('h2 \<Rightarrow> nat \<Rightarrow> nat list Heap) \<Rightarrow> 'h1 \<Rightarrow> 'h2 \<Rightarrow> 
                  nat \<Rightarrow> (nat \<times> nat) list \<Rightarrow> (nat \<times> nat) list Heap" where
  "cand_loop p1 p2 H1 H2 0 acc = return acc"
| "cand_loop p1 p2 H1 H2 (Suc u) acc = do {
     a \<leftarrow> p1 H1 u;
     b \<leftarrow> p2 H2 u;
     cand_loop p1 p2 H1 H2 u (map (Pair u) (merge_uniq a b) @ acc) }"

definition "cand_csr_imp p1 p2 H1 H2 n = do { es \<leftarrow> cand_loop p1 p2 H1 H2 n []; build_CSR es }"

subsection \<open>Correctness\<close>

lemma set_merge_uniq: "set (merge_uniq xs ys) = set xs \<union> set ys"
  by (induction xs ys rule: merge_uniq.induct) auto

lemma sorted_merge_uniq:
  "\<lbrakk>sorted_wrt (<) xs; sorted_wrt (<) ys\<rbrakk> \<Longrightarrow> sorted_wrt (<) (merge_uniq xs ys)"
proof(induction xs ys rule: merge_uniq.induct)
  case (3 x xs y ys)
  have "\<forall> z \<in> set ys. y < z" "\<forall> z \<in> set xs. x < z"
    using 3(4,5) by simp_all
  then show ?case
    using 3 by (auto simp: set_merge_uniq)
qed simp_all

lemma nbrs_concat_Pair:
  "nbrs (concat (map (\<lambda> x. map (Pair x) (L x)) xs)) u = concat (map (\<lambda> x. if x = u then L x else []) xs)"
  by (induction xs) (simp_all add: nbrs_def filter_map comp_def)

lemma concat_if_dist:
  "distinct xs \<Longrightarrow> concat (map (\<lambda> x. if x = u then L x else []) xs) = (if u \<in> set xs then L u else [])"
  by (induction xs) auto

lemma nbrs_cand_list: "nbrs (cand_list p1 p2 n) u = (if u < n then merge_uniq (p1 u) (p2 u) else [])"
  unfolding cand_list_def nbrs_concat_Pair by (simp add: concat_if_dist)

lemma mem_cand_list: 
  "(u, v) \<in> set (cand_list p1 p2 n) \<longleftrightarrow> u < n \<and> (v \<in> set (p1 u) \<or> v \<in> set (p2 u))"
  unfolding cand_list_def by (auto simp: set_merge_uniq)

lemma build_CSR_csr3: "<emp> build_CSR es <csr3_assn (build_nhlists es)>"
  by (rule ht_cons_post[OF build_CSR_correct]) (sep_auto simp: CSR_assn_def)

locale exchange_candidates_imp =
  p1: exchange_partners_imp n indep1 orcl_prep1 ins_orcl1 exch_orcl1 pts1 pst1 pts1_imp +
  p2: exchange_partners_imp n indep2 orcl_prep2 ins_orcl2 exch_orcl2 pts2 pst2 pts2_imp
  for n indep1 orcl_prep1 ins_orcl1 exch_orcl1 pts1 pst1 pts1_imp 
    indep2 orcl_prep2 ins_orcl2 exch_orcl2 pts2 pst2 pts2_imp
begin

abbreviation "es0 \<equiv> cand_list pts1 pts2 n"

lemma cand_loop_rule:
  "<pst1 H1 * pst2 H2 * \<up>(u \<le> n)> cand_loop pts1_imp pts2_imp H1 H2 u acc 
   <\<lambda> r. pst1 H1 * pst2 H2 * \<up>(r = cand_list pts1 pts2 u @ acc)>"
proof(induction u arbitrary: acc)
  case 0
  show ?case
    by (sep_auto simp: cand_list_def)
next
  case (Suc u)
  have l: "cand_list pts1 pts2 (Suc u) = cand_list pts1 pts2 u @ map (Pair u) (merge_uniq (pts1 u) (pts2 u))"
    unfolding cand_list_def by simp
  show ?case
    by (sep_auto simp: l heap: p1.pts_imp p2.pts_imp Suc.IH)
qed

lemma cand_csr_rule:
  "<pst1 H1 * pst2 H2> cand_csr_imp pts1_imp pts2_imp H1 H2 n 
   <\<lambda> G. pst1 H1 * pst2 H2 * csr3_assn (build_nhlists es0) G>"
  unfolding cand_csr_imp_def by (sep_auto heap: cand_loop_rule build_CSR_csr3)

text \<open>The properties the exchange graph search requires of its candidate graph.\<close>

lemma cand_bound: "(u, v) \<in> set es0 \<Longrightarrow> u < n \<and> v < n"
  unfolding mem_cand_list using p1.pts_bound p2.pts_bound by blast

lemma cand_sorted: "sorted_wrt (<) (nbrs es0 u)"
  unfolding nbrs_cand_list by (simp add: sorted_merge_uniq p1.pts_sorted p2.pts_sorted)

lemma cand_cover1:
  "\<lbrakk>finite X; X \<subseteq> {0..<n}; indep1 X; indep2 X; u < n; v < n; u \<in> X; v \<notin> X;
    \<not> ins_orcl1 (orcl_prep1 X) v; exch_orcl1 (orcl_prep1 X) u v\<rbrakk> \<Longrightarrow> (u, v) \<in> set es0"
  unfolding mem_cand_list using p1.pts_cover[of X u v] by blast

lemma cand_cover2:
  "\<lbrakk>finite X; X \<subseteq> {0..<n}; indep1 X; indep2 X; u < n; v < n; u \<notin> X; v \<in> X;
    \<not> ins_orcl2 (orcl_prep2 X) u; exch_orcl2 (orcl_prep2 X) v u\<rbrakk> \<Longrightarrow> (u, v) \<in> set es0"
  unfolding mem_cand_list using p2.pts_cover[of X v u] by blast

end

end
