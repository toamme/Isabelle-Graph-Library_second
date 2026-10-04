theory Bipartite_Arrays
  imports Partition_Oracle_Imp Basic_Matching.Matching
begin

section \<open>Bipartite Graphs Given by Two Arrays\<close>

text \<open>The graph is the set of the doubletons \<open>{fs ! i, ts ! i}\<close>. It is bipartite with the left
  endpoints on one side and the right endpoints on the other, and no edge is listed twice. A
  set of positions represents the set of its doubletons.\<close>

locale bipartite_matching_imp =
  fixes nv :: nat
    and fs ts :: "nat list"
  assumes lengths: "length ts = length fs"
    and bip: "bipartite ((\<lambda> i. {fs ! i, ts ! i}) ` {0..<length fs}) (set fs) (set ts)"
    and simple: "inj_on (\<lambda> i. (fs ! i, ts ! i)) {0..<length fs}"
    and verts: "set fs \<union> set ts \<subseteq> {..<nv}"
begin

lemma sides: "set fs \<inter> set ts = {}"
  using bip by (rule bipartite_disjointD)

lemma ends: "i < length fs \<Longrightarrow> fs ! i \<in> set fs \<and> ts ! i \<in> set ts"
  using lengths by simp

lemma left_right: "\<lbrakk>i < length fs; j < length fs\<rbrakk> \<Longrightarrow> fs ! i \<noteq> ts ! j"
proof
  assume ij: "i < length fs" "j < length fs" and eq: "fs ! i = ts ! j"
  have "fs ! i \<in> set fs" "fs ! i \<in> set ts"
    using ends[OF ij(1)] ends[OF ij(2)] unfolding eq by simp_all
  then show False
    using sides by blast
qed

lemma dbltn_inj: "inj_on (\<lambda> i. {fs ! i, ts ! i}) {0..<length fs}"
proof(rule inj_onI)
  fix i j
  assume i: "i \<in> {0..<length fs}" and j: "j \<in> {0..<length fs}" 
    and eq: "{fs ! i, ts ! i} = {fs ! j, ts ! j}"
  have "fs ! i \<in> {fs ! j, ts ! j}" "ts ! i \<in> {fs ! j, ts ! j}"
    unfolding eq[symmetric] by simp_all
  then have "fs ! i = fs ! j" "ts ! i = ts ! j"
    using left_right[of i j] left_right[of j i] i j by auto
  then show "i = j"
    using simple i j by (intro inj_onD[OF simple]) simp_all
qed

lemma blocks_in: "Fa \<mapsto>\<^sub>a fs * Ta \<mapsto>\<^sub>a ts = blocks_assn (length fs) nv fs Fa * blocks_assn (length fs) nv ts Ta"
proof-
  have "fs ! i < nv" "ts ! i < nv" if "i < length fs" for i
    using ends[OF that] verts by auto
  then have "\<forall> i < length fs. fs ! i < nv" "\<forall> i < length fs. ts ! i < nv"
    by simp_all
  then show ?thesis
    unfolding blocks_assn_def using lengths by simp
qed

end

end
