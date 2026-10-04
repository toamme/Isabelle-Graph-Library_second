theory Partition_Oracle
  imports Exchange_Oracles
begin

section \<open>Oracles for Unit Partition Matroids\<close>

text \<open>The carrier is partitioned into blocks by \<open>blk\<close>. A set is independent iff it 
  contains at most one element per block. The prepared context is the set of covered 
  blocks, the insertion query is a membership test and the exchange query (only asked 
  for a dependent \<open>X + y\<close>) compares two blocks.\<close>

subsection \<open>The Matroid\<close>

locale unit_partition_matroid =
  fixes carrier :: "'a set"
    and blk :: "'a \<Rightarrow> 'b"
  assumes carrier_finite: "finite carrier"
begin

definition "part_indep X = (X \<subseteq> carrier \<and> inj_on blk X)"

lemma part_matroid: "matroid carrier part_indep"
proof(unfold_locales, goal_cases)
  case 1
  then show ?case by(rule carrier_finite)
next
  case (2 X)
  then show ?case by(simp add: part_indep_def)
next
  case 3
  have "part_indep {}" by(simp add: part_indep_def)
  then show ?case by blast
next
  case (4 X Y)
  then show ?case by(auto simp add: part_indep_def intro: inj_on_subset)
next
  case (5 X Y)
  have finite: "finite X" "finite Y"
    using 5(1,2) carrier_finite by(auto simp add: part_indep_def intro: finite_subset)
  have "card (blk ` Y) < card (blk ` X)"
    using 5 by(simp add: part_indep_def card_image)
  hence "\<not> blk ` X \<subseteq> blk ` Y"
    using card_mono[OF finite_imageI[OF finite(2)]] by fastforce
  then obtain x where x: "x \<in> X" "blk x \<notin> blk ` Y"
    by blast
  hence "x \<in> X - Y"
    by blast
  moreover have "part_indep (insert x Y)"
    using 5(1,2) x by(auto simp add: part_indep_def)
  ultimately show ?case by blast
qed

sublocale part: matroid carrier part_indep
  by(rule part_matroid)

lemma part_indep_insert:
  assumes "part_indep X" "y \<in> carrier - X"
  shows "part_indep (insert y X) \<longleftrightarrow> blk y \<notin> blk ` X"
proof-
  have "X - {y} = X"
    using assms(2) by blast
  thus ?thesis
    using assms by(simp add: part_indep_def)
qed

lemma part_indep_exch:
  assumes "part_indep X" "y \<in> carrier - X" "x \<in> X" "blk y \<in> blk ` X"
  shows "part_indep (insert y (X - {x})) \<longleftrightarrow> blk x = blk y"
proof-
  have inj: "inj_on blk X"
    using assms(1) by(simp add: part_indep_def)
  have "part_indep (X - {x})"
    using assms(1) part.indep_subset by blast
  hence "part_indep (insert y (X - {x})) \<longleftrightarrow> blk y \<notin> blk ` (X - {x})"
    using assms(2) by(intro part_indep_insert) auto
  moreover have "blk y \<notin> blk ` (X - {x}) \<longleftrightarrow> blk x = blk y"
  proof
    assume asm: "blk y \<notin> blk ` (X - {x})"
    obtain z where z: "z \<in> X" "blk y = blk z"
      using assms(4) by(rule imageE)
    show "blk x = blk y"
    proof(cases "z = x")
      case True
      thus ?thesis using z(2) by simp
    next
      case False
      hence "blk y \<in> blk ` (X - {x})"
        using z by(auto intro!: image_eqI[of _ _ z])
      thus ?thesis using asm by simp
    qed
  next
    assume "blk x = blk y"
    thus "blk y \<notin> blk ` (X - {x})"
      using inj assms(3) by(auto dest: inj_onD)
  qed
  ultimately show ?thesis by simp
qed

end

subsection \<open>The Oracle\<close>

locale unit_partition_oracle_spec =
  fixes blk :: "'a \<Rightarrow> 'b"
    and to_list :: "'mset \<Rightarrow> 'a list"
    and bset_empty :: "'bset"
    and bset_insert :: "'b \<Rightarrow> 'bset \<Rightarrow> 'bset"
    and bset_memb :: "'b \<Rightarrow> 'bset \<Rightarrow> bool"
begin

definition "part_prep X = foldr (\<lambda> x. bset_insert (blk x)) (to_list X) bset_empty"
definition "part_ins c y = (\<not> bset_memb (blk y) c)"
definition "part_exch (c::'bset) x y = (blk x = blk y)"

end

lemmas [code] = unit_partition_oracle_spec.part_prep_def unit_partition_oracle_spec.part_ins_def
  unit_partition_oracle_spec.part_exch_def

locale unit_partition_oracle =
  unit_partition_oracle_spec blk to_list bset_empty bset_insert bset_memb +
  unit_partition_matroid carrier blk
  for blk :: "'a \<Rightarrow> 'b"
    and to_list :: "'mset \<Rightarrow> 'a list"
    and bset_empty :: "'bset"
    and bset_insert :: "'b \<Rightarrow> 'bset \<Rightarrow> 'bset"
    and bset_memb :: "'b \<Rightarrow> 'bset \<Rightarrow> bool"
    and carrier :: "'a set" +
  fixes to_set :: "'mset \<Rightarrow> 'a set"
    and set_invar :: "'mset \<Rightarrow> bool"
    and bset_inv :: "'bset \<Rightarrow> bool"
    and bset_abs :: "'bset \<Rightarrow> 'b set"
  assumes to_list: "\<And> X. set_invar X \<Longrightarrow> set (to_list X) = to_set X"
  assumes bset_empty: "bset_inv bset_empty" "bset_abs bset_empty = {}"
  assumes bset_insert: 
    "\<And> s b. bset_inv s \<Longrightarrow> bset_inv (bset_insert b s)"
    "\<And> s b. bset_inv s \<Longrightarrow> bset_abs (bset_insert b s) = insert b (bset_abs s)"
  assumes bset_memb: "\<And> s b. bset_inv s \<Longrightarrow> bset_memb b s \<longleftrightarrow> b \<in> bset_abs s"
begin

lemma foldr_bset:
  "bset_inv (foldr (\<lambda> x. bset_insert (blk x)) xs bset_empty) \<and>
   bset_abs (foldr (\<lambda> x. bset_insert (blk x)) xs bset_empty) = blk ` set xs"
  by(induction xs) (simp_all add: bset_empty bset_insert)

lemma part_prep:
  assumes "set_invar X"
  shows "bset_inv (part_prep X)" "bset_abs (part_prep X) = blk ` to_set X"
  using foldr_bset[of "to_list X"] to_list[OF assms] by(simp_all add: part_prep_def)

lemma part_ins:
  assumes "set_invar X"
  shows "part_ins (part_prep X) y \<longleftrightarrow> blk y \<notin> blk ` to_set X"
  using part_prep[OF assms] by(simp add: part_ins_def bset_memb)

sublocale indep_oracle part_prep part_ins part_exch carrier part_indep to_set set_invar
proof(unfold_locales, goal_cases)
  case (1 X y)
  then show ?case
    using part_indep_insert[OF 1(3,4)] part_ins[OF 1(1)] by simp
next
  case (2 X x y)
  have "blk y \<in> blk ` to_set X"
    using part_indep_insert[OF 2(3,4)] 2(6) by simp
  then show ?case
    using part_indep_exch[OF 2(3,4,5)] by(simp add: part_exch_def)
qed

end

end
