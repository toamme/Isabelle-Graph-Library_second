theory Capacity_Partition_Oracle_Imp
  imports Partition_Oracle_Imp
begin

section \<open>Partition Matroids with Capacities\<close>

text \<open>The carrier is partitioned into blocks by \<open>blk\<close>, and every block \<open>b\<close> has a capacity
  \<open>cap b\<close>. A set is independent iff it contains at most \<open>cap b\<close> elements of every block \<open>b\<close>.
  The unit partition matroids of @{theory Matroid_Intersection.Partition_Oracle} are the case
  \<open>cap = (\<lambda> _. 1)\<close>. The oracle works on the solution set itself: an insertion query compares
  the number of solution elements in the block of the new element with the capacity, and an
  exchange query (only asked when the block is full) compares two blocks. Imperatively, the
  counters per block of @{theory Matroid_Intersection.Partition_Oracle_Imp} and an array of
  capacities answer both in constant time; the exchange partners are again the blocks.\<close>

subsection \<open>Counting per Block\<close>

definition "blk_card blk X b = card {x \<in> X. blk x = b}"

lemma blk_card_insert:
  "\<lbrakk>finite X; x \<notin> X\<rbrakk> \<Longrightarrow>
   blk_card blk (insert x X) b = (if blk x = b then Suc (blk_card blk X b) else blk_card blk X b)"
proof-
  assume a: "finite X" "x \<notin> X"
  have f: "finite {z \<in> X. blk z = b}"
    using a(1) by simp
  show ?thesis
  proof(cases "blk x = b")
    case True
    have "{z \<in> insert x X. blk z = b} = insert x {z \<in> X. blk z = b}"
      using True by auto
    then show ?thesis
      unfolding blk_card_def using True a(2) card_insert_disjoint[OF f] by simp
  next
    case False
    have "{z \<in> insert x X. blk z = b} = {z \<in> X. blk z = b}"
      using False by auto
    then show ?thesis
      unfolding blk_card_def using False by simp
  qed
qed

lemma blk_card_delete:
  "\<lbrakk>finite X; x \<in> X\<rbrakk> \<Longrightarrow>
   blk_card blk (X - {x}) b = (if blk x = b then blk_card blk X b - 1 else blk_card blk X b)"
proof-
  assume a: "finite X" "x \<in> X"
  have "blk_card blk X b = blk_card blk (insert x (X - {x})) b"
    using a(2) by (simp add: insert_absorb)
  then show ?thesis
    using blk_card_insert[of "X - {x}" x blk b] a(1) by simp
qed

lemma blk_card_mono: "\<lbrakk>finite X; Y \<subseteq> X\<rbrakk> \<Longrightarrow> blk_card blk Y b \<le> blk_card blk X b"
  unfolding blk_card_def by (rule card_mono) auto

lemma blk_card_sum:
  "\<lbrakk>finite X; finite T; blk ` X \<subseteq> T\<rbrakk> \<Longrightarrow> card X = (\<Sum> b \<in> T. blk_card blk X b)"
  using sum.group[of X T blk "\<lambda> _. 1 :: nat"] unfolding blk_card_def by simp

lemma bcount_blk_card: "bcount bl X b = blk_card (\<lambda> i. bl ! i) X b"
  unfolding bcount_def blk_card_def ..

subsection \<open>The Matroid\<close>

locale cap_partition_matroid =
  fixes carrier :: "'a set"
    and blk :: "'a \<Rightarrow> 'b"
    and cap :: "'b \<Rightarrow> nat"
  assumes carrier_finite: "finite carrier"
begin

definition "cap_indep X = (X \<subseteq> carrier \<and> (\<forall> b. blk_card blk X b \<le> cap b))"

lemma cap_indep_finite: "cap_indep X \<Longrightarrow> finite X"
  using carrier_finite finite_subset unfolding cap_indep_def by blast

lemma cap_augment:
  assumes "cap_indep X" "cap_indep Y" "card Y < card X"
  shows "\<exists> x \<in> X - Y. cap_indep (insert x Y)"
proof-
  have fin: "finite X" "finite Y"
    using assms(1,2) cap_indep_finite by auto
  have "\<exists> b. blk_card blk Y b < blk_card blk X b"
  proof(rule ccontr)
    assume "\<nexists> b. blk_card blk Y b < blk_card blk X b"
    then have le: "blk_card blk X b \<le> blk_card blk Y b" for b
      using not_less by blast
    have "card X = (\<Sum> b \<in> blk ` (X \<union> Y). blk_card blk X b)"
      by (rule blk_card_sum) (use fin in auto)
    also have "\<dots> \<le> (\<Sum> b \<in> blk ` (X \<union> Y). blk_card blk Y b)"
      by (rule sum_mono) (rule le)
    also have "\<dots> = card Y"
      by (rule blk_card_sum[symmetric]) (use fin in auto)
    finally show False
      using assms(3) by simp
  qed
  then obtain b where b: "blk_card blk Y b < blk_card blk X b"
    by blast
  have "\<not> {z \<in> X. blk z = b} \<subseteq> {z \<in> Y. blk z = b}"
  proof
    assume "{z \<in> X. blk z = b} \<subseteq> {z \<in> Y. blk z = b}"
    then have "blk_card blk X b \<le> blk_card blk Y b"
      unfolding blk_card_def by (rule card_mono[rotated]) (use fin(2) in simp)
    then show False
      using b by simp
  qed
  then obtain x where x: "x \<in> X" "blk x = b" "x \<notin> Y"
    by blast
  have ins: "blk_card blk (insert x Y) b' =
             (if blk x = b' then Suc (blk_card blk Y b') else blk_card blk Y b')" for b'
    by (rule blk_card_insert[OF fin(2) x(3)])
  have capb: "Suc (blk_card blk Y b) \<le> cap b"
    using le_trans[OF Suc_leI[OF b]] assms(1) unfolding cap_indep_def by blast
  have "cap_indep (insert x Y)"
    unfolding cap_indep_def
  proof(intro conjI allI)
    show "insert x Y \<subseteq> carrier"
      using x(1) assms(1,2) unfolding cap_indep_def by blast
  next
    fix b'
    show "blk_card blk (insert x Y) b' \<le> cap b'"
    proof(cases "blk x = b'")
      case True
      then show ?thesis
        using ins[of b'] capb x(2) by simp
    next
      case False
      then show ?thesis
        using ins[of b'] assms(2) unfolding cap_indep_def by simp
    qed
  qed
  then show ?thesis
    using x by blast
qed

lemma cap_matroid: "matroid carrier cap_indep"
proof(unfold_locales, goal_cases)
  case 1
  then show ?case by (rule carrier_finite)
next
  case (2 X)
  then show ?case by (simp add: cap_indep_def)
next
  case 3
  have "cap_indep {}"
    by (simp add: cap_indep_def blk_card_def)
  then show ?case by blast
next
  case (4 X Y)
  have "finite X"
    using 4(1) by (rule cap_indep_finite)
  then show ?case
    using 4 blk_card_mono[of X Y blk] le_trans unfolding cap_indep_def by blast
next
  case (5 X Y)
  then show ?case
    by (intro cap_augment) simp_all
qed

sublocale cap: matroid carrier cap_indep
  by (rule cap_matroid)

lemma cap_indep_insert:
  assumes "cap_indep X" "y \<in> carrier - X"
  shows "cap_indep (insert y X) \<longleftrightarrow> blk_card blk X (blk y) < cap (blk y)"
proof-
  have fin: "finite X"
    using assms(1) by (rule cap_indep_finite)
  have ny: "y \<notin> X"
    using assms(2) by blast
  have ins: "blk_card blk (insert y X) b =
             (if blk y = b then Suc (blk_card blk X b) else blk_card blk X b)" for b
    by (rule blk_card_insert[OF fin ny])
  show ?thesis
  proof
    assume "cap_indep (insert y X)"
    then have "blk_card blk (insert y X) (blk y) \<le> cap (blk y)"
      unfolding cap_indep_def by blast
    then show "blk_card blk X (blk y) < cap (blk y)"
      using ins[of "blk y"] by simp
  next
    assume lt: "blk_card blk X (blk y) < cap (blk y)"
    show "cap_indep (insert y X)"
      unfolding cap_indep_def
    proof(intro conjI allI)
      show "insert y X \<subseteq> carrier"
        using assms unfolding cap_indep_def by blast
    next
      fix b
      show "blk_card blk (insert y X) b \<le> cap b"
        using ins[of b] lt assms(1) unfolding cap_indep_def by (cases "blk y = b") auto
    qed
  qed
qed

lemma cap_indep_exch:
  assumes "cap_indep X" "y \<in> carrier - X" "x \<in> X" "\<not> cap_indep (insert y X)"
  shows "cap_indep (insert y (X - {x})) \<longleftrightarrow> blk x = blk y"
proof-
  have fin: "finite X"
    using assms(1) by (rule cap_indep_finite)
  have "\<not> blk_card blk X (blk y) < cap (blk y)"
    using cap_indep_insert[OF assms(1,2)] assms(4) by simp
  moreover have "blk_card blk X (blk y) \<le> cap (blk y)"
    using assms(1) unfolding cap_indep_def by blast
  ultimately have full: "blk_card blk X (blk y) = cap (blk y)"
    by simp
  have ind: "cap_indep (X - {x})"
    using assms(1) by (rule cap.indep_subset) blast
  have y: "y \<in> carrier - (X - {x})"
    using assms(2) by blast
  have del: "blk_card blk (X - {x}) (blk y) =
             (if blk x = blk y then blk_card blk X (blk y) - 1 else blk_card blk X (blk y))"
    by (rule blk_card_delete[OF fin assms(3)])
  have pos: "0 < blk_card blk X (blk y)" if "blk x = blk y"
    unfolding blk_card_def using that assms(3) fin by (auto simp: card_gt_0_iff)
  show ?thesis
    using cap_indep_insert[OF ind y] del full pos by (cases "blk x = blk y") auto
qed

end

subsection \<open>The Oracle\<close>

text \<open>Solutions are sets; the oracle needs no preparation.\<close>

locale cap_partition_oracle = cap_partition_matroid
begin

definition "cap_ins X y = (blk_card blk X (blk y) < cap (blk y))"

definition "cap_exch (X :: 'a set) x y = (blk x = blk y)"

sublocale indep_oracle "\<lambda> X. X" cap_ins cap_exch carrier cap_indep "\<lambda> X. X" finite
proof(unfold_locales, goal_cases)
  case (1 X y)
  then show ?case
    using cap_indep_insert[OF 1(3,4)] by (simp add: cap_ins_def)
next
  case (2 X x y)
  then show ?case
    using cap_indep_exch[OF 2(3,4,5,6)] by (simp add: cap_exch_def)
qed

end

subsection \<open>Imperative Insertion Queries\<close>

text \<open>The capacities \<open>cap\<close> of the blocks below \<open>nb\<close> are an array. Counters, blocks, exchange
  queries and partners are those of the unit case.\<close>

definition "caps_assn nb cap Ka = Ka \<mapsto>\<^sub>a map cap [0..<nb]"

definition part_cap_ins_imp :: "nat array \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "part_cap_ins_imp Bl Ka C y = do { 
     b \<leftarrow> Array.nth Bl y; c \<leftarrow> Array.nth C b; k \<leftarrow> Array.nth Ka b; return (c < k) }"

lemma caps_of_list: "<emp> Array.of_list (map cap [0..<nb]) <caps_assn nb cap>"
  unfolding caps_assn_def by sep_auto

lemma part_cap_ins_rule:
  "<cnt_assn nb bl X C * blocks_assn n nb bl Bl * caps_assn nb cap Ka * \<up>(y < n)> 
     part_cap_ins_imp Bl Ka C y
   <\<lambda> r. cnt_assn nb bl X C * blocks_assn n nb bl Bl * caps_assn nb cap Ka * 
         \<up>(finite X \<and> r = (blk_card (\<lambda> i. bl ! i) X (bl ! y) < cap (bl ! y)))>"
  unfolding part_cap_ins_imp_def cnt_assn_def blocks_assn_def caps_assn_def 
  by (sep_auto simp: bcount_blk_card)


end
