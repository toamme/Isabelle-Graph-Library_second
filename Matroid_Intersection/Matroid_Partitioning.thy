section \<open>Matroid Partitioning (Korte--Vygen \S13.6)\<close>

theory Matroid_Partitioning
  imports Matroid_Intersection
begin

text \<open>
  This theory formalises \S13.6 of Korte--Vygen, \<^emph>\<open>Combinatorial Optimization\<close>: the \<^emph>\<open>union\<close>
  (or \<^emph>\<open>sum\<close>) of finitely many matroids over a common ground set, and the Nash-Williams rank
  formula (Theorem 13.34), which is the single main theorem of the section.

  The proof of Theorem 13.34 in the book folds together several genuinely self-contained facts.
  We isolate each one as a standalone lemma:
    \<^item> the union is an \<^emph>\<open>independence system\<close> (@{text partitionable_indep_system});
    \<^item> a partition may always be replaced by a mere \<^emph>\<open>cover\<close> by independent sets, and vice versa
      (@{text partitionable_iff_cover});
    \<^item> weak duality \<open>|Y| \<le> |X - A| + (\<Sum>i r\<^sub>i(A))\<close> for a partition of \<open>Y \<subseteq> X\<close>
      (@{text partition_card_le}), hence the easy inequality of the rank formula
      (@{text partitionable_card_le_rank_formula});
    \<^item> a purely set-theoretic submodular inequality on the deleted parts
      (@{text card_Diff_Un_Int_le});
    \<^item> monotonicity and submodularity of the rank formula itself
      (@{text rank_formula_mono}, @{text rank_formula_submodular}).

  The submodular apparatus lets us discharge the Whitney direction (\<open>submodular rank \<Rightarrow> matroid\<close>,
  Theorem 13.10) \<^emph>\<open>inline\<close>: from the min-max reduction we prove the exchange (augment) property
  directly (@{text partitionable_augment_aux}).  The only ingredient left as an explicit hypothesis
  of the main theorem is the reduction itself (Edmonds' construction, Theorem 13.34's use of
  Theorem 13.31): that the rank formula is \<^emph>\<open>attained\<close> by an actual partitionable subset.  This is
  the content obtained by applying matroid intersection min-max (available in this development as
  @{thm [source] double_matroid.two_matroid_max_min_eq}) to the two auxiliary matroids on
  \<open>X \<times> {1..k}\<close> described in the book.
\<close>

subsection \<open>Definition 13.33: the union of matroids\<close>

text \<open>
  We fix a finite index set \<open>I\<close> and, for every \<open>i \<in> I\<close>, a matroid \<open>(carrier, indep i)\<close> over the
  common ground set \<open>carrier\<close>.  (Finiteness of \<open>carrier\<close> is only needed for the degenerate case
  \<open>I = {}\<close>; for a nonempty family it already follows from the matroid axioms.)
\<close>

locale matroid_partition =
  fixes carrier :: "'a set"
    and I :: "'i set"
    and indep :: "'i \<Rightarrow> 'a set \<Rightarrow> bool"
  assumes I_finite:       "finite I"
      and carrier_finite: "finite carrier"
      and matroids:       "\<And>i. i \<in> I \<Longrightarrow> matroid carrier (indep i)"
begin

text \<open>The rank function of the \<open>i\<close>-th matroid.\<close>

abbreviation r :: "'i \<Rightarrow> 'a set \<Rightarrow> nat" where
  "r i \<equiv> indep_system.lower_rank_of (indep i)"

text \<open>
  Definition 13.33.  A set \<open>X\<close> is \<^emph>\<open>partitionable\<close> if it splits into a disjoint union
  \<open>X = X\<^sub>1 \<union> \<dots> \<union> X\<^sub>k\<close> with \<open>X\<^sub>i\<close> independent in the \<open>i\<close>-th matroid.  The \<^emph>\<open>union\<close> of the family is the
  independence system with ground set \<open>carrier\<close> whose independent sets are the partitionable ones.
\<close>

definition partition_by :: "('i \<Rightarrow> 'a set) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "partition_by f X \<longleftrightarrow> (X = (\<Union>i\<in>I. f i)
                        \<and> (\<forall>i\<in>I. \<forall>j\<in>I. i \<noteq> j \<longrightarrow> f i \<inter> f j = {})
                        \<and> (\<forall>i\<in>I. indep i (f i)))"

definition partitionable :: "'a set \<Rightarrow> bool" where
  "partitionable X \<longleftrightarrow> (\<exists>f. partition_by f X)"

text \<open>
  The target of the Nash-Williams rank formula: \<open>min\<^bsub>A \<subseteq> X\<^esub> (|X - A| + \<Sum>\<^sub>i r\<^sub>i(A))\<close>.
\<close>

definition rank_formula :: "'a set \<Rightarrow> nat" where
  "rank_formula X = Min ((\<lambda>A. card (X - A) + (\<Sum>i\<in>I. r i A)) ` Pow X)"

text \<open>
  \<^bold>\<open>Matroid Partitioning Problem\<close> (Korte--Vygen, \S13.6).  Given the family of matroids, the task is
  to find a partitionable subset of maximum cardinality.  A set \<open>X\<close> is an \<^emph>\<open>optimum solution\<close> --
  \<open>partition_opt X\<close> -- if it is itself partitionable and no partitionable set has larger cardinality.
  By the Nash-Williams theorem the union is a matroid, so an optimum solution is exactly a basis of
  the union and its cardinality equals the rank of the union, \<^term>\<open>rank_formula carrier\<close>.
\<close>

definition partition_opt :: "'a set \<Rightarrow> bool" where
  "partition_opt X \<longleftrightarrow> partitionable X \<and> (\<forall>Y. partitionable Y \<longrightarrow> card Y \<le> card X)"


subsection \<open>Basic facts about a single member of the family\<close>

lemma indep_subset_carrier:
  assumes "i \<in> I" "indep i A" shows "A \<subseteq> carrier"
proof -
  interpret M: matroid carrier "indep i" using matroids[OF assms(1)] .
  show ?thesis using assms(2) M.indep_subset_carrier by blast
qed

lemma indep_empty_i: "i \<in> I \<Longrightarrow> indep i {}"
proof -
  assume "i \<in> I"
  then interpret M: matroid carrier "indep i" using matroids by simp
  show "indep i {}" using M.indep_empty by simp
qed

lemma indep_subset_i: "i \<in> I \<Longrightarrow> indep i A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> indep i B"
proof -
  assume "i \<in> I"
  then interpret M: matroid carrier "indep i" using matroids by simp
  assume "indep i A" "B \<subseteq> A"
  thus "indep i B" using M.indep_subset by blast
qed

lemma card_le_rank:
  assumes "i \<in> I" "indep i B" "B \<subseteq> A" "A \<subseteq> carrier" shows "card B \<le> r i A"
proof -
  interpret M: matroid carrier "indep i" using matroids[OF assms(1)] .
  have "M.indep_in A B" using assms(2,3) by (auto simp: M.indep_in_def)
  thus ?thesis using M.rank_of_indep_in_le[OF assms(4)] by simp
qed

lemma r_mono:
  assumes "i \<in> I" "A \<subseteq> B" "B \<subseteq> carrier" shows "r i A \<le> r i B"
proof -
  interpret M: matroid carrier "indep i" using matroids[OF assms(1)] .
  show ?thesis using M.rank_of_mono[OF assms(2,3)] by simp
qed

lemma r_submod:
  assumes "i \<in> I" "A \<subseteq> carrier" "B \<subseteq> carrier"
  shows "r i (A \<union> B) + r i (A \<inter> B) \<le> r i A + r i B"
proof -
  interpret M: matroid carrier "indep i" using matroids[OF assms(1)] .
  show ?thesis using M.rank_of_Un_Int_le[OF assms(2,3)] by simp
qed

lemma r_empty: "i \<in> I \<Longrightarrow> r i {} = 0"
proof -
  assume "i \<in> I"
  then interpret M: matroid carrier "indep i" using matroids by simp
  show "r i {} = 0" using M.rank_of_le[of "{}"] by simp
qed


subsection \<open>Elementary facts about partitionable sets\<close>

lemma partition_by_subset_carrier:
  assumes "partition_by f X" shows "X \<subseteq> carrier"
proof
  fix x assume "x \<in> X"
  then obtain i where i: "i \<in> I" "x \<in> f i" using assms by (auto simp: partition_by_def)
  have "indep i (f i)" using assms i(1) by (auto simp: partition_by_def)
  hence "f i \<subseteq> carrier" using indep_subset_carrier[OF i(1)] by blast
  thus "x \<in> carrier" using i(2) by blast
qed

lemma partitionable_subset_carrier:
  "partitionable X \<Longrightarrow> X \<subseteq> carrier"
  using partition_by_subset_carrier by (auto simp: partitionable_def)

lemma partitionable_finite:
  "partitionable X \<Longrightarrow> finite X"
  using partitionable_subset_carrier carrier_finite finite_subset by blast


subsection \<open>Standalone lemma 1: the union is an independence system\<close>

lemma partitionable_empty: "partitionable {}"
  unfolding partitionable_def partition_by_def
  by (rule exI[of _ "\<lambda>_. {}"]) (auto simp: indep_empty_i)

lemma partitionable_subset:
  assumes "partitionable X" "Y \<subseteq> X" shows "partitionable Y"
proof -
  from assms(1) obtain f where f: "partition_by f X" by (auto simp: partitionable_def)
  define g where "g \<equiv> \<lambda>i. f i \<inter> Y"
  have "partition_by g Y"
    unfolding partition_by_def
  proof (intro conjI ballI impI)
    have "(\<Union>i\<in>I. g i) = (\<Union>i\<in>I. f i) \<inter> Y" by (auto simp: g_def)
    also have "\<dots> = X \<inter> Y" using f by (simp add: partition_by_def)
    also have "\<dots> = Y" using assms(2) by blast
    finally show "Y = (\<Union>i\<in>I. g i)" by simp
  next
    fix i j assume "i \<in> I" "j \<in> I" "i \<noteq> j"
    thus "g i \<inter> g j = {}" using f by (auto simp: partition_by_def g_def)
  next
    fix i assume "i \<in> I"
    hence "indep i (f i)" using f by (simp add: partition_by_def)
    thus "indep i (g i)" using indep_subset_i[OF \<open>i \<in> I\<close>] by (auto simp: g_def)
  qed
  thus ?thesis by (auto simp: partitionable_def)
qed

lemma partitionable_indep_system: "indep_system carrier partitionable"
proof
  show "finite carrier" by (rule carrier_finite)
next
  fix X assume "partitionable X" thus "X \<subseteq> carrier" by (rule partitionable_subset_carrier)
next
  show "\<exists>X. partitionable X" using partitionable_empty by blast
next
  fix X Y assume "partitionable X" "Y \<subseteq> X" thus "partitionable Y" by (rule partitionable_subset)
qed


subsection \<open>Standalone lemma 2: partition versus cover\<close>

text \<open>
  Because each matroid is closed under subsets, requiring a \<^emph>\<open>disjoint\<close> partition is no stronger
  than requiring a mere cover by independent sets: any cover can be disjointified by assigning each
  element to one of the parts that contains it.
\<close>

lemma partitionable_iff_cover:
  "partitionable X \<longleftrightarrow> (\<exists>f. X = (\<Union>i\<in>I. f i) \<and> (\<forall>i\<in>I. indep i (f i)))"
proof
  assume "partitionable X"
  thus "\<exists>f. X = (\<Union>i\<in>I. f i) \<and> (\<forall>i\<in>I. indep i (f i))"
    by (auto simp: partitionable_def partition_by_def)
next
  assume "\<exists>f. X = (\<Union>i\<in>I. f i) \<and> (\<forall>i\<in>I. indep i (f i))"
  then obtain f where f: "X = (\<Union>i\<in>I. f i)" "\<forall>i\<in>I. indep i (f i)" by blast
  define phi where "phi \<equiv> \<lambda>x. SOME i. i \<in> I \<and> x \<in> f i"
  define g where "g \<equiv> \<lambda>i. {x \<in> X. phi x = i}"
  have phi: "phi x \<in> I \<and> x \<in> f (phi x)" if "x \<in> X" for x
  proof -
    from that have "\<exists>i. i \<in> I \<and> x \<in> f i" using f(1) by auto
    thus ?thesis unfolding phi_def by (rule someI_ex)
  qed
  have "partition_by g X"
    unfolding partition_by_def
  proof (intro conjI ballI impI)
    show "X = (\<Union>i\<in>I. g i)"
    proof
      show "X \<subseteq> (\<Union>i\<in>I. g i)" using phi by (auto simp: g_def)
      show "(\<Union>i\<in>I. g i) \<subseteq> X" by (auto simp: g_def)
    qed
  next
    fix i j assume "i \<in> I" "j \<in> I" "i \<noteq> j"
    thus "g i \<inter> g j = {}" by (auto simp: g_def)
  next
    fix i assume "i \<in> I"
    have "g i \<subseteq> f i" using phi by (auto simp: g_def)
    thus "indep i (g i)" using indep_subset_i[OF \<open>i \<in> I\<close>] f(2) \<open>i \<in> I\<close> by blast
  qed
  thus "partitionable X" by (auto simp: partitionable_def)
qed


subsection \<open>Standalone lemma 3: weak duality (the easy inequality)\<close>

text \<open>
  For any partition of a subset \<open>Y \<subseteq> X\<close> and any \<open>A \<subseteq> X\<close> the book's chain of inequalities
  \<open>|Y| = |Y - A| + |Y \<inter> A| \<le> |X - A| + \<Sum>\<^sub>i |Y\<^sub>i \<inter> A| \<le> |X - A| + \<Sum>\<^sub>i r\<^sub>i(A)\<close> holds.
\<close>

lemma partition_card_le:
  assumes pf: "partition_by f Y" and YX: "Y \<subseteq> X" and AX: "A \<subseteq> X" and Xc: "X \<subseteq> carrier"
  shows "card Y \<le> card (X - A) + (\<Sum>i\<in>I. r i A)"
proof -
  have finX: "finite X" using Xc carrier_finite finite_subset by blast
  have finY: "finite Y" using YX finX finite_subset by blast
  have Yeq: "Y = (\<Union>i\<in>I. f i)" and disj: "\<forall>i\<in>I. \<forall>j\<in>I. i \<noteq> j \<longrightarrow> f i \<inter> f j = {}"
    and indf: "\<forall>i\<in>I. indep i (f i)" using pf by (auto simp: partition_by_def)
  have finfi: "finite (f i)" if "i \<in> I" for i using Yeq that finY by (auto intro: finite_subset)
  \<comment> \<open>split off the part inside \<open>A\<close>\<close>
  have "card Y = card (Y \<inter> A) + card (Y - A)" using finY by (simp add: card_Int_Diff)
  moreover
  \<comment> \<open>the part outside \<open>A\<close> is bounded by \<open>|X - A|\<close>\<close>
  have "card (Y - A) \<le> card (X - A)" using YX finX by (auto intro!: card_mono)
  moreover
  \<comment> \<open>the part inside \<open>A\<close> is a disjoint union of the traces\<close>
  have YintA: "Y \<inter> A = (\<Union>i\<in>I. f i \<inter> A)" using Yeq by auto
  have "card (Y \<inter> A) = (\<Sum>i\<in>I. card (f i \<inter> A))"
    unfolding YintA
    using I_finite finfi disj by (subst card_UN_disjoint) auto
  moreover
  have "(\<Sum>i\<in>I. card (f i \<inter> A)) \<le> (\<Sum>i\<in>I. r i A)"
  proof (rule sum_mono)
    fix i assume "i \<in> I"
    have "indep i (f i \<inter> A)" using indf \<open>i \<in> I\<close> indep_subset_i[OF \<open>i \<in> I\<close>] by blast
    thus "card (f i \<inter> A) \<le> r i A"
      using card_le_rank[OF \<open>i \<in> I\<close>, of "f i \<inter> A" A] AX Xc by blast
  qed
  ultimately show ?thesis by linarith
qed


subsection \<open>Standalone lemma 4: the rank formula bounds every partitionable subset\<close>

lemma rank_formula_set_finite_nonempty:
  assumes "X \<subseteq> carrier"
  shows "finite ((\<lambda>A. card (X - A) + (\<Sum>i\<in>I. r i A)) ` Pow X)"
    and "((\<lambda>A. card (X - A) + (\<Sum>i\<in>I. r i A)) ` Pow X) \<noteq> {}"
proof -
  have "finite X" using assms carrier_finite finite_subset by blast
  thus "finite ((\<lambda>A. card (X - A) + (\<Sum>i\<in>I. r i A)) ` Pow X)" by simp
  show "((\<lambda>A. card (X - A) + (\<Sum>i\<in>I. r i A)) ` Pow X) \<noteq> {}" by blast
qed

lemma rank_formula_le:
  assumes "A \<subseteq> X" "X \<subseteq> carrier"
  shows "rank_formula X \<le> card (X - A) + (\<Sum>i\<in>I. r i A)"
  unfolding rank_formula_def
  using rank_formula_set_finite_nonempty[OF assms(2)] assms(1)
  by (auto intro!: Min_le)

lemma partitionable_card_le_rank_formula:
  assumes "partitionable Y" "Y \<subseteq> X" "X \<subseteq> carrier"
  shows "card Y \<le> rank_formula X"
  unfolding rank_formula_def
  using rank_formula_set_finite_nonempty[OF assms(3)]
proof (subst Min_ge_iff, goal_cases)
  case 3
  show ?case
  proof (intro ballI)
    fix v assume "v \<in> (\<lambda>A. card (X - A) + (\<Sum>i\<in>I. r i A)) ` Pow X"
    then obtain A where A: "A \<subseteq> X" "v = card (X - A) + (\<Sum>i\<in>I. r i A)" by auto
    from assms(1) obtain f where "partition_by f Y" by (auto simp: partitionable_def)
    thus "card Y \<le> v" using partition_card_le[OF _ assms(2) A(1) assms(3)] A(2) by simp
  qed
qed auto


subsection \<open>Standalone lemma 5: a set-theoretic submodular inequality\<close>

text \<open>
  The purely combinatorial core of the submodularity argument: the deleted parts satisfy
  \<open>|(X \<union> Y) - (A \<union> B)| + |(X \<inter> Y) - (A \<inter> B)| \<le> |X - A| + |Y - B|\<close>.
\<close>

lemma card_Diff_Un_Int_le:
  assumes "finite X" "finite Y"
  shows "card ((X \<union> Y) - (A \<union> B)) + card ((X \<inter> Y) - (A \<inter> B))
           \<le> card (X - A) + card (Y - B)"
proof -
  let ?P = "(X \<union> Y) - (A \<union> B)" and ?Q = "(X \<inter> Y) - (A \<inter> B)"
  let ?U = "X - A" and ?V = "Y - B"
  have finU: "finite ?U" and finV: "finite ?V"
    and finP: "finite ?P" and finQ: "finite ?Q" using assms by auto
  have PQ_un: "?P \<union> ?Q \<subseteq> ?U \<union> ?V" by auto
  have PQ_int: "?P \<inter> ?Q \<subseteq> ?U \<inter> ?V" by auto
  have "card ?P + card ?Q = card (?P \<union> ?Q) + card (?P \<inter> ?Q)"
    by (rule card_Un_Int[OF finP finQ])
  also have "card (?P \<union> ?Q) \<le> card (?U \<union> ?V)"
    using PQ_un finU finV by (intro card_mono) auto
  moreover have "card (?P \<inter> ?Q) \<le> card (?U \<inter> ?V)"
    using PQ_int finU finV by (intro card_mono) auto
  ultimately have "card ?P + card ?Q \<le> card (?U \<union> ?V) + card (?U \<inter> ?V)" by linarith
  also have "card (?U \<union> ?V) + card (?U \<inter> ?V) = card ?U + card ?V"
    by (rule card_Un_Int[OF finU finV, symmetric])
  finally show ?thesis .
qed


subsection \<open>Standalone lemma 6: the rank formula is monotone and submodular\<close>

lemma rank_formula_attained:
  assumes "X \<subseteq> carrier"
  shows "\<exists>A\<subseteq>X. rank_formula X = card (X - A) + (\<Sum>i\<in>I. r i A)"
proof -
  have "rank_formula X \<in> (\<lambda>A. card (X - A) + (\<Sum>i\<in>I. r i A)) ` Pow X"
    unfolding rank_formula_def
    using rank_formula_set_finite_nonempty[OF assms] by (auto intro: Min_in)
  thus ?thesis by auto
qed

lemma rank_formula_mono:
  assumes "X \<subseteq> Y" "Y \<subseteq> carrier" shows "rank_formula X \<le> rank_formula Y"
proof -
  have Xc: "X \<subseteq> carrier" using assms by blast
  have finY: "finite Y" using assms(2) carrier_finite finite_subset by blast
  obtain B where B: "B \<subseteq> Y" "rank_formula Y = card (Y - B) + (\<Sum>i\<in>I. r i B)"
    using rank_formula_attained[OF assms(2)] by blast
  have set_eq: "X - B \<inter> X = X - B" by blast
  have "rank_formula X \<le> card (X - (B \<inter> X)) + (\<Sum>i\<in>I. r i (B \<inter> X))"
    using rank_formula_le[of "B \<inter> X" X] Xc by blast
  also have "card (X - (B \<inter> X)) = card (X - B)" using set_eq by simp
  also have "card (X - B) \<le> card (Y - B)"
    using assms(1) finY by (auto intro!: card_mono)
  also have "(\<Sum>i\<in>I. r i (B \<inter> X)) \<le> (\<Sum>i\<in>I. r i B)"
  proof (rule sum_mono)
    fix i assume "i \<in> I"
    have "B \<subseteq> carrier" using B(1) assms(2) by blast
    thus "r i (B \<inter> X) \<le> r i B" using r_mono[OF \<open>i \<in> I\<close>, of "B \<inter> X" B] by blast
  qed
  ultimately show ?thesis using B(2) by linarith
qed

lemma rank_formula_submodular:
  assumes Xc: "X \<subseteq> carrier" and Yc: "Y \<subseteq> carrier"
  shows "rank_formula (X \<union> Y) + rank_formula (X \<inter> Y) \<le> rank_formula X + rank_formula Y"
proof -
  have finX: "finite X" and finY: "finite Y"
    using Xc Yc carrier_finite finite_subset by blast+
  obtain A where A: "A \<subseteq> X" "rank_formula X = card (X - A) + (\<Sum>i\<in>I. r i A)"
    using rank_formula_attained[OF Xc] by blast
  obtain B where B: "B \<subseteq> Y" "rank_formula Y = card (Y - B) + (\<Sum>i\<in>I. r i B)"
    using rank_formula_attained[OF Yc] by blast
  have Ac: "A \<subseteq> carrier" and Bc: "B \<subseteq> carrier" using A(1) B(1) Xc Yc by blast+
  \<comment> \<open>apply the rank-formula bound at the witnesses \<open>A \<union> B\<close> and \<open>A \<inter> B\<close>\<close>
  have le1: "rank_formula (X \<union> Y) \<le> card ((X \<union> Y) - (A \<union> B)) + (\<Sum>i\<in>I. r i (A \<union> B))"
    using rank_formula_le[of "A \<union> B" "X \<union> Y"] A(1) B(1) Xc Yc by blast
  have le2: "rank_formula (X \<inter> Y) \<le> card ((X \<inter> Y) - (A \<inter> B)) + (\<Sum>i\<in>I. r i (A \<inter> B))"
    using rank_formula_le[of "A \<inter> B" "X \<inter> Y"] A(1) B(1) Xc by blast
  \<comment> \<open>the set-part is submodular\<close>
  have card_part: "card ((X \<union> Y) - (A \<union> B)) + card ((X \<inter> Y) - (A \<inter> B))
                     \<le> card (X - A) + card (Y - B)"
    by (rule card_Diff_Un_Int_le[OF finX finY])
  \<comment> \<open>the rank-part is submodular in each matroid\<close>
  have "(\<Sum>i\<in>I. r i (A \<union> B)) + (\<Sum>i\<in>I. r i (A \<inter> B))
          = (\<Sum>i\<in>I. r i (A \<union> B) + r i (A \<inter> B))"
    by (simp add: sum.distrib)
  also have "\<dots> \<le> (\<Sum>i\<in>I. r i A + r i B)"
    by (rule sum_mono) (rule r_submod[OF _ Ac Bc])
  also have "\<dots> = (\<Sum>i\<in>I. r i A) + (\<Sum>i\<in>I. r i B)" by (simp add: sum.distrib)
  finally have rank_part: "(\<Sum>i\<in>I. r i (A \<union> B)) + (\<Sum>i\<in>I. r i (A \<inter> B))
                             \<le> (\<Sum>i\<in>I. r i A) + (\<Sum>i\<in>I. r i B)" .
  from le1 le2 card_part rank_part show ?thesis using A(2) B(2) by linarith
qed


subsection \<open>The main theorem: Nash-Williams (Theorem 13.34)\<close>

text \<open>
  We first collect the consequences of monotonicity and submodularity that turn the rank formula
  into a genuine matroid rank function (the Whitney direction of Theorem 13.10): a unit-increase
  law and the ``absorption'' lemma familiar from the AFP @{theory Matroids.Matroid} development.
\<close>

lemma rank_formula_insert_le:
  assumes "X \<subseteq> carrier" "x \<in> carrier"
  shows "rank_formula (insert x X) \<le> Suc (rank_formula X)"
proof -
  obtain A where A: "A \<subseteq> X" "rank_formula X = card (X - A) + (\<Sum>i\<in>I. r i A)"
    using rank_formula_attained[OF assms(1)] by blast
  have finXA: "finite (X - A)" using assms(1) carrier_finite finite_subset by blast
  have "A \<subseteq> insert x X" using A(1) by blast
  hence "rank_formula (insert x X) \<le> card (insert x X - A) + (\<Sum>i\<in>I. r i A)"
    using rank_formula_le[of A "insert x X"] assms by blast
  moreover have "card (insert x X - A) \<le> Suc (card (X - A))"
  proof -
    have sub: "insert x X - A \<subseteq> insert x (X - A)" by blast
    have "card (insert x X - A) \<le> card (insert x (X - A))"
      using card_mono[OF _ sub] finXA by simp
    also have "\<dots> \<le> Suc (card (X - A))" using finXA by (simp add: card_insert_if)
    finally show ?thesis .
  qed
  ultimately show ?thesis using A(2) by linarith
qed

lemma rank_formula_Un_absorbI:
  assumes "X \<subseteq> carrier" "Y \<subseteq> carrier"
  assumes "\<And>y. y \<in> Y - X \<Longrightarrow> rank_formula (insert y X) = rank_formula X"
  shows "rank_formula (X \<union> Y) = rank_formula X"
proof -
  have "finite (Y - X)" using finite_subset[OF \<open>Y \<subseteq> carrier\<close>] carrier_finite by auto
  then show ?thesis using assms
  proof (induction "Y - X" arbitrary: Y rule: finite_induct)
    case empty
    then have "X \<union> Y = X" by auto
    then show ?case by auto
  next
    case (insert y F)
    have "rank_formula (X \<union> Y) + rank_formula X \<le> rank_formula X + rank_formula X"
    proof -
      have "rank_formula (X \<union> Y) + rank_formula X
              = rank_formula ((X \<union> (Y - {y})) \<union> (insert y X))
                + rank_formula ((X \<union> (Y - {y})) \<inter> (insert y X))"
      proof -
        have "X \<union> Y = (X \<union> (Y - {y})) \<union> (insert y X)"
             "X = (X \<union> (Y - {y})) \<inter> (insert y X)" using insert by auto
        then show ?thesis by auto
      qed
      also have "\<dots> \<le> rank_formula (X \<union> (Y - {y})) + rank_formula (insert y X)"
        using insert by (intro rank_formula_submodular) auto
      also have "\<dots> = rank_formula (X \<union> (Y - {y})) + rank_formula X"
      proof -
        have "y \<in> Y - X" using insert by auto
        then show ?thesis using insert by auto
      qed
      also have "\<dots> = rank_formula X + rank_formula X"
      proof -
        have "F = (Y - {y}) - X" "Y - {y} \<subseteq> carrier" using insert by auto
        then show ?thesis using insert insert(3)[of "Y - {y}"] by auto
      qed
      finally show ?thesis .
    qed
    moreover have "rank_formula (X \<union> Y) + rank_formula X \<ge> rank_formula X + rank_formula X"
      using insert rank_formula_mono by auto
    ultimately show ?case by auto
  qed
qed

lemma rank_formula_le_card:
  assumes "X \<subseteq> carrier" shows "rank_formula X \<le> card X"
proof -
  have "rank_formula X \<le> card (X - {}) + (\<Sum>i\<in>I. r i {})"
    using rank_formula_le[of "{}" X] assms by blast
  also have "\<dots> = card X" by (simp add: r_empty)
  finally show ?thesis .
qed

lemma partitionable_imp_rank_formula_eq_card:
  assumes "partitionable X" shows "rank_formula X = card X"
proof -
  have Xc: "X \<subseteq> carrier" using assms partitionable_subset_carrier by blast
  have "card X \<le> rank_formula X"
    using partitionable_card_le_rank_formula[OF assms subset_refl Xc] .
  moreover have "rank_formula X \<le> card X" using rank_formula_le_card[OF Xc] .
  ultimately show ?thesis by simp
qed

text \<open>
  The one deep ingredient of Theorem 13.34 is the reduction to matroid intersection (Edmonds'
  construction): the rank formula is \<^emph>\<open>attained\<close> by an actual partitionable subset.  We take it as an
  explicit hypothesis @{text attn}; it is exactly what applying the matroid-intersection min-max
  theorem @{thm [source] double_matroid.two_matroid_max_min_eq} to the two auxiliary matroids of the
  book yields.  Everything else --- including matroid-ness --- is derived from it below.
\<close>

lemma rank_full_imp_partitionable:
  assumes attn: "\<And>Z. Z \<subseteq> carrier \<Longrightarrow> \<exists>Y. partitionable Y \<and> Y \<subseteq> Z \<and> card Y = rank_formula Z"
    and "X \<subseteq> carrier" "rank_formula X = card X"
  shows "partitionable X"
proof -
  obtain Y where Y: "partitionable Y" "Y \<subseteq> X" "card Y = rank_formula X"
    using attn[OF assms(2)] by blast
  have "finite X" using assms(2) carrier_finite finite_subset by blast
  hence "Y = X" using Y(2,3) assms(3) by (simp add: card_subset_eq)
  thus ?thesis using Y(1) by simp
qed

text \<open>
  The exchange property.  If no element of \<open>P - Q\<close> can be added to \<open>Q\<close>, then --- by unit-increase and
  the converse above --- none of them raises the rank of \<open>Q\<close>; absorption then collapses the rank of
  \<open>Q \<union> P\<close> down to \<open>|Q|\<close>, contradicting \<open>|P| > |Q|\<close>.  This is the inline Whitney argument (Thm 13.10).
\<close>

lemma partitionable_augment_aux:
  assumes attn: "\<And>Z. Z \<subseteq> carrier \<Longrightarrow> \<exists>Y. partitionable Y \<and> Y \<subseteq> Z \<and> card Y = rank_formula Z"
    and P: "partitionable P" and Q: "partitionable Q" and card_eq: "card P = Suc (card Q)"
  shows "\<exists>e\<in>P - Q. partitionable (insert e Q)"
proof (rule ccontr)
  assume noaug: "\<not> (\<exists>e\<in>P - Q. partitionable (insert e Q))"
  have Pc: "P \<subseteq> carrier" and Qc: "Q \<subseteq> carrier"
    using P Q partitionable_subset_carrier by blast+
  have finQ: "finite Q" using Q partitionable_finite by blast
  have rQ: "rank_formula Q = card Q" using Q partitionable_imp_rank_formula_eq_card by blast
  \<comment> \<open>no element of \<open>P - Q\<close> raises the rank of \<open>Q\<close>\<close>
  have flat: "rank_formula (insert e Q) = rank_formula Q" if e: "e \<in> P - Q" for e
  proof -
    have ec: "e \<in> carrier" using e Pc by blast
    have enotQ: "e \<notin> Q" using e by blast
    have "rank_formula Q \<le> rank_formula (insert e Q)"
      using rank_formula_mono[of Q "insert e Q"] Qc ec by blast
    moreover have "rank_formula (insert e Q) \<le> Suc (rank_formula Q)"
      using rank_formula_insert_le[OF Qc ec] .
    moreover have "rank_formula (insert e Q) \<noteq> Suc (rank_formula Q)"
    proof
      assume "rank_formula (insert e Q) = Suc (rank_formula Q)"
      hence "rank_formula (insert e Q) = card (insert e Q)"
        using rQ enotQ finQ by simp
      hence "partitionable (insert e Q)"
        using rank_full_imp_partitionable[OF attn] Qc ec by blast
      thus False using noaug e by blast
    qed
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>hence the whole of \<open>P\<close> can be absorbed without changing the rank\<close>
  have "rank_formula (Q \<union> P) = rank_formula Q"
    using flat by (intro rank_formula_Un_absorbI[OF Qc Pc]) auto
  hence "rank_formula (Q \<union> P) = card Q" using rQ by simp
  moreover have "card P \<le> rank_formula (Q \<union> P)"
    using partitionable_card_le_rank_formula[OF P _ ] Qc Pc by blast
  ultimately show False using card_eq by simp
qed

lemma union_is_matroid:
  assumes attn: "\<And>Z. Z \<subseteq> carrier \<Longrightarrow> \<exists>Y. partitionable Y \<and> Y \<subseteq> Z \<and> card Y = rank_formula Z"
  shows "matroid carrier partitionable"
proof (rule matroid.intro[OF partitionable_indep_system])
  show "matroid_axioms partitionable"
    unfolding matroid_axioms_def
  proof (intro allI impI)
    fix P Q assume "partitionable P" "partitionable Q" "card P = Suc (card Q)"
    thus "\<exists>x\<in>P - Q. partitionable (insert x Q)"
      using partitionable_augment_aux[OF attn, of P Q] by blast
  qed
qed

lemma nash_williams_rank:
  assumes attn: "\<And>Z. Z \<subseteq> carrier \<Longrightarrow> \<exists>Y. partitionable Y \<and> Y \<subseteq> Z \<and> card Y = rank_formula Z"
    and Xc: "X \<subseteq> carrier"
  shows "indep_system.lower_rank_of partitionable X = rank_formula X"
proof -
  note Umat = union_is_matroid[OF attn]
  interpret US: indep_system carrier partitionable by (rule partitionable_indep_system)
  have ge: "rank_formula X \<le> US.lower_rank_of X"
  proof -
    obtain Y where Y: "partitionable Y" "Y \<subseteq> X" "card Y = rank_formula X"
      using attn[OF Xc] by blast
    have "US.indep_in X Y" using Y(1,2) by (auto simp: US.indep_in_def)
    hence "card Y \<le> US.lower_rank_of X" using matroid.rank_of_indep_in_le[OF Umat Xc] by blast
    thus ?thesis using Y(3) by simp
  qed
  have le: "US.lower_rank_of X \<le> rank_formula X"
  proof -
    obtain B where B: "US.basis_in X B" using US.basis_in_ex[OF Xc] by blast
    have Bpart: "partitionable B" and BX: "B \<subseteq> X"
      using US.basis_in_indep_in[OF Xc B] US.indep_in_indep US.indep_in_subset_carrier by blast+
    have "US.lower_rank_of X = card B" using matroid.rank_of_eq_card_basis_in[OF Umat Xc B] .
    also have "card B \<le> rank_formula X" using partitionable_card_le_rank_formula[OF Bpart BX Xc] .
    finally show ?thesis .
  qed
  show "indep_system.lower_rank_of partitionable X = rank_formula X" using ge le by linarith
qed

text \<open>
  Theorem 13.34 (Nash-Williams).  The union of the matroids is itself a matroid, and its rank
  function is the rank formula.
\<close>

theorem nash_williams:
  assumes attn: "\<And>Z. Z \<subseteq> carrier \<Longrightarrow> \<exists>Y. partitionable Y \<and> Y \<subseteq> Z \<and> card Y = rank_formula Z"
  shows "matroid carrier partitionable"
    and "X \<subseteq> carrier \<Longrightarrow> indep_system.lower_rank_of partitionable X = rank_formula X"
  using union_is_matroid[OF attn] nash_williams_rank[OF attn] by blast+

end


subsection \<open>Discharging the reduction: Edmonds' two auxiliary matroids\<close>

text \<open>
  We now discharge the hypothesis @{text attn} of Theorem 13.34, obtaining the unconditional
  statement.  Following Edmonds' construction (the proof of Theorem 13.34 in Korte--Vygen), for a
  fixed \<open>X \<subseteq> carrier\<close> we build two matroids on the ground set \<open>X \<times> I\<close> (the \<open>|I|\<close> copies of \<open>X\<close>):
    \<^item> the \<^emph>\<open>direct sum\<close> \<open>pindep1\<close>, whose independent sets are those whose \<open>i\<close>-th section is
      independent in the \<open>i\<close>-th matroid; its rank is \<open>\<Sum>i r\<^sub>i(section i)\<close>;
    \<^item> the \<^emph>\<open>partition matroid\<close> \<open>pindep2\<close>, whose independent sets are those on which the first
      projection is injective (at most one copy of each element); its rank is the number of
      distinct elements used.
  A common independent set of the two corresponds to a partition of a subset of \<open>X\<close>, so the
  matroid-intersection min-max theorem @{thm [source] double_matroid.two_matroid_max_min_eq}
  yields that the largest partitionable subset of \<open>X\<close> has cardinality \<open>rank_formula X\<close>.
\<close>

context matroid_partition
begin

text \<open>The \<open>i\<close>-th section of \<open>R \<subseteq> X \<times> I\<close> is just the fibre \<open>R\<inverse> `` {i}\<close> of the relation \<open>R\<close>;
  we only introduce the notation \<open>sect\<close> for readability, together with its unfolding lemma.\<close>

abbreviation sect :: "('a \<times> 'i) set \<Rightarrow> 'i \<Rightarrow> 'a set" where
  "sect R i \<equiv> R\<inverse> `` {i}"

lemma sect_def: "sect R i = {e. (e, i) \<in> R}"
  by auto

definition pindep1 :: "'a set \<Rightarrow> ('a \<times> 'i) set \<Rightarrow> bool" where
  "pindep1 X Q \<longleftrightarrow> Q \<subseteq> X \<times> I \<and> (\<forall>i\<in>I. indep i (sect Q i))"

definition pindep2 :: "'a set \<Rightarrow> ('a \<times> 'i) set \<Rightarrow> bool" where
  "pindep2 X Q \<longleftrightarrow> Q \<subseteq> X \<times> I \<and> inj_on fst Q"

lemma sect_subset_X: "R \<subseteq> X \<times> I \<Longrightarrow> sect R i \<subseteq> X"
  by (auto simp: sect_def)

lemma sect_mono: "R \<subseteq> S \<Longrightarrow> sect R i \<subseteq> sect S i"
  by (auto simp: sect_def)

lemma sect_insert:
  "sect (insert (e, i0) Q) i = (if i = i0 then insert e (sect Q i) else sect Q i)"
  by (auto simp: sect_def)

lemma finite_carr': "X \<subseteq> carrier \<Longrightarrow> finite (X \<times> I)"
  using carrier_finite I_finite finite_subset by blast

lemma card_eq_sum_sect:
  assumes "R \<subseteq> X \<times> I" "finite X"
  shows "card R = (\<Sum>i\<in>I. card (sect R i))"
proof -
  have finR: "finite R" using assms I_finite by (auto intro: finite_subset)
  have "R = (\<Union>i\<in>I. (\<lambda>e. (e, i)) ` sect R i)"
    using assms(1) by (auto simp: sect_def)
  moreover have "card (\<Union>i\<in>I. (\<lambda>e. (e, i)) ` sect R i) = (\<Sum>i\<in>I. card ((\<lambda>e. (e, i)) ` sect R i))"
    using I_finite finR by (intro card_UN_disjoint) (auto simp: sect_def intro: finite_subset)
  moreover have "\<And>i. card ((\<lambda>e. (e, i)) ` sect R i) = card (sect R i)"
    by (intro card_image) (auto simp: inj_on_def)
  ultimately show ?thesis by simp
qed


subsubsection \<open>The partition matroid\<close>

lemma indep_system_pindep2:
  assumes "X \<subseteq> carrier" shows "indep_system (X \<times> I) (pindep2 X)"
proof
  show "finite (X \<times> I)" by (rule finite_carr'[OF assms])
next
  fix Q assume "pindep2 X Q" thus "Q \<subseteq> X \<times> I" by (simp add: pindep2_def)
next
  show "\<exists>Q. pindep2 X Q" by (rule exI[of _ "{}"]) (simp add: pindep2_def)
next
  fix Q P assume "pindep2 X Q" "P \<subseteq> Q"
  thus "pindep2 X P" by (auto simp: pindep2_def elim: inj_on_subset)
qed

lemma matroid_pindep2:
  assumes XC: "X \<subseteq> carrier" shows "matroid (X \<times> I) (pindep2 X)"
proof (rule matroid.intro[OF indep_system_pindep2[OF XC]], unfold matroid_axioms_def, intro allI impI)
  fix P Q assume P: "pindep2 X P" and Q: "pindep2 X Q" and c: "card P = Suc (card Q)"
  have finXI: "finite (X \<times> I)" by (rule finite_carr'[OF XC])
  have finP: "finite P" and finQ: "finite Q"
    using P Q finXI finite_subset by (auto simp: pindep2_def)
  have iP: "inj_on fst P" and iQ: "inj_on fst Q" using P Q by (auto simp: pindep2_def)
  have "card (fst ` Q) = card Q" using iQ by (simp add: card_image)
  moreover have "card (fst ` P) = card P" using iP by (simp add: card_image)
  ultimately have lt: "card (fst ` Q) < card (fst ` P)" using c by simp
  have "fst ` P - fst ` Q \<noteq> {}"
  proof
    assume "fst ` P - fst ` Q = {}"
    hence "fst ` P \<subseteq> fst ` Q" by blast
    hence "card (fst ` P) \<le> card (fst ` Q)" using finQ by (auto intro: card_mono)
    thus False using lt by simp
  qed
  then obtain e where e: "e \<in> fst ` P" "e \<notin> fst ` Q" by blast
  then obtain i where ei: "(e, i) \<in> P" by auto
  have notinQ: "(e, i) \<notin> Q" using e(2) by (metis fst_conv rev_image_eqI)
  have "pindep2 X (insert (e, i) Q)"
    using Q ei P e(2) by (auto simp: pindep2_def)
  thus "\<exists>x\<in>P - Q. pindep2 X (insert x Q)" using ei notinQ by blast
qed

lemma rank2_eq:
  assumes XC: "X \<subseteq> carrier" and R: "R \<subseteq> X \<times> I"
  shows "indep_system.lower_rank_of (pindep2 X) R = card (fst ` R)"
proof -
  note mat2 = matroid_pindep2[OF XC]
  interpret IS2: indep_system "X \<times> I" "pindep2 X" by (rule indep_system_pindep2[OF XC])
  have finR: "finite R" using R finite_carr'[OF XC] finite_subset by blast
  obtain B where B: "IS2.basis_in R B" using IS2.basis_in_ex[OF R] by blast
  have Bind: "pindep2 X B" and BR: "B \<subseteq> R"
    using IS2.basis_in_indep_in[OF R B] IS2.indep_in_indep IS2.indep_in_subset_carrier by blast+
  have "IS2.lower_rank_of R = card B" using matroid.rank_of_eq_card_basis_in[OF mat2 R B] .
  also have "card B = card (fst ` B)" using Bind by (simp add: pindep2_def card_image)
  also have "card (fst ` B) \<le> card (fst ` R)"
    using BR finR by (auto intro!: card_mono image_mono)
  finally have le: "IS2.lower_rank_of R \<le> card (fst ` R)" .
  define T where "T = (\<lambda>e. (e, SOME i. (e, i) \<in> R)) ` (fst ` R)"
  have Tsub: "T \<subseteq> R"
  proof
    fix p assume "p \<in> T"
    then obtain e where e: "e \<in> fst ` R" "p = (e, SOME i. (e, i) \<in> R)" by (auto simp: T_def)
    from e(1) have "\<exists>i. (e, i) \<in> R" by auto
    hence "(e, SOME i. (e, i) \<in> R) \<in> R" by (rule someI_ex)
    thus "p \<in> R" using e(2) by simp
  qed
  have injT: "inj_on fst T" by (auto simp: T_def inj_on_def)
  have fstT: "fst ` T = fst ` R" by (force simp: T_def)
  have "pindep2 X T" using Tsub R injT by (auto simp: pindep2_def)
  hence "IS2.indep_in R T" using Tsub by (auto simp: IS2.indep_in_def)
  hence "card T \<le> IS2.lower_rank_of R" using matroid.rank_of_indep_in_le[OF mat2 R] by blast
  moreover have "card T = card (fst ` R)" using card_image[OF injT] fstT by simp
  ultimately have "card (fst ` R) \<le> IS2.lower_rank_of R" by simp
  with le show ?thesis by linarith
qed


subsubsection \<open>The direct-sum matroid\<close>

lemma indep_system_pindep1:
  assumes "X \<subseteq> carrier" shows "indep_system (X \<times> I) (pindep1 X)"
proof
  show "finite (X \<times> I)" by (rule finite_carr'[OF assms])
next
  fix Q assume "pindep1 X Q" thus "Q \<subseteq> X \<times> I" by (simp add: pindep1_def)
next
  show "\<exists>Q. pindep1 X Q"
    by (rule exI[of _ "{}"]) (auto simp: pindep1_def sect_def indep_empty_i)
next
  fix Q P assume "pindep1 X Q" "P \<subseteq> Q"
  thus "pindep1 X P"
    using indep_subset_i sect_mono by (fastforce simp: pindep1_def)
qed

lemma matroid_pindep1:
  assumes XC: "X \<subseteq> carrier" shows "matroid (X \<times> I) (pindep1 X)"
proof (rule matroid.intro[OF indep_system_pindep1[OF XC]], unfold matroid_axioms_def, intro allI impI)
  fix P Q assume P: "pindep1 X P" and Q: "pindep1 X Q" and c: "card P = Suc (card Q)"
  have finX: "finite X" using XC carrier_finite finite_subset by blast
  have subP: "P \<subseteq> X \<times> I" and subQ: "Q \<subseteq> X \<times> I" using P Q by (auto simp: pindep1_def)
  have cardP: "card P = (\<Sum>i\<in>I. card (sect P i))"
    and cardQ: "card Q = (\<Sum>i\<in>I. card (sect Q i))"
    using card_eq_sum_sect[OF subP finX] card_eq_sum_sect[OF subQ finX] by auto
  have "\<exists>i\<in>I. card (sect Q i) < card (sect P i)"
  proof (rule ccontr)
    assume "\<not> (\<exists>i\<in>I. card (sect Q i) < card (sect P i))"
    hence le: "\<forall>i\<in>I. card (sect P i) \<le> card (sect Q i)" by auto
    have "(\<Sum>i\<in>I. card (sect P i)) \<le> (\<Sum>i\<in>I. card (sect Q i))"
      using le by (intro sum_mono) blast
    thus False using cardP cardQ c by simp
  qed
  then obtain i where i: "i \<in> I" "card (sect Q i) < card (sect P i)" by blast
  interpret Mi: matroid carrier "indep i" using matroids[OF i(1)] .
  have "indep i (sect P i)" and "indep i (sect Q i)" using P Q i(1) by (auto simp: pindep1_def)
  from Mi.augment[OF this i(2)]
  obtain e where e: "e \<in> sect P i - sect Q i" "indep i (insert e (sect Q i))" by blast
  have eiP: "(e, i) \<in> P" using e(1) by (simp add: sect_def)
  have eiQ: "(e, i) \<notin> Q" using e(1) by (simp add: sect_def)
  have "pindep1 X (insert (e, i) Q)"
    unfolding pindep1_def
  proof (intro conjI ballI)
    show "insert (e, i) Q \<subseteq> X \<times> I" using eiP subP subQ by blast
  next
    fix j assume "j \<in> I"
    show "indep j (sect (insert (e, i) Q) j)"
    proof (cases "j = i")
      case True
      thus ?thesis using e(2) by (simp add: sect_insert)
    next
      case False
      thus ?thesis using Q \<open>j \<in> I\<close> by (simp add: sect_insert pindep1_def)
    qed
  qed
  thus "\<exists>x\<in>P - Q. pindep1 X (insert x Q)" using eiP eiQ by blast
qed

lemma sect_basis_exists:
  assumes "i \<in> I" "S \<subseteq> carrier"
  shows "\<exists>B. indep i B \<and> B \<subseteq> S \<and> card B = r i S"
proof -
  interpret Mi: matroid carrier "indep i" using matroids[OF assms(1)] .
  obtain B where B: "Mi.basis_in S B" using Mi.basis_in_ex[OF assms(2)] by blast
  have "indep i B" "B \<subseteq> S"
    using Mi.basis_in_indep_in[OF assms(2) B] Mi.indep_in_indep Mi.indep_in_subset_carrier by blast+
  moreover have "card B = r i S" using Mi.rank_of_eq_card_basis_in[OF assms(2) B] by simp
  ultimately show ?thesis by blast
qed

lemma rank1_eq:
  assumes XC: "X \<subseteq> carrier" and R: "R \<subseteq> X \<times> I"
  shows "indep_system.lower_rank_of (pindep1 X) R = (\<Sum>i\<in>I. r i (sect R i))"
proof -
  note mat1 = matroid_pindep1[OF XC]
  interpret IS1: indep_system "X \<times> I" "pindep1 X" by (rule indep_system_pindep1[OF XC])
  have finX: "finite X" using XC carrier_finite finite_subset by blast
  have sectRc: "\<And>i. i \<in> I \<Longrightarrow> sect R i \<subseteq> carrier" using sect_subset_X[OF R] XC by blast
  obtain B where B: "IS1.basis_in R B" using IS1.basis_in_ex[OF R] by blast
  have Bind: "pindep1 X B" and BR: "B \<subseteq> R"
    using IS1.basis_in_indep_in[OF R B] IS1.indep_in_indep IS1.indep_in_subset_carrier by blast+
  have BXI: "B \<subseteq> X \<times> I" using Bind by (simp add: pindep1_def)
  have "IS1.lower_rank_of R = card B" using matroid.rank_of_eq_card_basis_in[OF mat1 R B] .
  also have "card B = (\<Sum>i\<in>I. card (sect B i))" using card_eq_sum_sect[OF BXI finX] .
  also have "(\<Sum>i\<in>I. card (sect B i)) \<le> (\<Sum>i\<in>I. r i (sect R i))"
  proof (rule sum_mono)
    fix i assume "i \<in> I"
    have "indep i (sect B i)" using Bind \<open>i \<in> I\<close> by (simp add: pindep1_def)
    thus "card (sect B i) \<le> r i (sect R i)"
      using card_le_rank[OF \<open>i \<in> I\<close> _ sect_mono[OF BR] sectRc[OF \<open>i \<in> I\<close>]] by blast
  qed
  finally have le: "IS1.lower_rank_of R \<le> (\<Sum>i\<in>I. r i (sect R i))" .
  define bas where "bas = (\<lambda>i. SOME B. indep i B \<and> B \<subseteq> sect R i \<and> card B = r i (sect R i))"
  have bas: "indep i (bas i) \<and> bas i \<subseteq> sect R i \<and> card (bas i) = r i (sect R i)" if "i \<in> I" for i
    unfolding bas_def using sect_basis_exists[OF that sectRc[OF that]] by (rule someI_ex)
  define T where "T = (\<Union>i\<in>I. (\<lambda>e. (e, i)) ` bas i)"
  have sectT: "sect T i = bas i" if "i \<in> I" for i
    using bas[OF that] R that by (auto simp: T_def sect_def)
  have TXI: "T \<subseteq> X \<times> I"
    using bas R by (auto simp: T_def dest: sect_subset_X[OF R, THEN subsetD])
  have "pindep1 X T"
    using TXI bas sectT by (auto simp: pindep1_def)
  hence "IS1.indep_in R T" using bas by (auto simp: IS1.indep_in_def T_def sect_def)
  hence "card T \<le> IS1.lower_rank_of R" using matroid.rank_of_indep_in_le[OF mat1 R] by blast
  moreover have "card T = (\<Sum>i\<in>I. r i (sect R i))"
  proof -
    have "card T = (\<Sum>i\<in>I. card (sect T i))" using card_eq_sum_sect[OF TXI finX] .
    also have "\<dots> = (\<Sum>i\<in>I. r i (sect R i))" using sectT bas by (auto intro: sum.cong)
    finally show ?thesis .
  qed
  ultimately have "(\<Sum>i\<in>I. r i (sect R i)) \<le> IS1.lower_rank_of R" by simp
  with le show ?thesis by linarith
qed


subsubsection \<open>The reduction and the unconditional theorem\<close>

lemma common_imp_partitionable:
  assumes XC: "X \<subseteq> carrier" and Q1: "pindep1 X Q" and Q2: "pindep2 X Q"
  shows "\<exists>Y. partitionable Y \<and> Y \<subseteq> X \<and> card Y = card Q"
proof -
  have QXI: "Q \<subseteq> X \<times> I" using Q1 by (simp add: pindep1_def)
  have injQ: "inj_on fst Q" using Q2 by (simp add: pindep2_def)
  have "partition_by (sect Q) (fst ` Q)"
    unfolding partition_by_def
  proof (intro conjI ballI impI)
    show "fst ` Q = (\<Union>i\<in>I. sect Q i)" using QXI by (force simp: sect_def)
  next
    fix i j assume ij: "i \<in> I" "j \<in> I" "i \<noteq> j"
    show "sect Q i \<inter> sect Q j = {}"
    proof (rule ccontr)
      assume "sect Q i \<inter> sect Q j \<noteq> {}"
      then obtain e where eij: "(e, i) \<in> Q" "(e, j) \<in> Q" by (auto simp: sect_def)
      have "fst (e, i) = fst (e, j)" by simp
      from inj_onD[OF injQ this eij(1) eij(2)] have "(e, i) = (e, j)" .
      thus False using ij(3) by simp
    qed
  next
    fix i assume "i \<in> I" thus "indep i (sect Q i)" using Q1 by (simp add: pindep1_def)
  qed
  hence "partitionable (fst ` Q)" by (auto simp: partitionable_def)
  moreover have "fst ` Q \<subseteq> X" using QXI by force
  moreover have "card (fst ` Q) = card Q" using injQ by (simp add: card_image)
  ultimately show ?thesis by blast
qed

lemma fst_Diff_carr':
  assumes "R \<subseteq> X \<times> I"
  shows "fst ` (X \<times> I - R) = X - (\<Inter>i\<in>I. sect R i)"
proof
  show "fst ` (X \<times> I - R) \<subseteq> X - (\<Inter>i\<in>I. sect R i)"
  proof
    fix e assume "e \<in> fst ` (X \<times> I - R)"
    then obtain i where "(e, i) \<in> X \<times> I - R" by auto
    hence "e \<in> X" "i \<in> I" "e \<notin> sect R i" by (auto simp: sect_def)
    thus "e \<in> X - (\<Inter>i\<in>I. sect R i)" by auto
  qed
next
  show "X - (\<Inter>i\<in>I. sect R i) \<subseteq> fst ` (X \<times> I - R)"
  proof
    fix e assume e: "e \<in> X - (\<Inter>i\<in>I. sect R i)"
    then obtain i where "i \<in> I" "e \<notin> sect R i" by auto
    hence "(e, i) \<in> X \<times> I - R" using e by (auto simp: sect_def)
    thus "e \<in> fst ` (X \<times> I - R)" by (metis fst_conv rev_image_eqI)
  qed
qed

lemma rank2_compl:
  assumes XC: "X \<subseteq> carrier" and R: "R \<subseteq> X \<times> I"
  shows "indep_system.lower_rank_of (pindep2 X) (X \<times> I - R) = card (X - (\<Inter>i\<in>I. sect R i))"
proof -
  have "X \<times> I - R \<subseteq> X \<times> I" by auto
  hence "indep_system.lower_rank_of (pindep2 X) (X \<times> I - R) = card (fst ` (X \<times> I - R))"
    by (rule rank2_eq[OF XC])
  also have "fst ` (X \<times> I - R) = X - (\<Inter>i\<in>I. sect R i)" by (rule fst_Diff_carr'[OF R])
  finally show ?thesis .
qed

lemma partition_rank_attained:
  assumes XC: "X \<subseteq> carrier"
  shows "\<exists>Y. partitionable Y \<and> Y \<subseteq> X \<and> card Y = rank_formula X"
proof (cases "I = {}")
  case True
  have "rank_formula X \<le> card (X - X) + (\<Sum>i\<in>I. r i X)"
    using rank_formula_le[OF subset_refl XC] .
  hence "rank_formula X = 0" using True by simp
  thus ?thesis using partitionable_empty by (intro exI[of _ "{}"]) auto
next
  case False
  note dm = double_matroid.intro[OF matroid_pindep1[OF XC] matroid_pindep2[OF XC]]
  have finXI: "finite (X \<times> I)" by (rule finite_carr'[OF XC])
  let ?rk1 = "indep_system.lower_rank_of (pindep1 X)"
  let ?rk2 = "indep_system.lower_rank_of (pindep2 X)"
  let ?MinS = "{?rk1 R + ?rk2 (X \<times> I - R) |R. R \<subseteq> X \<times> I}"
  let ?MaxS = "{card Q |Q. pindep1 X Q \<and> pindep2 X Q}"
  \<comment> \<open>the min side equals the rank formula\<close>
  have Min_eq: "Min ?MinS = rank_formula X"
  proof (rule Min_eqI)
    have "?MinS = (\<lambda>R. ?rk1 R + ?rk2 (X \<times> I - R)) ` Pow (X \<times> I)" by auto
    thus "finite ?MinS" using finXI by simp
  next
    fix v assume "v \<in> ?MinS"
    then obtain R where R: "R \<subseteq> X \<times> I" "v = ?rk1 R + ?rk2 (X \<times> I - R)" by auto
    define A where "A = X \<inter> (\<Inter>i\<in>I. sect R i)"
    have AX: "A \<subseteq> X" by (simp add: A_def)
    have v_eq: "v = (\<Sum>i\<in>I. r i (sect R i)) + card (X - (\<Inter>i\<in>I. sect R i))"
      using R rank1_eq[OF XC R(1)] rank2_compl[OF XC R(1)] by simp
    have cardXA: "card (X - (\<Inter>i\<in>I. sect R i)) = card (X - A)"
      by (rule arg_cong[where f = card]) (auto simp: A_def)
    have "(\<Sum>i\<in>I. r i A) \<le> (\<Sum>i\<in>I. r i (sect R i))"
    proof (rule sum_mono)
      fix i assume "i \<in> I"
      have "A \<subseteq> sect R i" using \<open>i \<in> I\<close> by (auto simp: A_def)
      moreover have "sect R i \<subseteq> carrier" using sect_subset_X[OF R(1)] XC by blast
      ultimately show "r i A \<le> r i (sect R i)" using r_mono[OF \<open>i \<in> I\<close>] by blast
    qed
    hence "rank_formula X \<le> card (X - A) + (\<Sum>i\<in>I. r i (sect R i))"
      using rank_formula_le[OF AX XC] by linarith
    thus "rank_formula X \<le> v" using v_eq cardXA by simp
  next
    obtain As where As: "As \<subseteq> X" "rank_formula X = card (X - As) + (\<Sum>i\<in>I. r i As)"
      using rank_formula_attained[OF XC] by blast
    have RAsub: "As \<times> I \<subseteq> X \<times> I" using As(1) by auto
    have sectAs: "\<And>i. i \<in> I \<Longrightarrow> sect (As \<times> I) i = As" by (auto simp: sect_def)
    have InterAs: "(\<Inter>i\<in>I. sect (As \<times> I) i) = As"
    proof -
      from False obtain i0 where "i0 \<in> I" by auto
      show ?thesis using sectAs \<open>i0 \<in> I\<close> by auto
    qed
    have "?rk1 (As \<times> I) = (\<Sum>i\<in>I. r i As)"
      using rank1_eq[OF XC RAsub] sectAs by (simp cong: sum.cong)
    moreover have "?rk2 (X \<times> I - As \<times> I) = card (X - As)"
      using rank2_compl[OF XC RAsub] InterAs by simp
    ultimately have "rank_formula X = ?rk1 (As \<times> I) + ?rk2 (X \<times> I - As \<times> I)"
      using As(2) by simp
    thus "rank_formula X \<in> ?MinS" using RAsub by blast
  qed
  \<comment> \<open>the max side is attained by an actual common independent set\<close>
  have finMaxS: "finite ?MaxS"
  proof -
    have "?MaxS \<subseteq> card ` Pow (X \<times> I)" by (auto simp: pindep1_def)
    moreover have "finite (card ` Pow (X \<times> I))" using finXI by simp
    ultimately show ?thesis by (rule finite_subset)
  qed
  have "pindep1 X {} \<and> pindep2 X {}"
    by (auto simp: pindep1_def pindep2_def sect_def indep_empty_i)
  hence neMaxS: "?MaxS \<noteq> {}" by blast
  have "Max ?MaxS \<in> ?MaxS" using finMaxS neMaxS by (rule Max_in)
  then obtain Q where Q: "pindep1 X Q" "pindep2 X Q" "card Q = Max ?MaxS" by auto
  have "Max ?MaxS = Min ?MinS" by (rule double_matroid.two_matroid_max_min_eq[OF dm])
  hence "card Q = rank_formula X" using Q(3) Min_eq by simp
  thus ?thesis using common_imp_partitionable[OF XC Q(1,2)] by metis
qed

text \<open>Theorem 13.34, unconditionally: the union of the matroids is a matroid whose rank
  function is the Nash-Williams formula.\<close>

theorem nash_williams_unconditional:
  shows "matroid carrier partitionable"
    and "X \<subseteq> carrier \<Longrightarrow> indep_system.lower_rank_of partitionable X = rank_formula X"
  using nash_williams[OF partition_rank_attained] by blast+


subsection \<open>Reduction: an optimum partition from a matroid intersection\<close>

text \<open>
  The construction inside the Nash-Williams proof also \<^emph>\<open>solves\<close> the Matroid Partitioning Problem.
  On the ground set \<^term>\<open>carrier \<times> I\<close> the two auxiliary matroids \<^term>\<open>pindep1 carrier\<close> (direct sum)
  and \<^term>\<open>pindep2 carrier\<close> (partition matroid) form a \<^locale>\<open>double_matroid\<close>, and common
  independent sets of the two correspond -- cardinality-preservingly -- to partitionable subsets of
  \<^term>\<open>carrier\<close> via the first projection \<open>fst\<close>.  Hence projecting a \<^emph>\<open>maximum\<close> common independent
  set (an optimum of the matroid intersection problem, \<^const>\<open>double_matroid.is_max\<close>) yields an
  optimum solution of the partitioning problem.  A matroid-intersection algorithm applied to the two
  auxiliary matroids therefore solves matroid partitioning.
\<close>

text \<open>Forward map: a common independent set projects, under \<open>fst\<close>, to a partition of the same size.\<close>

lemma common_partition_by:
  assumes Q1: "pindep1 X Q" and Q2: "pindep2 X Q"
  shows "partition_by (sect Q) (fst ` Q)"
proof -
  have QXI: "Q \<subseteq> X \<times> I" using Q1 by (simp add: pindep1_def)
  have injQ: "inj_on fst Q" using Q2 by (simp add: pindep2_def)
  show ?thesis
    unfolding partition_by_def
  proof (intro conjI ballI impI)
    show "fst ` Q = (\<Union>i\<in>I. sect Q i)" using QXI by (force simp: sect_def)
  next
    fix i j assume ij: "i \<in> I" "j \<in> I" "i \<noteq> j"
    show "sect Q i \<inter> sect Q j = {}"
    proof (rule ccontr)
      assume "sect Q i \<inter> sect Q j \<noteq> {}"
      then obtain e where eij: "(e, i) \<in> Q" "(e, j) \<in> Q" by (auto simp: sect_def)
      have "fst (e, i) = fst (e, j)" by simp
      from inj_onD[OF injQ this eij(1) eij(2)] ij(3) show False by simp
    qed
  next
    fix i assume "i \<in> I" thus "indep i (sect Q i)" using Q1 by (simp add: pindep1_def)
  qed
qed

lemma common_imp_partitionable_fst:
  assumes "pindep1 X Q" and "pindep2 X Q"
  shows "partitionable (fst ` Q)" (is ?p) and "card (fst ` Q) = card Q" (is ?c)
proof -
  show ?p using common_partition_by[OF assms] by (auto simp: partitionable_def)
  show ?c using assms(2) by (simp add: pindep2_def card_image)
qed

text \<open>Backward map: a partitionable set lifts to a common independent set of the same size,
by tagging each element with the (unique) part it lies in.\<close>

lemma partitionable_imp_common:
  assumes "partitionable Y"
  shows "\<exists>Q. pindep1 carrier Q \<and> pindep2 carrier Q \<and> fst ` Q = Y \<and> card Q = card Y"
proof -
  from assms obtain f where f: "partition_by f Y" by (auto simp: partitionable_def)
  have Yeq: "Y = (\<Union>i\<in>I. f i)"
    and disj: "\<forall>i\<in>I. \<forall>j\<in>I. i \<noteq> j \<longrightarrow> f i \<inter> f j = {}"
    and indf: "\<forall>i\<in>I. indep i (f i)"
    using f by (auto simp: partition_by_def)
  define Q where "Q = {(e, i) | e i. i \<in> I \<and> e \<in> f i}"
  have sectQ: "\<And>i. i \<in> I \<Longrightarrow> sect Q i = f i" by (auto simp: sect_def Q_def)
  have fi_carr: "\<And>i. i \<in> I \<Longrightarrow> f i \<subseteq> carrier" using indf indep_subset_carrier by blast
  have QXI: "Q \<subseteq> carrier \<times> I" using fi_carr by (fastforce simp: Q_def)
  have p1: "pindep1 carrier Q"
    unfolding pindep1_def
  proof (intro conjI ballI)
    show "Q \<subseteq> carrier \<times> I" by (rule QXI)
  next
    fix i assume iI: "i \<in> I"
    have "sect Q i = f i" using sectQ[OF iI] .
    thus "indep i (sect Q i)" using indf iI by simp
  qed
  have injQ: "inj_on fst Q"
  proof (rule inj_onI)
    fix p q assume p: "p \<in> Q" and q: "q \<in> Q" and eq: "fst p = fst q"
    obtain e i where pi: "p = (e, i)" "i \<in> I" "e \<in> f i" using p by (auto simp: Q_def)
    obtain e' j where qj: "q = (e', j)" "j \<in> I" "e' \<in> f j" using q by (auto simp: Q_def)
    have ee: "e = e'" using eq pi(1) qj(1) by simp
    have "i = j"
    proof (rule ccontr)
      assume "i \<noteq> j"
      hence "f i \<inter> f j = {}" using disj pi(2) qj(2) by blast
      thus False using pi(3) qj(3) ee by auto
    qed
    thus "p = q" using pi(1) qj(1) ee by simp
  qed
  have p2: "pindep2 carrier Q" unfolding pindep2_def using QXI injQ by simp
  have fstQ: "fst ` Q = Y"
  proof
    show "fst ` Q \<subseteq> Y" using Yeq by (auto simp: Q_def)
  next
    show "Y \<subseteq> fst ` Q"
    proof
      fix x assume "x \<in> Y"
      then obtain i where "i \<in> I" "x \<in> f i" using Yeq by auto
      hence "(x, i) \<in> Q" by (auto simp: Q_def)
      thus "x \<in> fst ` Q" by (metis fst_conv rev_image_eqI)
    qed
  qed
  have "card Q = card (fst ` Q)" using injQ by (simp add: card_image)
  hence cardQ: "card Q = card Y" using fstQ by simp
  show ?thesis using p1 p2 fstQ cardQ by blast
qed

text \<open>Main reduction: the \<open>fst\<close>-image of a \<^emph>\<open>maximum\<close> common independent set of the two auxiliary
matroids is an optimum solution of the matroid partitioning problem.\<close>

theorem partition_opt_from_intersection:
  assumes Q1: "pindep1 carrier Q" and Q2: "pindep2 carrier Q"
    and maxQ: "\<And>Q'. pindep1 carrier Q' \<Longrightarrow> pindep2 carrier Q' \<Longrightarrow> card Q' \<le> card Q"
  shows "partition_opt (fst ` Q)"
  unfolding partition_opt_def
proof (intro conjI allI impI)
  show "partitionable (fst ` Q)" using common_imp_partitionable_fst(1)[OF Q1 Q2] .
next
  fix Y assume "partitionable Y"
  then obtain Q' where Q': "pindep1 carrier Q'" "pindep2 carrier Q'" "card Q' = card Y"
    using partitionable_imp_common by blast
  have "card Y = card Q'" using Q'(3) by simp
  also have "\<dots> \<le> card Q" using maxQ[OF Q'(1,2)] .
  also have "\<dots> = card (fst ` Q)" using common_imp_partitionable_fst(2)[OF Q1 Q2] by simp
  finally show "card Y \<le> card (fst ` Q)" .
qed

text \<open>Phrased with the matroid-intersection optimum predicate \<^const>\<open>double_matroid.is_max\<close>: exactly
what a maximum-cardinality matroid-intersection algorithm returns for the two auxiliary matroids.\<close>

corollary partition_opt_from_is_max:
  assumes "double_matroid.is_max (pindep1 carrier) (pindep2 carrier) Q"
  shows "partition_opt (fst ` Q)"
proof -
  interpret dm: double_matroid "carrier \<times> I" "pindep1 carrier" "pindep2 carrier"
    by (rule double_matroid.intro[OF matroid_pindep1[OF subset_refl] matroid_pindep2[OF subset_refl]])
  note m = assms[unfolded dm.is_max_def]
  show ?thesis
  proof (rule partition_opt_from_intersection)
    show "pindep1 carrier Q" using m by simp
    show "pindep2 carrier Q" using m by simp
  next
    fix Q' assume "pindep1 carrier Q'" "pindep2 carrier Q'"
    thus "card Q' \<le> card Q" using m by (auto simp: not_less)
  qed
qed

text \<open>Sanity: an optimum partition exists, and its cardinality is the rank of the union
(the Nash-Williams value).\<close>

corollary partition_opt_card:
  assumes "partition_opt X" shows "card X = rank_formula carrier"
proof -
  have pX: "partitionable X" using assms by (simp add: partition_opt_def)
  have le: "card X \<le> rank_formula carrier"
    using partitionable_card_le_rank_formula[OF pX partitionable_subset_carrier[OF pX] subset_refl] .
  obtain Y where Y: "partitionable Y" "card Y = rank_formula carrier"
    using partition_rank_attained[OF subset_refl] by blast
  have "rank_formula carrier = card Y" using Y(2) by simp
  also have "\<dots> \<le> card X" using assms Y(1) by (auto simp: partition_opt_def)
  finally show ?thesis using le by simp
qed

corollary partition_opt_exists: "\<exists>X. partition_opt X"
proof -
  obtain Y where Y: "partitionable Y" "card Y = rank_formula carrier"
    using partition_rank_attained[OF subset_refl] by blast
  have "partition_opt Y"
    unfolding partition_opt_def
  proof (intro conjI allI impI)
    show "partitionable Y" by (rule Y(1))
  next
    fix Z assume Z: "partitionable Z"
    have "card Z \<le> rank_formula carrier"
      using partitionable_card_le_rank_formula[OF Z partitionable_subset_carrier[OF Z] subset_refl] .
    thus "card Z \<le> card Y" using Y(2) by simp
  qed
  thus ?thesis by blast
qed

end

end
