theory Indexed_Heap
  imports Main Data_Structures.Fixed_Univ_Key_Value_Queue_Specs
begin

section \<open>An Indexed Binary Min-Heap: Functional Model\<close>

text \<open>A binary min-heap over elements that are natural numbers (indices into a fixed universe,
      e.g.\ vertex numbers), together with a key function. The heap is a list @{term hs} in which
      position @{term j} has parent @{term \<open>parent j\<close>} and the children \<open>2j+1\<close> and \<open>2j+2\<close>.

      This is the functional model of the imperative heap of
      \<open>Indexed_Heap_Imperative\<close>: there, the list is stored in an array of size \<open>n\<close> (with the
      current size in a reference), the keys in a key array indexed by elements, and the position
      of every element in a position array, which makes @{text decrease_key} logarithmic.
      The operations are the usual ones: insertion and key decrease sift the element up,
      extraction moves the last element to the root and sifts it down. The keys in the model
      are those of the functional algorithm; ties are broken exactly as by the imperative code,
      so that the model determines the result of every operation.\<close>

subsection \<open>Tree structure\<close>

definition parent :: "nat \<Rightarrow> nat" where
  "parent i = (i - 1) div 2"

lemma parent_less [simp]: "0 < i \<Longrightarrow> parent i < i"
  unfolding parent_def by linarith

lemma parent_childI [simp]: "parent (2 * i + 1) = i" "parent (2 * i + 2) = i"
  unfolding parent_def by simp_all

lemma parent_eq_iff: "0 < j \<Longrightarrow> parent j = i \<longleftrightarrow> j = 2 * i + 1 \<or> j = 2 * i + 2"
  unfolding parent_def by linarith

lemma parent_eqD: "\<lbrakk>parent j = i; 0 < j\<rbrakk> \<Longrightarrow> 2 * i + 1 \<le> j"
  using parent_eq_iff
  by auto

subsection \<open>Sifting\<close>

text \<open>Swap an element with its parent while its key is smaller.\<close>

function sift_up :: "(nat \<Rightarrow> 'a::linorder) \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "sift_up ks hs i =
     (if i = 0 then hs
      else if ks (hs ! i) < ks (hs ! parent i)
           then sift_up ks (hs[i := hs ! parent i, parent i := hs ! i]) (parent i)
           else hs)"
  by pat_completeness auto
termination by (relation "measure (\<lambda>(_, _, i). i)") simp_all

declare sift_up.simps [simp del]

lemma sift_up_0 [simp]: "sift_up ks hs 0 = hs"
  by (subst sift_up.simps) simp

lemma sift_up_rec:
  "\<lbrakk>0 < i; ks (hs ! i) < ks (hs ! parent i)\<rbrakk> \<Longrightarrow>
   sift_up ks hs i = sift_up ks (hs[i := hs ! parent i, parent i := hs ! i]) (parent i)"
  by (subst sift_up.simps) simp

lemma sift_up_stop: "\<not> ks (hs ! i) < ks (hs ! parent i) \<Longrightarrow> sift_up ks hs i = hs"
  by (subst sift_up.simps) simp

text \<open>The child with the smaller key; the right one only if it exists and is strictly smaller.\<close>

definition min_child :: "(nat \<Rightarrow> 'a::linorder) \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "min_child ks hs i =
     (if Suc (2 * i + 1) < length hs \<and> ks (hs ! Suc (2 * i + 1)) < ks (hs ! (2 * i + 1))
      then Suc (2 * i + 1) else 2 * i + 1)"

lemma min_child_bounds:
  "2 * i + 1 < length hs \<Longrightarrow> i < min_child ks hs i \<and> min_child ks hs i < length hs"
  unfolding min_child_def by auto

lemma parent_min_child [simp]: "parent (min_child ks hs i) = i"
  unfolding min_child_def by (simp add: parent_def)

lemma min_child_min:
  "\<lbrakk>2 * i + 1 < length hs; j < length hs; 0 < j; parent j = i\<rbrakk>
   \<Longrightarrow> ks (hs ! min_child ks hs i) \<le> ks (hs ! j)"
  unfolding min_child_def by (auto simp: parent_eq_iff)

text \<open>Swap an element with its smaller child while that child's key is smaller.\<close>

function sift_down :: "(nat \<Rightarrow> 'a::linorder) \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "sift_down ks hs i =
     (if 2 * i + 1 < length hs \<and> ks (hs ! min_child ks hs i) < ks (hs ! i)
      then sift_down ks (hs[i := hs ! min_child ks hs i, min_child ks hs i := hs ! i])
                        (min_child ks hs i)
      else hs)"
  by pat_completeness auto
termination
proof (relation "measure (\<lambda>(_, hs, i). length hs - i)", goal_cases)
  case (2 ks hs i) thus ?case using min_child_bounds[of i hs ks] by (simp; linarith)
qed simp

declare sift_down.simps [simp del]

lemma sift_down_stop:
  "\<not> (2 * i + 1 < length hs \<and> ks (hs ! min_child ks hs i) < ks (hs ! i)) \<Longrightarrow> sift_down ks hs i = hs"
  by (subst sift_down.simps) auto

lemma sift_up_perm:
  "i < length hs \<Longrightarrow>
   length (sift_up ks hs i) = length hs \<and> set (sift_up ks hs i) = set hs \<and>
   (distinct (sift_up ks hs i) \<longleftrightarrow> distinct hs)"
proof (induction ks hs i rule: sift_up.induct)
  case (1 ks hs i)
  show ?case
    using 1 less_trans[OF parent_less 1(2)] by (simp add: sift_up.simps[of ks hs i])
qed

lemma sift_down_perm:
  "i < length hs \<Longrightarrow>
   length (sift_down ks hs i) = length hs \<and> set (sift_down ks hs i) = set hs \<and>
   (distinct (sift_down ks hs i) \<longleftrightarrow> distinct hs)"
proof (induction ks hs i rule: sift_down.induct)
  case (1 ks hs i)
  show ?case
    using 1 min_child_bounds[of i hs ks] by (simp add: sift_down.simps[of ks hs i])
qed

subsection \<open>The heap property\<close>

definition heap_prop :: "(nat \<Rightarrow> 'a::linorder) \<Rightarrow> nat list \<Rightarrow> bool" where
  "heap_prop ks hs \<longleftrightarrow> (\<forall>j<length hs. 0 < j \<longrightarrow> ks (hs ! parent j) \<le> ks (hs ! j))"

text \<open>During sift-up at @{term i}: the heap property holds except between @{term i} and its
      parent, and the parent of @{term i} bounds the children of @{term i}.\<close>

definition up_inv :: "(nat \<Rightarrow> 'a::linorder) \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "up_inv ks hs i \<longleftrightarrow>
     (\<forall>j<length hs. 0 < j \<longrightarrow> j \<noteq> i \<longrightarrow> ks (hs ! parent j) \<le> ks (hs ! j)) \<and>
     (\<forall>j<length hs. 0 < j \<longrightarrow> parent j = i \<longrightarrow> 0 < i \<longrightarrow> ks (hs ! parent i) \<le> ks (hs ! j))"

text \<open>During sift-down at @{term i}: the heap property holds except between @{term i} and its
      children, and the parent of @{term i} bounds the children of @{term i}.\<close>

definition down_inv :: "(nat \<Rightarrow> 'a::linorder) \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "down_inv ks hs i \<longleftrightarrow>
     (\<forall>j<length hs. 0 < j \<longrightarrow> parent j \<noteq> i \<longrightarrow> ks (hs ! parent j) \<le> ks (hs ! j)) \<and>
     (\<forall>j<length hs. 0 < j \<longrightarrow> parent j = i \<longrightarrow> 0 < i \<longrightarrow> ks (hs ! parent i) \<le> ks (hs ! j))"

lemma heap_prop_min:
  assumes "heap_prop ks hs" "j < length hs"
  shows "ks (hs ! 0) \<le> ks (hs ! j)"
  using assms(2)
proof (induction j rule: less_induct)
  case (less j)
  show ?case
  proof (cases "j = 0")
    case False
    hence "ks (hs ! 0) \<le> ks (hs ! parent j)" using less by simp
    also have "\<dots> \<le> ks (hs ! j)" using assms(1) less(2) False by (simp add: heap_prop_def)
    finally show ?thesis .
  qed simp
qed

lemma up_inv_step:
  assumes inv: "up_inv ks hs i" and i: "0 < i" "i < length hs"
      and lt: "ks (hs ! i) < ks (hs ! parent i)"
  shows "up_inv ks (hs[i := hs ! parent i, parent i := hs ! i]) (parent i)"
proof -
  let ?p = "parent i"
  let ?hs = "hs[i := hs ! ?p, ?p := hs ! i]"
  have p: "?p < i" "?p < length hs" "i \<noteq> ?p" using parent_less[OF i(1)] i(2) by auto
  have I1: "\<And>j. \<lbrakk>j < length hs; 0 < j; j \<noteq> i\<rbrakk> \<Longrightarrow> ks (hs ! parent j) \<le> ks (hs ! j)"
   and I2: "\<And>j. \<lbrakk>j < length hs; 0 < j; parent j = i\<rbrakk> \<Longrightarrow> ks (hs ! ?p) \<le> ks (hs ! j)"
    using inv i unfolding up_inv_def by auto
  have np: "?hs ! ?p = hs ! i" and ni: "?hs ! i = hs ! ?p" using p i by auto
  have no: "\<And>j. \<lbrakk>j \<noteq> ?p; j \<noteq> i\<rbrakk> \<Longrightarrow> ?hs ! j = hs ! j" by simp
  show ?thesis
    unfolding up_inv_def length_list_update
  proof (intro conjI allI impI)
    fix j assume j: "j < length hs" "0 < j" "j \<noteq> ?p"
    have pj: "parent j < j" using j by simp
    consider "j = i" | "j \<noteq> i" "parent j = ?p" | "j \<noteq> i" "parent j = i"
      | "j \<noteq> i" "parent j \<noteq> ?p" "parent j \<noteq> i" by blast
    thus "ks (?hs ! parent j) \<le> ks (?hs ! j)"
    proof cases
      case 1 thus ?thesis using lt np ni by simp
    next
      case 2
      hence "ks (hs ! i) \<le> ks (hs ! j)" using lt I1[of j] j by simp
      thus ?thesis using 2 j np no[of j] by simp
    next
      case 3 thus ?thesis using I2[of j] j ni no[of j] by simp
    next
      case 4 thus ?thesis using I1[of j] j no[of j] no[of "parent j"] by simp
    qed
  next
    fix j assume j: "j < length hs" "0 < j" "parent j = ?p" "0 < ?p"
    have gp: "parent ?p < ?p" using j by simp
    have jp: "j \<noteq> ?p" using j by (metis parent_less less_irrefl)
    have "ks (hs ! parent ?p) \<le> ks (hs ! ?p)" using I1[of ?p] j p by simp
    moreover have "j \<noteq> i \<Longrightarrow> ks (hs ! ?p) \<le> ks (hs ! j)" using I1[of j] j by simp
    moreover have "?hs ! parent ?p = hs ! parent ?p" using no[of "parent ?p"] gp p by simp
    ultimately show "ks (?hs ! parent ?p) \<le> ks (?hs ! j)"
      using ni no[of j] jp by (cases "j = i") (auto intro: order_trans)
  qed
qed

lemma sift_up_heap:
  "\<lbrakk>i < length hs; up_inv ks hs i\<rbrakk> \<Longrightarrow> heap_prop ks (sift_up ks hs i)"
proof (induction ks hs i rule: sift_up.induct)
  case (1 ks hs i)
  show ?case
  proof (cases "i = 0")
    case i0: True
    thus ?thesis using 1(3) by (simp add: up_inv_def heap_prop_def)
  next
    case i0: False
    show ?thesis
    proof (cases "ks (hs ! i) < ks (hs ! parent i)")
      case lt: True
      have "parent i < length hs" using 1(2) i0 by (meson less_trans parent_less neq0_conv)
      thus ?thesis
        using 1(1)[OF i0 lt] up_inv_step[OF 1(3)] i0 lt 1(2) sift_up_rec[of i ks hs] by simp
    next
      case ge: False
      show ?thesis
        unfolding sift_up_stop[OF ge] heap_prop_def
      proof (intro allI impI)
        fix j assume "j < length hs" "0 < j"
        thus "ks (hs ! parent j) \<le> ks (hs ! j)"
          using 1(3) ge by (cases "j = i") (auto simp: up_inv_def not_less)
      qed
    qed
  qed
qed

lemma down_inv_step:
  assumes inv: "down_inv ks hs i" and l: "2 * i + 1 < length hs"
      and lt: "ks (hs ! min_child ks hs i) < ks (hs ! i)"
  shows "down_inv ks (hs[i := hs ! min_child ks hs i, min_child ks hs i := hs ! i])
                     (min_child ks hs i)"
proof -
  let ?c = "min_child ks hs i"
  let ?hs = "hs[i := hs ! ?c, ?c := hs ! i]"
  have c: "i < ?c" "?c < length hs" using min_child_bounds[OF l] by auto
  have I1: "\<And>j. \<lbrakk>j < length hs; 0 < j; parent j \<noteq> i\<rbrakk> \<Longrightarrow> ks (hs ! parent j) \<le> ks (hs ! j)"
   and I2: "\<And>j. \<lbrakk>j < length hs; 0 < j; parent j = i; 0 < i\<rbrakk> \<Longrightarrow> ks (hs ! parent i) \<le> ks (hs ! j)"
    using inv unfolding down_inv_def by auto
  have M: "\<And>j. \<lbrakk>j < length hs; 0 < j; parent j = i\<rbrakk> \<Longrightarrow> ks (hs ! ?c) \<le> ks (hs ! j)"
    using min_child_min[OF l] by blast
  have nc: "?hs ! ?c = hs ! i" and ni: "?hs ! i = hs ! ?c" using c by auto
  have no: "\<And>j. \<lbrakk>j \<noteq> ?c; j \<noteq> i\<rbrakk> \<Longrightarrow> ?hs ! j = hs ! j" by simp
  show ?thesis
    unfolding down_inv_def length_list_update
  proof (intro conjI allI impI)
    fix j assume j: "j < length hs" "0 < j" "parent j \<noteq> ?c"
    have pj: "parent j < j" using j by simp
    consider "j = ?c" | "j = i" | "j \<noteq> ?c" "j \<noteq> i" "parent j = i"
      | "j \<noteq> ?c" "j \<noteq> i" "parent j \<noteq> i" by blast
    thus "ks (?hs ! parent j) \<le> ks (?hs ! j)"
    proof cases
      case 1 thus ?thesis using lt nc ni by simp
    next
      case 2
      have "parent i < i" using 2 j by simp
      hence "parent i \<noteq> ?c" "parent i \<noteq> i" using c by auto
      thus ?thesis using 2 j c I2[of ?c] ni no[of "parent i"] by simp
    next
      case 3 thus ?thesis using j M[of j] ni no[of j] by simp
    next
      case 4 thus ?thesis using j I1[of j] no[of j] no[of "parent j"] by simp
    qed
  next
    fix j assume j: "j < length hs" "0 < j" "parent j = ?c" "0 < ?c"
    have "?c < j" using j by (metis parent_less)
    hence "j \<noteq> ?c" "j \<noteq> i" using c by auto
    thus "ks (?hs ! parent ?c) \<le> ks (?hs ! j)"
      using j c I1[of j] ni no[of j] by simp
  qed
qed

lemma sift_down_heap:
  "\<lbrakk>i < length hs; down_inv ks hs i\<rbrakk> \<Longrightarrow> heap_prop ks (sift_down ks hs i)"
proof (induction ks hs i rule: sift_down.induct)
  case (1 ks hs i)
  show ?case
  proof (cases "2 * i + 1 < length hs \<and> ks (hs ! min_child ks hs i) < ks (hs ! i)")
    case True
    thus ?thesis
      using 1(1)[OF True] down_inv_step[OF 1(3)] min_child_bounds[of i hs ks]
      by (simp add: sift_down.simps[of ks hs i])
  next
    case False
    have "heap_prop ks hs"
      unfolding heap_prop_def
    proof (intro allI impI)
      fix j assume j: "j < length hs" "0 < j"
      show "ks (hs ! parent j) \<le> ks (hs ! j)"
      proof (cases "parent j = i")
        case True
        hence l: "2 * i + 1 < length hs" using parent_eqD[OF True j(2)] j(1) by linarith
        hence "ks (hs ! i) \<le> ks (hs ! min_child ks hs i)" using False by simp
        also have "\<dots> \<le> ks (hs ! j)" using min_child_min[OF l j True] .
        finally show ?thesis using True by simp
      qed (use 1(3) j in \<open>simp add: down_inv_def\<close>)
    qed
    thus ?thesis using sift_down_stop[OF False] by simp
  qed
qed

subsection \<open>Position lookup\<close>

text \<open>The position of an element in the heap list. The imperative heap reads it from its position
      array instead.\<close>

fun idx :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "idx [] x = 0"
| "idx (y # ys) x = (if y = x then 0 else Suc (idx ys x))"

lemma idx_less: "x \<in> set hs \<Longrightarrow> idx hs x < length hs"
  by (induction hs) auto

lemma idx_nth [simp]: "x \<in> set hs \<Longrightarrow> hs ! idx hs x = x"
  by (induction hs) auto

lemma idx_unique: "\<lbrakk>distinct hs; j < length hs\<rbrakk> \<Longrightarrow> idx hs (hs ! j) = j"
  by (metis idx_less idx_nth nth_eq_iff_index_eq nth_mem)

subsection \<open>Operations\<close>

type_synonym 'a iheap = "nat list \<times> (nat \<Rightarrow> 'a)"

definition heap_empty :: "'a iheap" where
  "heap_empty = ([], \<lambda>_. undefined)"

fun heap_insert :: "'a::linorder iheap \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a iheap" where
  "heap_insert (hs, ks) x k = (sift_up (ks(x := k)) (hs @ [x]) (length hs), ks(x := k))"

fun heap_decrease_key :: "'a::linorder iheap \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a iheap" where
  "heap_decrease_key (hs, ks) x k = (sift_up (ks(x := k)) hs (idx hs x), ks(x := k))"

fun heap_extract_min :: "'a::linorder iheap \<Rightarrow> 'a iheap \<times> nat option" where
  "heap_extract_min (hs, ks) =
     (if hs = [] then ((hs, ks), None)
      else if butlast hs = [] then (([], ks), Some (hs ! 0))
      else ((sift_down ks ((butlast hs)[0 := last hs]) 0, ks), Some (hs ! 0)))"

fun heap_invar :: "nat set \<Rightarrow> 'a::linorder iheap \<Rightarrow> bool" where
  "heap_invar U (hs, ks) \<longleftrightarrow> distinct hs \<and> set hs \<subseteq> U \<and> heap_prop ks hs"

fun heap_abstract :: "'a iheap \<Rightarrow> (nat \<times> 'a) set" where
  "heap_abstract (hs, ks) = (\<lambda>v. (v, ks v)) ` set hs"

subsection \<open>Correctness\<close>

lemma up_inv_insert:
  assumes "heap_prop ks hs" "x \<notin> set hs"
  shows "up_inv (ks(x := k)) (hs @ [x]) (length hs)"
  unfolding up_inv_def
proof (intro conjI allI impI)
  fix j assume j: "j < length (hs @ [x])" "0 < j" "j \<noteq> length hs"
  hence "j < length hs" "parent j < length hs" by (auto intro: less_trans[OF parent_less])
  thus "(ks(x := k)) ((hs @ [x]) ! parent j) \<le> (ks(x := k)) ((hs @ [x]) ! j)"
    using assms j by (auto simp: nth_append heap_prop_def dest: nth_mem)
next
  fix j assume j: "j < length (hs @ [x])" "0 < j" "parent j = length hs"
  thus "(ks(x := k)) ((hs @ [x]) ! parent (length hs)) \<le> (ks(x := k)) ((hs @ [x]) ! j)"
    using parent_less[of j] by simp
qed

lemma up_inv_decrease:
  assumes H: "heap_prop ks hs" "distinct hs" "x \<in> set hs" and k: "k < ks x"
  shows "up_inv (ks(x := k)) hs (idx hs x)"
proof -
  let ?i = "idx hs x"
  have i: "?i < length hs" "hs ! ?i = x" using H idx_less by auto
  have ne: "\<And>j. \<lbrakk>j < length hs; j \<noteq> ?i\<rbrakk> \<Longrightarrow> hs ! j \<noteq> x"
    using H(2) i by (metis nth_eq_iff_index_eq)
  have P: "\<And>j. \<lbrakk>j < length hs; 0 < j\<rbrakk> \<Longrightarrow> ks (hs ! parent j) \<le> ks (hs ! j)"
    using H(1) by (simp add: heap_prop_def)
  show ?thesis
    unfolding up_inv_def
  proof (intro conjI allI impI)
    fix j assume j: "j < length hs" "0 < j" "j \<noteq> ?i"
    have pj: "parent j < length hs" using j by (meson less_trans parent_less)
    show "(ks(x := k)) (hs ! parent j) \<le> (ks(x := k)) (hs ! j)"
      using P[OF j(1,2)] ne[OF j(1,3)] k
      by (cases "parent j = ?i") (auto simp: i ne[OF pj])
  next
    fix j assume j: "j < length hs" "0 < j" "parent j = ?i" "0 < ?i"
    have "ks (hs ! parent ?i) \<le> ks x" using P[of ?i] i j by simp
    also have "\<dots> \<le> ks (hs ! j)" using P[OF j(1,2)] j i by simp
    finally show "(ks(x := k)) (hs ! parent ?i) \<le> (ks(x := k)) (hs ! j)"
      using ne[of "parent ?i"] ne[of j] j i parent_less[of ?i] parent_less[of j]
      by (auto simp del: parent_less)
  qed
qed

lemma extract_list:
  assumes "distinct hs" "butlast hs \<noteq> []"
  shows "distinct ((butlast hs)[0 := last hs])"
        "set ((butlast hs)[0 := last hs]) = set hs - {hs ! 0}"
        "length ((butlast hs)[0 := last hs]) = length hs - 1"
        "\<And>j. \<lbrakk>0 < j; j < length hs - 1\<rbrakk> \<Longrightarrow> (butlast hs)[0 := last hs] ! j = hs ! j"
proof -
  obtain a r where hs: "hs = a # r" and r: "r \<noteq> []" using assms(2) by (cases hs) (auto split: if_splits)
  have e: "(butlast hs)[0 := last hs] = last r # butlast r" using r hs by simp
  have d: "distinct r" "a \<notin> set r" using assms(1) hs by auto
  have "distinct (butlast r @ [last r])" using d(1) append_butlast_last_id[OF r] by simp
  thus "distinct ((butlast hs)[0 := last hs])" using e by simp
  have "set (butlast r @ [last r]) = set r" using append_butlast_last_id[OF r] by simp
  thus "set ((butlast hs)[0 := last hs]) = set hs - {hs ! 0}" using e d hs by auto
  show "length ((butlast hs)[0 := last hs]) = length hs - 1" using hs by simp
  fix j assume "0 < j" "j < length hs - 1"
  thus "(butlast hs)[0 := last hs] ! j = hs ! j"
    using e hs by (cases j) (auto simp: nth_butlast)
qed

lemma down_inv_extract:
  assumes "heap_prop ks hs" "distinct hs" "butlast hs \<noteq> []"
  shows "down_inv ks ((butlast hs)[0 := last hs]) 0"
  unfolding down_inv_def
proof (intro conjI allI impI)
  fix j assume j: "j < length ((butlast hs)[0 := last hs])" "0 < j" "parent j \<noteq> 0"
  have pj: "0 < parent j" "parent j < j" using j by auto
  have "(butlast hs)[0 := last hs] ! parent j = hs ! parent j"
       "(butlast hs)[0 := last hs] ! j = hs ! j"
    using extract_list(3,4)[OF assms(2,3)] j pj by auto
  moreover have "j < length hs" using j extract_list(3)[OF assms(2,3)] by simp
  ultimately show "ks ((butlast hs)[0 := last hs] ! parent j) \<le> ks ((butlast hs)[0 := last hs] ! j)"
    using assms(1) j by (simp add: heap_prop_def)
qed simp

lemma heap_extract_min_simps:
  "heap_extract_min ([], ks) = (([], ks), None)"
  "hs \<noteq> [] \<Longrightarrow> snd (heap_extract_min (hs, ks)) = Some (hs ! 0)"
  by auto

lemma heap_extract_min_fst:
  assumes "heap_invar U (hs, ks)" "hs \<noteq> []"
  shows "heap_invar U (fst (heap_extract_min (hs, ks)))"
        "heap_abstract (fst (heap_extract_min (hs, ks))) = heap_abstract (hs, ks) - {(hs ! 0, ks (hs ! 0))}"
proof -
  have H: "distinct hs" "set hs \<subseteq> U" "heap_prop ks hs" using assms by auto
  show "heap_invar U (fst (heap_extract_min (hs, ks)))"
  proof (cases "butlast hs = []")
    case False
    have l: "0 < length ((butlast hs)[0 := last hs])" using False by (cases hs) (auto split: if_splits)
    show ?thesis
      using False H assms(2) sift_down_perm[OF l, of ks] sift_down_heap[OF l down_inv_extract[OF H(3,1) False]]
        extract_list[OF H(1) False] by auto
  qed (simp add: heap_prop_def)
  show "heap_abstract (fst (heap_extract_min (hs, ks))) = heap_abstract (hs, ks) - {(hs ! 0, ks (hs ! 0))}"
  proof (cases "butlast hs = []")
    case True
    then obtain a where "hs = [a]" using assms(2) by (cases hs) (auto split: if_splits)
    thus ?thesis by simp
  next
    case False
    have l: "0 < length ((butlast hs)[0 := last hs])" using False by (cases hs) (auto split: if_splits)
    show ?thesis
      using False assms(2) sift_down_perm[OF l, of ks] extract_list[OF H(1) False] H(1)
      by auto
  qed
qed

lemma heap_key_value_queue:
  "key_value_queue U heap_empty heap_extract_min heap_decrease_key heap_insert (heap_invar U) heap_abstract"
proof (unfold_locales, goal_cases)
  case (1 H x k) thus ?case by (cases H) auto
next
  case 2 thus ?case by (simp add: heap_empty_def heap_prop_def)
next
  case 3 thus ?case by (simp add: heap_empty_def)
next
  case (4 H) thus ?case
    by (cases H) (metis heap_extract_min_fst(1) heap_extract_min.simps fst_conv)
next
  case (5 H x)
  obtain hs ks where H: "H = (hs, ks)" by fastforce
  have "hs \<noteq> []" using 5 H by auto
  hence x: "x = hs ! 0" using 5 H by (metis heap_extract_min_simps(2) option.inject)
  have m: "\<And>j. j < length hs \<Longrightarrow> ks (hs ! 0) \<le> ks (hs ! j)" using heap_prop_min 5 H by auto
  have "(hs ! 0, ks (hs ! 0)) \<in> heap_abstract (hs, ks) \<and>
        (\<forall>x' k'. (x', k') \<in> heap_abstract (hs, ks) \<longrightarrow> ks (hs ! 0) \<le> k')"
  proof (intro conjI allI impI)
    show "(hs ! 0, ks (hs ! 0)) \<in> heap_abstract (hs, ks)" using \<open>hs \<noteq> []\<close> by simp
    fix x' k' assume "(x', k') \<in> heap_abstract (hs, ks)"
    then obtain j where "j < length hs" "k' = ks (hs ! j)" by (auto simp: in_set_conv_nth)
    thus "ks (hs ! 0) \<le> k'" using m by simp
  qed
  thus ?case using H x by blast
next
  case (6 H) thus ?case by (cases H) (auto split: if_splits)
next
  case (7 H x k)
  obtain hs ks where H: "H = (hs, ks)" by fastforce
  have "hs \<noteq> []" using 7 H by auto
  hence "x = hs ! 0" using 7 H by (metis heap_extract_min_simps(2) option.inject)
  moreover have "k = ks x" using 7 H by auto
  ultimately show ?case using 7 H heap_extract_min_fst(2)[of U hs ks] \<open>hs \<noteq> []\<close> by simp
next
  case (8 H) thus ?case by (cases H) (auto split: if_splits)
next
  case (9 H x k)
  obtain hs ks where H: "H = (hs, ks)" by fastforce
  have x: "x \<notin> set hs" using 9 H by auto
  have l: "length hs < length (hs @ [x])" by simp
  show ?case
    using 9 H x sift_up_perm[OF l, of "ks(x := k)"]
      sift_up_heap[OF l up_inv_insert[of ks hs x k]] by auto
next
  case (10 H x k)
  obtain hs ks where H: "H = (hs, ks)" by fastforce
  have x: "x \<notin> set hs" using 10 H by auto
  have l: "length hs < length (hs @ [x])" by simp
  show ?case using 10 H x sift_up_perm[OF l, of "ks(x := k)"] by auto
next
  case (11 H x k k')
  obtain hs ks where H: "H = (hs, ks)" by fastforce
  have x: "x \<in> set hs" "k' = ks x" using 11 H by auto
  have l: "idx hs x < length hs" using idx_less[OF x(1)] .
  show ?case
    using 11 H x sift_up_perm[OF l, of "ks(x := k)"]
      sift_up_heap[OF l up_inv_decrease[of ks hs x k]] by auto
next
  case (12 H x k k')
  obtain hs ks where H: "H = (hs, ks)" by fastforce
  have x: "x \<in> set hs" "k = ks x" using 12 H by auto
  have l: "idx hs x < length hs" using idx_less[OF x(1)] .
  show ?case using 12 H x sift_up_perm[OF l, of "ks(x := k')"] by auto
next
  case (13 H x k k') thus ?case by (cases H) auto
qed


end


