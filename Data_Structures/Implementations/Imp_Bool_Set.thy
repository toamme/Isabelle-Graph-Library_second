theory Imp_Bool_Set
  imports Imp_Range_Iteration
begin                       

section \<open>Sets of Nats below a Bound as Boolean Arrays\<close>

text \<open>The array holds exactly the characteristic list of the set.\<close>

definition xset_assn :: "nat \<Rightarrow> nat set \<Rightarrow> bool array \<Rightarrow> assn" where
  "xset_assn n X Xi = Xi \<mapsto>\<^sub>a map (\<lambda> i. i \<in> X) [0..<n] * \<up>(X \<subseteq> {..<n})"

lemma xset_assn_new: "<emp> Array.new n False <xset_assn n {}>"
  unfolding xset_assn_def by (sep_auto simp: map_replicate_const)

lemma xset_of_list_rule:
  "<\<up>(xs = map (\<lambda> i. i \<in> X) [0..<n] \<and> X \<subseteq> {..<n})> Array.of_list xs <xset_assn n X>"
  unfolding xset_assn_def by sep_auto

lemma xset_memb_rule:
  "<xset_assn n X Xi * \<up>(i < n)> Array.nth Xi i <\<lambda> r. xset_assn n X Xi * \<up>(r \<longleftrightarrow> i \<in> X)>"
  unfolding xset_assn_def by sep_auto

lemma map_mem_update:
  "i < n \<Longrightarrow>
   (map (\<lambda> j. j \<in> X) [0..<n])[i := b] = map (\<lambda> j. j \<in> (if b then insert i X else X - {i})) [0..<n]"
  by (rule nth_equalityI) (auto simp: nth_list_update)

lemma xset_upd_rule:
  "<xset_assn n X Xi * \<up>(i < n)> Array.upd i b Xi
     <\<lambda> r. xset_assn n (if b then insert i X else X - {i}) Xi * \<up>(r = Xi)>"
  unfolding xset_assn_def by (sep_auto simp: map_mem_update split: if_split)

text \<open>An array of length \<open>n\<close> with arbitrary content, e.g. a workspace array between two
  uses; it is cleared in place.\<close>

definition len_assn :: "nat \<Rightarrow> 'a::heap array \<Rightarrow> assn" where
  "len_assn n a = (\<exists>\<^sub>A l. a \<mapsto>\<^sub>a l * \<up>(length l = n))"

lemma len_assn_new: "<emp> Array.new n x <len_assn n>"
  unfolding len_assn_def by sep_auto

lemma xset_len: "xset_assn n X Xi \<Longrightarrow>\<^sub>A len_assn n Xi"
  unfolding xset_assn_def len_assn_def by sep_auto

definition "xset_clear_imp n Xi = fill_range_imp (\<lambda> _. False) n Xi"

lemma xset_clear_rule: "<len_assn n Xi> xset_clear_imp n Xi <\<lambda> r. xset_assn n {} Xi * \<up>(r = Xi)>"
proof-
  have "<Xi \<mapsto>\<^sub>a l * \<up>(length l = n)> xset_clear_imp n Xi <\<lambda> r. xset_assn n {} Xi * \<up>(r = Xi)>" for l
    unfolding xset_clear_imp_def
    by (rule ht_cons_post[OF fill_range_imp_rule]) (sep_auto simp: xset_assn_def)
  then show ?thesis
    unfolding len_assn_def by (rule ht_ex_pre)
qed

section \<open>An Abstract Imperative Set of Nats below a Bound\<close>

text \<open>The interface through which the algorithms see a solution: a membership test and
  insertion and deletion, which are idempotent. The handle may carry further data that its
  operations keep up to date (e.g. for oracles).\<close>

locale imp_nat_set =
  fixes n :: nat
    and sol_assn :: "nat set \<Rightarrow> 'si \<Rightarrow> assn"
    and smemb_imp :: "nat \<Rightarrow> 'si \<Rightarrow> bool Heap"
    and sins_imp :: "nat \<Rightarrow> 'si \<Rightarrow> unit Heap"
    and sdel_imp :: "nat \<Rightarrow> 'si \<Rightarrow> unit Heap"
  assumes sol_bound: "sol_assn X Si \<Longrightarrow>\<^sub>A sol_assn X Si * \<up>(X \<subseteq> {..<n})"
    and smemb_rule: "<sol_assn X Si * \<up>(x < n)> smemb_imp x Si <\<lambda> r. sol_assn X Si * \<up>(r = (x \<in> X))>"
    and sins_rule: "<sol_assn X Si * \<up>(x < n)> sins_imp x Si <\<lambda> _. sol_assn (insert x X) Si>"
    and sdel_rule: "<sol_assn X Si * \<up>(x < n)> sdel_imp x Si <\<lambda> _. sol_assn (X - {x}) Si>"

end
