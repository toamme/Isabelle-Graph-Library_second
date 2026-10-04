theory Partition_Oracle_Imp
  imports Partition_Oracle Exchange_Oracles_Imp
begin

section \<open>The Unit Partition Oracle in Imperative HOL\<close>

text \<open>Elements are the nats below \<open>n\<close>, blocks the nats below \<open>nb\<close>, and the block of each
  element is stored in an array (the static data of the oracle). The oracle data of a solution
  is an array counting, for every block, the elements of the solution in it. Insertion and
  deletion of an element update one counter; insertion queries read one counter, and exchange
  queries compare two blocks. All take constant time. They refine the functional oracle of
  \<open>Partition_Oracle\<close> with sets as solutions and as block sets.\<close>

subsection \<open>Code\<close>

definition part_cnt_ins :: "nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "part_cnt_ins Bl C i = do { b \<leftarrow> Array.nth Bl i; c \<leftarrow> Array.nth C b; Array.upd b (Suc c) C; return () }"

definition part_cnt_del :: "nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "part_cnt_del Bl C i = do { b \<leftarrow> Array.nth Bl i; c \<leftarrow> Array.nth C b; Array.upd b (c - 1) C; return () }"

definition part_ins_imp :: "nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "part_ins_imp Bl C y = do { b \<leftarrow> Array.nth Bl y; c \<leftarrow> Array.nth C b; return (c = 0) }"

definition part_exch_imp :: "nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "part_exch_imp Bl x y = do { a \<leftarrow> Array.nth Bl x; b \<leftarrow> Array.nth Bl y; return (a = b) }"

subsection \<open>Correctness\<close>

definition "blocks_assn n nb bl Bl = Bl \<mapsto>\<^sub>a bl * \<up>(length bl = n \<and> (\<forall> i < n. bl ! i < nb))"

definition "bcount bl X b = card {i \<in> X. bl ! i = b}"

definition "cnt_assn nb bl X C = C \<mapsto>\<^sub>a map (bcount bl X) [0..<nb] * \<up>(finite X)"

lemma bcount_insert:
  "\<lbrakk>finite X; i \<notin> X\<rbrakk> \<Longrightarrow> 
   bcount bl (insert i X) b = (if bl ! i = b then Suc (bcount bl X b) else bcount bl X b)"
proof-
  assume a: "finite X" "i \<notin> X"
  have f: "finite {j \<in> X. bl ! j = b}"
    using a(1) by simp
  show ?thesis
  proof(cases "bl ! i = b")
    case True
    have "{j \<in> insert i X. bl ! j = b} = insert i {j \<in> X. bl ! j = b}"
      using True by auto
    then show ?thesis
      unfolding bcount_def using True a(2) card_insert_disjoint[OF f] by simp
  next
    case False
    have "{j \<in> insert i X. bl ! j = b} = {j \<in> X. bl ! j = b}"
      using False by auto
    then show ?thesis
      unfolding bcount_def using False by simp
  qed
qed

lemma bcount_delete:
  "\<lbrakk>finite X; i \<in> X\<rbrakk> \<Longrightarrow> 
   bcount bl (X - {i}) b = (if bl ! i = b then bcount bl X b - 1 else bcount bl X b)"
proof-
  assume a: "finite X" "i \<in> X"
  have "bcount bl X b = bcount bl (insert i (X - {i})) b"
    using a(2) by (simp add: insert_absorb)
  then show ?thesis
    using bcount_insert[of "X - {i}" i bl b] a(1) by simp
qed

lemma bcount_zero: "finite X \<Longrightarrow> (bcount bl X b = 0) = (b \<notin> (\<lambda> i. bl ! i) ` X)"
  unfolding bcount_def by auto

lemma map_bcount_upd:
  assumes "k < nb" "\<And> b. b < nb \<Longrightarrow> g b = (if b = k then v else f b)"
  shows "(map f [0..<nb])[k := v] = map g [0..<nb]"
  by (rule nth_equalityI) (use assms in \<open>auto simp: nth_list_update\<close>)

lemma cnt_assn_new: "<emp> Array.new nb 0 <cnt_assn nb bl {}>"
  unfolding cnt_assn_def bcount_def by (sep_auto simp: map_replicate_const)

lemma part_cnt_ins_rule:
  "<cnt_assn nb bl X C * blocks_assn n nb bl Bl * \<up>(i < n \<and> i \<notin> X)> part_cnt_ins Bl C i
   <\<lambda> _. cnt_assn nb bl (insert i X) C * blocks_assn n nb bl Bl>"
proof-
  have upd: "(map (bcount bl X) [0..<nb])[bl ! i := Suc (bcount bl X (bl ! i))] = 
             map (bcount bl (insert i X)) [0..<nb]"
    if "finite X" "i \<notin> X" "bl ! i < nb" 
    by (rule map_bcount_upd) (simp_all add: that bcount_insert[OF that(1,2)])
  show ?thesis
    unfolding part_cnt_ins_def cnt_assn_def blocks_assn_def by (sep_auto simp: upd)
qed

lemma part_cnt_del_rule:
  "<cnt_assn nb bl X C * blocks_assn n nb bl Bl * \<up>(i < n \<and> i \<in> X)> part_cnt_del Bl C i
   <\<lambda> _. cnt_assn nb bl (X - {i}) C * blocks_assn n nb bl Bl>"
proof-
  have upd: "(map (bcount bl X) [0..<nb])[bl ! i := bcount bl X (bl ! i) - Suc 0] = 
             map (bcount bl (X - {i})) [0..<nb]"
    if "finite X" "i \<in> X" "bl ! i < nb" 
    by (rule map_bcount_upd) (simp_all add: that bcount_delete[OF that(1,2)])
  show ?thesis
    unfolding part_cnt_del_def cnt_assn_def blocks_assn_def by (sep_auto simp: upd)
qed

lemma part_ins_imp_rule:
  "<cnt_assn nb bl X C * blocks_assn n nb bl Bl * \<up>(y < n)> part_ins_imp Bl C y
   <\<lambda> r. cnt_assn nb bl X C * blocks_assn n nb bl Bl * 
         \<up>(finite X \<and> r = (bl ! y \<notin> (\<lambda> i. bl ! i) ` X))>"
  unfolding part_ins_imp_def cnt_assn_def blocks_assn_def by (sep_auto simp: bcount_zero)

lemma part_exch_imp_rule:
  "<blocks_assn n nb bl Bl * \<up>(x < n \<and> y < n)> part_exch_imp Bl x y
   <\<lambda> r. blocks_assn n nb bl Bl * \<up>(r = (bl ! x = bl ! y))>"
  unfolding part_exch_imp_def blocks_assn_def by sep_auto

subsection \<open>Exchange Partners\<close>

text \<open>The potential exchange partners of an element are the elements of its block. The
  handle is an array holding, for every element, the ascending list of its block. It is built
  once from the array of blocks in time \<open>O(n + nb)\<close>: first the lists of all blocks, then one
  cell per element (the lists are shared). A query reads one cell; the array of blocks stays
  with its owner.\<close>

definition "bucket bl b = filter (\<lambda> i. bl ! i = b) [0..<length bl]"

definition "part_pts bl x = bucket bl (bl ! x)"

definition "buckets_assn nb bl Kb = Kb \<mapsto>\<^sub>a map (bucket bl) [0..<nb]"

definition "part_pst n bl Kx = Kx \<mapsto>\<^sub>a map (part_pts bl) [0..<n]"

definition "buckets_imp n nb Bl = do { 
   Kb \<leftarrow> Array.new nb [];
   foldr_range_imp (\<lambda> i _. do { b \<leftarrow> Array.nth Bl i; l \<leftarrow> Array.nth Kb b; Array.upd b (i # l) Kb; 
                                return () }) n ();
   return Kb }"

definition "part_handle_imp n nb Bl = do { 
   Kb \<leftarrow> buckets_imp n nb Bl; 
   Kx \<leftarrow> Array.new n []; 
   foldr_range_imp (\<lambda> i _. do { b \<leftarrow> Array.nth Bl i; l \<leftarrow> Array.nth Kb b; Array.upd i l Kx; 
                                return () }) n ();
   return Kx }"

lemma foldr_buckets:
  assumes "\<forall> j < n. bl ! j < nb" 
  shows "i \<le> n \<Longrightarrow> foldr (\<lambda> j l. l[bl ! j := j # l ! (bl ! j)]) [i..<n] (replicate nb []) = 
                     map (\<lambda> b. filter (\<lambda> j. bl ! j = b) [i..<n]) [0..<nb]"
proof(induction "n - i" arbitrary: i)
  case 0
  then show ?case
    by (simp add: map_replicate_const)
next
  case (Suc k)
  have i: "[i..<n] = i # [Suc i..<n]" "bl ! i < nb" "Suc i \<le> n"
    using Suc.hyps(2) assms by (simp_all add: upt_conv_Cons)
  have IH: "foldr (\<lambda> j l. l[bl ! j := j # l ! (bl ! j)]) [Suc i..<n] (replicate nb []) = 
            map (\<lambda> b. filter (\<lambda> j. bl ! j = b) [Suc i..<n]) [0..<nb]"
    by (rule Suc.hyps(1)) (use Suc.hyps(2) i(3) in simp_all)
  show ?case
    by (simp only: i(1) foldr.simps comp_apply IH) (rule map_bcount_upd, simp_all add: i(2))
qed

lemma foldr_partners:
  "i \<le> n \<Longrightarrow> foldr (\<lambda> j l. l[j := part_pts bl j]) [i..<n] (replicate n []) = 
              map (\<lambda> j. if j < i then [] else part_pts bl j) [0..<n]"
proof(induction "n - i" arbitrary: i)
  case 0
  then show ?case
    by (intro nth_equalityI) simp_all
next
  case (Suc k)
  have i: "[i..<n] = i # [Suc i..<n]" "i < n" "Suc i \<le> n"
    using Suc.hyps(2) by (simp_all add: upt_conv_Cons)
  have IH: "foldr (\<lambda> j l. l[j := part_pts bl j]) [Suc i..<n] (replicate n []) = 
            map (\<lambda> j. if j < Suc i then [] else part_pts bl j) [0..<n]"
    by (rule Suc.hyps(1)) (use Suc.hyps(2) i(3) in simp_all)
  show ?case
    by (simp only: i(1) foldr.simps comp_apply IH) (rule map_bcount_upd, simp_all add: i(2))
qed

lemma buckets_rule:
  "<blocks_assn n nb bl Bl> buckets_imp n nb Bl <\<lambda> Kb. blocks_assn n nb bl Bl * buckets_assn nb bl Kb>"
proof-
  have loop: 
    "<(\<lambda> l (_ :: unit). Kb \<mapsto>\<^sub>a l * \<up>(length l = nb)) (replicate nb []) () * blocks_assn n nb bl Bl> 
       foldr_range_imp (\<lambda> i _. do { b \<leftarrow> Array.nth Bl i; l \<leftarrow> Array.nth Kb b; Array.upd b (i # l) Kb; 
                                    return () }) n ()
     <\<lambda> r. (\<lambda> l _. Kb \<mapsto>\<^sub>a l * \<up>(length l = nb)) 
             (foldr (\<lambda> j l. l[bl ! j := j # l ! (bl ! j)]) [0..<n] (replicate nb [])) r * 
           blocks_assn n nb bl Bl>" for Kb
    by (rule foldr_range_imp_rule) (sep_auto simp: blocks_assn_def)
  have fin: "\<lbrakk>length bl = n; \<forall> j < n. bl ! j < nb\<rbrakk> \<Longrightarrow> 
             foldr (\<lambda> j l. l[bl ! j := j # l ! (bl ! j)]) [0..<n] (replicate nb []) = map (bucket bl) [0..<nb]"
    using foldr_buckets[of n bl nb 0] unfolding bucket_def by simp
  show ?thesis
    unfolding buckets_imp_def buckets_assn_def 
    by (sep_auto heap: loop[unfolded blocks_assn_def] simp: fin blocks_assn_def)
qed

lemma part_handle_rule:
  "<blocks_assn n nb bl Bl> part_handle_imp n nb Bl <\<lambda> Kx. blocks_assn n nb bl Bl * part_pst n bl Kx * true>"
proof-
  have loop: 
    "<(\<lambda> l (_ :: unit). Kx \<mapsto>\<^sub>a l * \<up>(length l = n)) (replicate n []) () * 
      (blocks_assn n nb bl Bl * buckets_assn nb bl Kb)> 
       foldr_range_imp (\<lambda> i _. do { b \<leftarrow> Array.nth Bl i; l \<leftarrow> Array.nth Kb b; Array.upd i l Kx; 
                                    return () }) n ()
     <\<lambda> r. (\<lambda> l _. Kx \<mapsto>\<^sub>a l * \<up>(length l = n)) 
             (foldr (\<lambda> j l. l[j := part_pts bl j]) [0..<n] (replicate n [])) r * 
           (blocks_assn n nb bl Bl * buckets_assn nb bl Kb)>" for Kx Kb
    by (rule foldr_range_imp_rule) 
       (sep_auto simp: blocks_assn_def buckets_assn_def part_pts_def[symmetric])
  have fin: "foldr (\<lambda> j l. l[j := part_pts bl j]) [0..<n] (replicate n []) = map (part_pts bl) [0..<n]"
    using foldr_partners[of 0 n bl] by simp
  show ?thesis
    unfolding part_handle_imp_def part_pst_def by (sep_auto heap: buckets_rule loop simp: fin)
qed

lemma part_pts_rule:
  "<part_pst n bl Kx * \<up>(x < n)> Array.nth Kx x <\<lambda> r. part_pst n bl Kx * \<up>(r = part_pts bl x)>"
  unfolding part_pst_def by sep_auto

lemma part_pts_sorted: "sorted_wrt (<) (part_pts bl x)"
  unfolding part_pts_def bucket_def by (simp add: sorted_wrt_filter)

lemma part_pts_bound: "y \<in> set (part_pts bl x) \<Longrightarrow> y < length bl"
  unfolding part_pts_def bucket_def by simp

lemma part_pts_cover: 
  "\<lbrakk>x < length bl; y < length bl; bl ! x = bl ! y\<rbrakk> \<Longrightarrow> y \<in> set (part_pts bl x) \<and> x \<in> set (part_pts bl y)"
  unfolding part_pts_def bucket_def by simp

subsection \<open>Solutions Counted in Two Partitions\<close>

text \<open>A solution for two partition oracles: the Boolean array of the solution, the two arrays
  of counters and the two arrays of blocks. Insertion and deletion keep both counters
  up to date.\<close>

type_synonym bm_sol = "bool array \<times> nat array \<times> nat array \<times> nat array \<times> nat array"

definition bm_memb :: "nat \<Rightarrow> bm_sol \<Rightarrow> bool Heap" where
  "bm_memb x Si = (case Si of (Xi, C1, C2, Bl, Br) \<Rightarrow> Array.nth Xi x)"

definition bm_ins :: "nat \<Rightarrow> bm_sol \<Rightarrow> unit Heap" where
  "bm_ins x Si = (case Si of (Xi, C1, C2, Bl, Br) \<Rightarrow> do {
     b \<leftarrow> Array.nth Xi x;
     if b then return ()
     else do { Array.upd x True Xi; part_cnt_ins Bl C1 x; part_cnt_ins Br C2 x } })"

definition bm_del :: "nat \<Rightarrow> bm_sol \<Rightarrow> unit Heap" where
  "bm_del x Si = (case Si of (Xi, C1, C2, Bl, Br) \<Rightarrow> do {
     b \<leftarrow> Array.nth Xi x;
     if b then do { Array.upd x False Xi; part_cnt_del Bl C1 x; part_cnt_del Br C2 x }
     else return () })"

fun bm_sol_assn :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat set \<Rightarrow> bm_sol \<Rightarrow> assn" where
  "bm_sol_assn m nb bl br X (Xi, C1, C2, Bl, Br) = 
     xset_assn m X Xi * cnt_assn nb bl X C1 * cnt_assn nb br X C2 * 
     blocks_assn m nb bl Bl * blocks_assn m nb br Br"

lemma bm_memb_rule:
  "<bm_sol_assn m nb bl br X Si * \<up>(x < m)> bm_memb x Si 
   <\<lambda> r. bm_sol_assn m nb bl br X Si * \<up>(r = (x \<in> X))>"
  by (cases Si rule: prod_cases5) (sep_auto simp: bm_memb_def heap: xset_memb_rule)

lemma bm_ins_rule:
  "<bm_sol_assn m nb bl br X Si * \<up>(x < m)> bm_ins x Si 
   <\<lambda> _. bm_sol_assn m nb bl br (Set.insert x X) Si>"
  by (cases Si rule: prod_cases5) 
     (sep_auto simp: bm_ins_def insert_absorb heap: xset_memb_rule xset_upd_rule part_cnt_ins_rule)

lemma bm_del_rule:
  "<bm_sol_assn m nb bl br X Si * \<up>(x < m)> bm_del x Si 
   <\<lambda> _. bm_sol_assn m nb bl br (X - {x}) Si>"
proof-
  have "x \<notin> X \<Longrightarrow> X - {x} = X"
    by blast
  then show ?thesis
    by (cases Si rule: prod_cases5) 
       (sep_auto simp: bm_del_def heap: xset_memb_rule xset_upd_rule part_cnt_del_rule)
qed

end
