theory Indexed_Heap_Imperative
  imports Indexed_Heap   Data_Structures.Fixed_Univ_Key_Value_Queue_Specs_Imp
begin

section \<open>An Indexed Binary Min-Heap in Imperative HOL\<close>

text \<open>The heap of \<open>Indexed_Heap\<close> over the universe \<open>{..<n}\<close>. It
      consists of

        \<^item> the heap array \<open>H\<close> of size \<open>n\<close>, whose first \<open>sz\<close> entries are the heap list,
        \<^item> the position array \<open>P\<close>, mapping every element in the heap to its index in \<open>H\<close>,
        \<^item> the key array \<open>K\<close>, mapping every element in the heap to its (concrete) key, and
        \<^item> a reference holding the size \<open>sz\<close>.

      All memory is allocated once by the empty operation; the other operations work in place.
      The sifting loops move a \<^emph>\<open>hole\<close> instead of swapping: the sifted element and its key are
      kept in registers and written only once, at the final position. Entries of \<open>P\<close> and \<open>K\<close> for
      elements not in the heap are irrelevant, so neither is ever reset.

      Keys are compared concretely; the functional keys are their images under the strictly
      monotone @{term queue_key}, so both comparisons agree.\<close>

type_synonym 'ai heap_imp = "nat array \<times> nat array \<times> 'ai array \<times> nat ref"

subsection \<open>Programs\<close>

text \<open>The programs are global definitions, independent of the proof locale below, so that
      they can be used by the global interpretations of the algorithms and for code generation.
      The sifting loops move a hole; the key of the sifted element is kept in a register.\<close>

partial_function (heap) sift_up_imp ::
  "nat array \<Rightarrow> nat array \<Rightarrow> 'ai::{heap, linorder} array \<Rightarrow> nat \<Rightarrow> 'ai \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "sift_up_imp Ha Pa Ka x kx i =
     (if i = 0 then do { Array.upd 0 x Ha; Array.upd x 0 Pa; return () }
      else do {
        let p = parent i;
        y \<leftarrow> Array.nth Ha p;
        ky \<leftarrow> Array.nth Ka y;
        if kx < ky then do {
          Array.upd i y Ha;
          Array.upd y i Pa;
          sift_up_imp Ha Pa Ka x kx p
        } else do { Array.upd i x Ha; Array.upd x i Pa; return () }
      })"

definition min_child_imp :: "nat array \<Rightarrow> 'ai::{heap, linorder} array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> 'ai) Heap" where
  "min_child_imp Ha Ka sz l = do {
     a \<leftarrow> Array.nth Ha l;
     ka \<leftarrow> Array.nth Ka a;
     if Suc l < sz then do {
       b \<leftarrow> Array.nth Ha (Suc l);
       kb \<leftarrow> Array.nth Ka b;
       return (if kb < ka then (Suc l, b, kb) else (l, a, ka))
     } else return (l, a, ka)
   }"

partial_function (heap) sift_down_imp ::
  "nat array \<Rightarrow> nat array \<Rightarrow> 'ai::{heap, linorder} array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'ai \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "sift_down_imp Ha Pa Ka sz x kx i =
     (if 2 * i + 1 < sz then do {
        (c, z, kz) \<leftarrow> min_child_imp Ha Ka sz (2 * i + 1);
        if kz < kx then do {
          Array.upd i z Ha;
          Array.upd z i Pa;
          sift_down_imp Ha Pa Ka sz x kx c
        } else do { Array.upd i x Ha; Array.upd x i Pa; return () }
      } else do { Array.upd i x Ha; Array.upd x i Pa; return () })"

definition heap_empty_imp :: "nat \<Rightarrow> 'ai::heap \<Rightarrow> 'ai heap_imp Heap" where
  "heap_empty_imp n k0 = do {
     Ha \<leftarrow> Array.new n 0;
     Pa \<leftarrow> Array.new n 0;
     Ka \<leftarrow> Array.new n k0;
     Sr \<leftarrow> ref 0;
     return (Ha, Pa, Ka, Sr)
   }"

definition heap_insert_imp :: "'ai::{heap, linorder} heap_imp \<Rightarrow> nat \<Rightarrow> 'ai \<Rightarrow> unit Heap" where
  "heap_insert_imp Hi x k = (case Hi of (Ha, Pa, Ka, Sr) \<Rightarrow> do {
     sz \<leftarrow> !Sr;
     Array.upd x k Ka;
     Sr := Suc sz;
     sift_up_imp Ha Pa Ka x k sz
   })"

definition heap_decrease_key_imp :: "'ai::{heap, linorder} heap_imp \<Rightarrow> nat \<Rightarrow> 'ai \<Rightarrow> unit Heap" where
  "heap_decrease_key_imp Hi x k = (case Hi of (Ha, Pa, Ka, Sr) \<Rightarrow> do {
     i \<leftarrow> Array.nth Pa x;
     Array.upd x k Ka;
     sift_up_imp Ha Pa Ka x k i
   })"

definition heap_extract_min_imp :: "'ai::{heap, linorder} heap_imp \<Rightarrow> nat option Heap" where
  "heap_extract_min_imp Hi = (case Hi of (Ha, Pa, Ka, Sr) \<Rightarrow> do {
     sz \<leftarrow> !Sr;
     if sz = 0 then return None
     else do {
       x \<leftarrow> Array.nth Ha 0;
       Sr := sz - 1;
       if sz - 1 = 0 then return (Some x)
       else do {
         y \<leftarrow> Array.nth Ha (sz - 1);
         ky \<leftarrow> Array.nth Ka y;
         sift_down_imp Ha Pa Ka (sz - 1) y ky 0;
         return (Some x)
       }
     }
   })"

definition heap_extract_min_key_imp :: "'ai::{heap, linorder} heap_imp \<Rightarrow> (nat \<times> 'ai) option Heap" where
  "heap_extract_min_key_imp Hi = (case Hi of (Ha, Pa, Ka, Sr) \<Rightarrow> do {
     sz \<leftarrow> !Sr;
     if sz = 0 then return None
     else do {
       x \<leftarrow> Array.nth Ha 0;
       k \<leftarrow> Array.nth Ka x;
       r \<leftarrow> heap_extract_min_imp Hi;
       return (map_option (\<lambda>y. (y, k)) r) } })"

locale indexed_heap_imp =
  fixes n :: nat
    and U :: "nat set"
    and queue_key :: "'ai::{heap, linorder} \<Rightarrow> 'a::linorder"
    and k0 :: 'ai
  assumes U_bound: "U \<subseteq> {..<n}"
      and key_less_iff: "\<And>a b. queue_key a < queue_key b \<longleftrightarrow> a < b"
begin

subsection \<open>Representation\<close>

text \<open>The arrays represent the heap list @{term hs}: they agree with it on its positions. While an
      element is sifted, the position @{term i} of the hole is excepted.\<close>

definition heap_rel :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "heap_rel hs hl pl \<longleftrightarrow> length hl = n \<and> length pl = n \<and>
     (\<forall>j<length hs. hl ! j = hs ! j \<and> pl ! (hs ! j) = j)"

definition hole_rel :: "nat list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "hole_rel hs i hl pl \<longleftrightarrow> length hl = n \<and> length pl = n \<and>
     (\<forall>j<length hs. j \<noteq> i \<longrightarrow> hl ! j = hs ! j \<and> pl ! (hs ! j) = j)"

definition key_rel :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat list \<Rightarrow> 'ai list \<Rightarrow> bool" where
  "key_rel ks hs kl \<longleftrightarrow> length kl = n \<and> (\<forall>v\<in>set hs. queue_key (kl ! v) = ks v)"

fun heap_assn :: "'a iheap \<Rightarrow> 'ai heap_imp \<Rightarrow> assn" where
  "heap_assn (hs, ks) (Ha, Pa, Ka, Sr) =
     (\<exists>\<^sub>Ahl pl kl. Ha \<mapsto>\<^sub>a hl * Pa \<mapsto>\<^sub>a pl * Ka \<mapsto>\<^sub>a kl * Sr \<mapsto>\<^sub>r length hs *
        \<up>(heap_rel hs hl pl \<and> key_rel ks hs kl \<and> length hs \<le> n))"

lemma distinct_length_le: "\<lbrakk>distinct xs; set xs \<subseteq> {..<m}\<rbrakk> \<Longrightarrow> length xs \<le> m"
  by (metis card_lessThan card_mono distinct_card finite_lessThan)

lemma heap_rel_hole: "heap_rel hs hl pl \<Longrightarrow> hole_rel hs i hl pl"
  unfolding heap_rel_def hole_rel_def by auto

lemma hole_fill:
  assumes "hole_rel hs i hl pl" "i < length hs" "distinct hs" "set hs \<subseteq> {..<n}"
  shows "heap_rel hs (hl[i := hs ! i]) (pl[hs ! i := i])"
  using assms distinct_length_le[OF assms(3,4)] subsetD[OF assms(4) nth_mem[OF assms(2)]] unfolding heap_rel_def hole_rel_def
  by (auto simp: nth_list_update nth_eq_iff_index_eq)

lemma hole_step:
  assumes "hole_rel hs i hl pl" "i < length hs" "p < length hs" "p \<noteq> i" "distinct hs"
      and "set hs \<subseteq> {..<n}"
  shows "hole_rel (hs[i := hs ! p, p := hs ! i]) p (hl[i := hs ! p]) (pl[hs ! p := i])"
  using assms distinct_length_le[OF assms(5,6)] subsetD[OF assms(6) nth_mem[OF assms(3)]] unfolding hole_rel_def
  by (auto simp: nth_list_update nth_eq_iff_index_eq)

lemma key_rel_len: "key_rel ks hs kl \<Longrightarrow> length kl = n"
  unfolding key_rel_def by simp

lemma key_rel_perm: "\<lbrakk>key_rel ks hs kl; set hs' = set hs\<rbrakk> \<Longrightarrow> key_rel ks hs' kl"
  unfolding key_rel_def by simp

lemma key_rel_upd:
  "\<lbrakk>key_rel ks hs kl; x < n; set hs' \<subseteq> insert x (set hs)\<rbrakk>
   \<Longrightarrow> key_rel (ks(x := queue_key k)) hs' (kl[x := k])"
  unfolding key_rel_def by (auto simp: nth_list_update)

lemma key_less_rel:
  "\<lbrakk>key_rel ks hs kl; x \<in> set hs; y \<in> set hs\<rbrakk> \<Longrightarrow> kl ! x < kl ! y \<longleftrightarrow> ks x < ks y"
  unfolding key_rel_def using key_less_iff by metis

subsection \<open>Sifting up\<close>



lemma sift_up_imp_rule:
  assumes "i < length hs" "hs ! i = x" "distinct hs" "set hs \<subseteq> {..<n}"
      and "hole_rel hs i hl pl" "key_rel ks hs kl" "queue_key kx = ks x"
  shows "<Ha \<mapsto>\<^sub>a hl * Pa \<mapsto>\<^sub>a pl * Ka \<mapsto>\<^sub>a kl> sift_up_imp Ha Pa Ka x kx i
         <\<lambda>_. \<exists>\<^sub>Ahl' pl'. Ha \<mapsto>\<^sub>a hl' * Pa \<mapsto>\<^sub>a pl' * Ka \<mapsto>\<^sub>a kl *
              \<up>(heap_rel (sift_up ks hs i) hl' pl')>"
  using assms
proof (induction i arbitrary: hs hl pl rule: less_induct)
  case (less i)
  have x: "x \<in> set hs" "x < n" using less.prems(1,2,4) nth_mem by auto
  have len: "length hl = n" "length pl = n" using less.prems(5) by (auto simp: hole_rel_def)
  have iln: "i < n" using distinct_length_le[OF less.prems(3,4)] less.prems(1) by linarith
  show ?case
  proof (cases "i = 0")
    case True
    thus ?thesis
      using hole_fill[OF less.prems(5,1,3,4)] less.prems(1,2) len x
      by (subst sift_up_imp.simps) sep_auto
  next
    case i0: False
    let ?p = "parent i"
    have pi: "?p < i" using i0 by simp
    have p: "?p < i" "?p < length hs" "?p \<noteq> i" using pi less.prems(1) by auto
    have y: "hl ! ?p = hs ! ?p" using less.prems(5) p by (auto simp: hole_rel_def)
    have ys: "hs ! ?p \<in> set hs" "hs ! ?p < n" using p less.prems(4) nth_mem by auto
    have ky: "kx < kl ! (hs ! ?p) \<longleftrightarrow> ks x < ks (hs ! ?p)"
      using less.prems(6,7) ys(1) key_less_iff unfolding key_rel_def by metis
    have plen: "?p < n" "hs ! ?p < length kl" using p iln ys less.prems(6) by (auto simp: key_rel_def)
    show ?thesis
    proof (cases "ks x < ks (hs ! ?p)")
      case lt: True
      let ?hs = "hs[i := hs ! ?p, ?p := hs ! i]"
      have IH: "<Ha \<mapsto>\<^sub>a hl[i := hs ! ?p] * Pa \<mapsto>\<^sub>a pl[hs ! ?p := i] * Ka \<mapsto>\<^sub>a kl>
                  sift_up_imp Ha Pa Ka x kx ?p
                <\<lambda>_. \<exists>\<^sub>Ahl' pl'. Ha \<mapsto>\<^sub>a hl' * Pa \<mapsto>\<^sub>a pl' * Ka \<mapsto>\<^sub>a kl *
                     \<up>(heap_rel (sift_up ks ?hs ?p) hl' pl')>"
      proof (rule less.IH[OF p(1)])
        show "?p < length ?hs" "?hs ! ?p = x" "distinct ?hs" "set ?hs \<subseteq> {..<n}"
          using p less.prems(1-4) by auto
        show "hole_rel ?hs ?p (hl[i := hs ! ?p]) (pl[hs ! ?p := i])"
          by (rule hole_step[OF less.prems(5,1) p(2,3) less.prems(3,4)])
        show "key_rel ks ?hs kl"
          by (rule key_rel_perm[OF less.prems(6)]) (use p less.prems(1) in simp)
      qed (rule less.prems(7))
      have "sift_up ks hs i = sift_up ks ?hs ?p"
        by (rule sift_up_rec) (use i0 lt less.prems(2) in simp_all)
      thus ?thesis
        using IH lt ky y len iln plen i0 ys
        by (subst sift_up_imp.simps) (sep_auto heap: IH)
    next
      case ge: False
      have "sift_up ks hs i = hs" 
        using sift_up_stop ge less.prems(2) by metis
      thus ?thesis
        using hole_fill[OF less.prems(5,1,3,4)] less.prems(1,2) ge ky y len iln plen i0 x
        by (subst sift_up_imp.simps) sep_auto
    qed
  qed
qed

subsection \<open>Sifting down\<close>

text \<open>The smaller child of the hole, together with its element and key, read once each.\<close>



lemma key_rel_mono: "\<lbrakk>key_rel ks hs kl; set hs' \<subseteq> set hs\<rbrakk> \<Longrightarrow> key_rel ks hs' kl"
  unfolding key_rel_def by auto

lemma min_child_imp_rule:
  assumes l: "2 * i + 1 < length hs" and hs: "distinct hs" "set hs \<subseteq> {..<n}"
      and rel: "hole_rel hs i hl pl" "key_rel ks hs kl"
  shows "<Ha \<mapsto>\<^sub>a hl * Ka \<mapsto>\<^sub>a kl> min_child_imp Ha Ka (length hs) (2 * i + 1)
         <\<lambda>r. Ha \<mapsto>\<^sub>a hl * Ka \<mapsto>\<^sub>a kl *
              \<up>(r = (min_child ks hs i, hs ! min_child ks hs i, kl ! (hs ! min_child ks hs i)))>"
proof -
  have len: "length hl = n" "length kl = n" using rel by (auto simp: hole_rel_def key_rel_def)
  have e: "hl ! (2 * i + 1) = hs ! (2 * i + 1)" using rel(1) l by (auto simp: hole_rel_def)
  have m: "hs ! (2 * i + 1) \<in> set hs" "hs ! (2 * i + 1) < n" using l hs(2) nth_mem by auto
  have sl: "length hs \<le> n" by (rule distinct_length_le[OF hs])
  have ln: "2 * i + 1 < n" using l sl by linarith
  show ?thesis
  proof (cases "Suc (2 * i + 1) < length hs")
    case True
    have e': "hl ! Suc (2 * i + 1) = hs ! Suc (2 * i + 1)" using rel(1) True by (auto simp: hole_rel_def)
    have m': "hs ! Suc (2 * i + 1) \<in> set hs" "hs ! Suc (2 * i + 1) < n" using True hs(2) nth_mem by auto
    have "Suc (2 * i + 1) < n" using True sl by linarith
    moreover have "kl ! (hs ! Suc (2 * i + 1)) < kl ! (hs ! (2 * i + 1)) \<longleftrightarrow>
                   ks (hs ! Suc (2 * i + 1)) < ks (hs ! (2 * i + 1))"
      using key_less_rel[OF rel(2) m'(1) m(1)] .
    ultimately show ?thesis
      unfolding min_child_imp_def min_child_def
      using True e e' m m' len ln by sep_auto
  next
    case False
    thus ?thesis
      unfolding min_child_imp_def min_child_def
      using e m len ln by sep_auto
  qed
qed



lemma sift_down_imp_rule:
  assumes "i < length hs" "hs ! i = x" "distinct hs" "set hs \<subseteq> {..<n}"
      and "hole_rel hs i hl pl" "key_rel ks hs kl" "queue_key kx = ks x"
  shows "<Ha \<mapsto>\<^sub>a hl * Pa \<mapsto>\<^sub>a pl * Ka \<mapsto>\<^sub>a kl> sift_down_imp Ha Pa Ka (length hs) x kx i
         <\<lambda>_. \<exists>\<^sub>Ahl' pl'. Ha \<mapsto>\<^sub>a hl' * Pa \<mapsto>\<^sub>a pl' * Ka \<mapsto>\<^sub>a kl *
              \<up>(heap_rel (sift_down ks hs i) hl' pl')>"
  using assms
proof (induction ks hs i arbitrary: hl pl rule: sift_down.induct)
  case (1 ks hs i)
  have x: "x \<in> set hs" "x < n" using "1.prems"(1,2,4) nth_mem by auto
  have len: "length hl = n" "length pl = n" using "1.prems"(5) by (auto simp: hole_rel_def)
  have iln: "i < n" using distinct_length_le[OF "1.prems"(3,4)] "1.prems"(1) by linarith
  have stop: "<Ha \<mapsto>\<^sub>a hl * Pa \<mapsto>\<^sub>a pl * Ka \<mapsto>\<^sub>a kl>
                do { Array.upd i x Ha; Array.upd x i Pa; return () }
              <\<lambda>_. \<exists>\<^sub>Ahl' pl'. Ha \<mapsto>\<^sub>a hl' * Pa \<mapsto>\<^sub>a pl' * Ka \<mapsto>\<^sub>a kl * \<up>(heap_rel hs hl' pl')>"
    using hole_fill[OF "1.prems"(5,1,3,4)] "1.prems"(2) len x iln by sep_auto
  show ?case
  proof (cases "2 * i + 1 < length hs")
    case False
    thus ?thesis using sift_down_stop[of i hs ks] stop
      by (subst sift_down_imp.simps) simp
  next
    case l: True
    let ?c = "min_child ks hs i"
    have c: "i < ?c" "?c < length hs" "?c \<noteq> i" using min_child_bounds[OF l, of ks] by auto
    have zs: "hs ! ?c \<in> set hs" "hs ! ?c < n" using c "1.prems"(4) nth_mem by auto
    have kz: "kl ! (hs ! ?c) < kx \<longleftrightarrow> ks (hs ! ?c) < ks x"
      using "1.prems"(6,7) zs(1) key_less_iff unfolding key_rel_def by metis
    note MC = min_child_imp_rule[OF l "1.prems"(3,4,5,6), of Ha]
    show ?thesis
    proof (cases "ks (hs ! ?c) < ks x")
      case lt: True
      let ?hs = "hs[i := hs ! ?c, ?c := hs ! i]"
      have cond: "2 * i + 1 < length hs \<and> ks (hs ! ?c) < ks (hs ! i)" using l lt "1.prems"(2) by simp
      have IH: "<Ha \<mapsto>\<^sub>a hl[i := hs ! ?c] * Pa \<mapsto>\<^sub>a pl[hs ! ?c := i] * Ka \<mapsto>\<^sub>a kl>
                  sift_down_imp Ha Pa Ka (length hs) x kx ?c
                <\<lambda>_. \<exists>\<^sub>Ahl' pl'. Ha \<mapsto>\<^sub>a hl' * Pa \<mapsto>\<^sub>a pl' * Ka \<mapsto>\<^sub>a kl *
                     \<up>(heap_rel (sift_down ks ?hs ?c) hl' pl')>"
      proof -
        have "<Ha \<mapsto>\<^sub>a hl[i := hs ! ?c] * Pa \<mapsto>\<^sub>a pl[hs ! ?c := i] * Ka \<mapsto>\<^sub>a kl>
                  sift_down_imp Ha Pa Ka (length ?hs) x kx ?c
                <\<lambda>_. \<exists>\<^sub>Ahl' pl'. Ha \<mapsto>\<^sub>a hl' * Pa \<mapsto>\<^sub>a pl' * Ka \<mapsto>\<^sub>a kl *
                     \<up>(heap_rel (sift_down ks ?hs ?c) hl' pl')>"
        proof (rule "1.IH"[OF cond])
          show "?c < length ?hs" "?hs ! ?c = x" "distinct ?hs" "set ?hs \<subseteq> {..<n}"
            using c "1.prems"(1-4) by auto
          show "hole_rel ?hs ?c (hl[i := hs ! ?c]) (pl[hs ! ?c := i])"
            by (rule hole_step[OF "1.prems"(5,1) c(2,3) "1.prems"(3,4)])
          show "key_rel ks ?hs kl"
            by (rule key_rel_perm[OF "1.prems"(6)]) (use c "1.prems"(1) in simp)
        qed (rule "1.prems"(7))
        thus ?thesis by simp
      qed
      have "sift_down ks hs i = sift_down ks ?hs ?c"
        using cond by (subst sift_down.simps) simp
      thus ?thesis
        using l lt kz len iln zs c
        by (subst sift_down_imp.simps) (sep_auto heap: MC IH)
    next
      case ge: False
      have "sift_down ks hs i = hs"
        using sift_down_stop ge "1.prems"(2) by metis
      thus ?thesis
        using l ge kz hole_fill[OF "1.prems"(5,1,3,4)] "1.prems"(2) len x iln
        by (subst sift_down_imp.simps) (sep_auto heap: MC)
    qed
  qed
qed

subsection \<open>Operations\<close>



lemma heap_empty_imp_rule: "<emp> heap_empty_imp n k0 <\<lambda>Hi. heap_assn heap_empty Hi>"
  unfolding heap_empty_imp_def heap_empty_def
  by (sep_auto simp: heap_rel_def key_rel_def)

lemma heap_insert_imp_rule:
  assumes "heap_invar U (hs, ks)" "x \<in> U" "x \<notin> set hs"
  shows "<heap_assn (hs, ks) (Ha, Pa, Ka, Sr)> heap_insert_imp (Ha, Pa, Ka, Sr) x k
         <\<lambda>_. heap_assn (heap_insert (hs, ks) x (queue_key k)) (Ha, Pa, Ka, Sr)>"
proof -
  let ?ks = "ks(x := queue_key k)" and ?hs = "hs @ [x]"
  have H: "distinct hs" "set hs \<subseteq> {..<n}" using assms(1) U_bound by auto
  have xn: "x < n" using assms(2) U_bound by auto
  have d: "distinct ?hs" "set ?hs \<subseteq> {..<n}" using H xn assms(3) by auto
  have sl: "length ?hs \<le> n" by (rule distinct_length_le[OF d])
  have perm: "length (sift_up ?ks ?hs (length hs)) = Suc (length hs)"
             "set (sift_up ?ks ?hs (length hs)) = insert x (set hs)"
             "distinct (sift_up ?ks ?hs (length hs))"
    using sift_up_perm[of "length hs" ?hs ?ks] d by auto
  have R: "\<And>hl pl kl. \<lbrakk>heap_rel hs hl pl; key_rel ks hs kl\<rbrakk> \<Longrightarrow>
      <Ha \<mapsto>\<^sub>a hl * Pa \<mapsto>\<^sub>a pl * Ka \<mapsto>\<^sub>a kl[x := k]> sift_up_imp Ha Pa Ka x k (length hs)
      <\<lambda>_. \<exists>\<^sub>Ahl' pl'. Ha \<mapsto>\<^sub>a hl' * Pa \<mapsto>\<^sub>a pl' * Ka \<mapsto>\<^sub>a kl[x := k] *
           \<up>(heap_rel (sift_up ?ks ?hs (length hs)) hl' pl')>"
  proof (rule sift_up_imp_rule)
    fix hl pl kl assume rel: "heap_rel hs hl pl" "key_rel ks hs kl"
    show "length hs < length ?hs" "?hs ! length hs = x" "distinct ?hs" "set ?hs \<subseteq> {..<n}"
      using d by auto
    show "hole_rel ?hs (length hs) hl pl"
      using rel(1) unfolding heap_rel_def hole_rel_def by (auto simp: nth_append)
    show "key_rel ?ks ?hs (kl[x := k])" by (rule key_rel_upd[OF rel(2) xn]) simp
    show "queue_key k = ?ks x" by simp
  qed
  have K: "\<And>kl. key_rel ks hs kl \<Longrightarrow> key_rel ?ks (sift_up ?ks ?hs (length hs)) (kl[x := k])"
    using key_rel_upd[OF _ xn] perm(2) by auto
  show ?thesis
    unfolding heap_insert_imp_def heap_assn.simps heap_insert.simps
    using perm sl xn
    by (sep_auto heap: R simp: K key_rel_len)
qed

lemma heap_rel_pos: "\<lbrakk>heap_rel hs hl pl; x \<in> set hs\<rbrakk> \<Longrightarrow> pl ! x = idx hs x"
  unfolding heap_rel_def using idx_less idx_nth by metis

lemma heap_rel_len: "heap_rel hs hl pl \<Longrightarrow> length hl = n \<and> length pl = n"
  unfolding heap_rel_def by simp

lemma heap_decrease_key_imp_rule:
  assumes "heap_invar U (hs, ks)" "x \<in> set hs"
  shows "<heap_assn (hs, ks) (Ha, Pa, Ka, Sr)> heap_decrease_key_imp (Ha, Pa, Ka, Sr) x k
         <\<lambda>_. heap_assn (heap_decrease_key (hs, ks) x (queue_key k)) (Ha, Pa, Ka, Sr)>"
proof -
  let ?ks = "ks(x := queue_key k)" and ?i = "idx hs x"
  have H: "distinct hs" "set hs \<subseteq> {..<n}" using assms(1) U_bound by auto
  have xn: "x < n" using assms(2) H(2) by auto
  have i: "?i < length hs" "hs ! ?i = x" using idx_less[OF assms(2)] assms(2) by auto
  have perm: "length (sift_up ?ks hs ?i) = length hs" "set (sift_up ?ks hs ?i) = set hs"
    using sift_up_perm[OF i(1), of ?ks] by auto
  have R: "\<And>hl pl kl. \<lbrakk>heap_rel hs hl pl; key_rel ks hs kl\<rbrakk> \<Longrightarrow>
      <Ha \<mapsto>\<^sub>a hl * Pa \<mapsto>\<^sub>a pl * Ka \<mapsto>\<^sub>a kl[x := k]> sift_up_imp Ha Pa Ka x k ?i
      <\<lambda>_. \<exists>\<^sub>Ahl' pl'. Ha \<mapsto>\<^sub>a hl' * Pa \<mapsto>\<^sub>a pl' * Ka \<mapsto>\<^sub>a kl[x := k] *
           \<up>(heap_rel (sift_up ?ks hs ?i) hl' pl')>"
  proof (rule sift_up_imp_rule[OF i H])
    fix hl pl kl assume rel: "heap_rel hs hl pl" "key_rel ks hs kl"
    show "hole_rel hs ?i hl pl" by (rule heap_rel_hole[OF rel(1)])
    show "key_rel ?ks hs (kl[x := k])" by (rule key_rel_upd[OF rel(2) xn]) blast
    show "queue_key k = ?ks x" by simp
  qed
  have K: "\<And>kl. key_rel ks hs kl \<Longrightarrow> key_rel ?ks (sift_up ?ks hs ?i) (kl[x := k])"
    by (rule key_rel_upd[OF _ xn]) (use perm(2) in blast)+
  show ?thesis
    unfolding heap_decrease_key_imp_def heap_assn.simps heap_decrease_key.simps
    using perm xn assms(2) heap_rel_len
    by (sep_auto heap: R simp: K key_rel_len heap_rel_pos)
qed

lemma heap_extract_min_imp_rule:
  assumes "heap_invar U (hs, ks)"
  shows "<heap_assn (hs, ks) (Ha, Pa, Ka, Sr)> heap_extract_min_imp (Ha, Pa, Ka, Sr)
         <\<lambda>r. heap_assn (fst (heap_extract_min (hs, ks))) (Ha, Pa, Ka, Sr) *
              \<up>(r = snd (heap_extract_min (hs, ks)))>"
proof -
  have H: "distinct hs" "set hs \<subseteq> {..<n}" using assms(1) U_bound by auto
  have sl: "length hs \<le> n" by (rule distinct_length_le[OF H])
  have h0: "\<And>hl pl. \<lbrakk>heap_rel hs hl pl; hs \<noteq> []\<rbrakk> \<Longrightarrow> hl ! 0 = hs ! 0"
    unfolding heap_rel_def by auto
  consider "hs = []" | "hs \<noteq> []" "butlast hs = []" | "butlast hs \<noteq> []" by fastforce
  thus ?thesis
  proof cases
    case 1 thus ?thesis unfolding heap_extract_min_imp_def by sep_auto
  next
    case 2
    then obtain a where a: "hs = [a]" by (cases hs) (auto split: if_splits)
    have "\<And>hl pl. heap_rel hs hl pl \<Longrightarrow> heap_rel [] hl pl"
      unfolding heap_rel_def by simp
    moreover have "\<And>kl. key_rel ks hs kl \<Longrightarrow> key_rel ks [] kl"
      unfolding key_rel_def by simp
    ultimately show ?thesis
      unfolding heap_extract_min_imp_def using a sl by (sep_auto simp: a heap_rel_def key_rel_def)
  next
    case c3: 3
    let ?hs = "(butlast hs)[0 := last hs]"
    have ne: "hs \<noteq> []" using c3 by auto
    note E = extract_list[OF H(1) c3]
    have l: "0 < length ?hs" "length ?hs = length hs - 1"
      using c3 E(3) by (cases hs) (auto split: if_splits)
    have lst: "last hs \<in> set hs" "last hs = hs ! (length hs - 1)" "last hs < n"
      using ne H(2) last_conv_nth by auto
    have R: "\<And>hl pl kl. \<lbrakk>heap_rel hs hl pl; key_rel ks hs kl\<rbrakk> \<Longrightarrow>
        <Ha \<mapsto>\<^sub>a hl * Pa \<mapsto>\<^sub>a pl * Ka \<mapsto>\<^sub>a kl>
          sift_down_imp Ha Pa Ka (length hs - 1) (last hs) (kl ! last hs) 0
        <\<lambda>_. \<exists>\<^sub>Ahl' pl'. Ha \<mapsto>\<^sub>a hl' * Pa \<mapsto>\<^sub>a pl' * Ka \<mapsto>\<^sub>a kl *
             \<up>(heap_rel (sift_down ks ?hs 0) hl' pl')>"
    proof -
      fix hl pl kl assume rel: "heap_rel hs hl pl" "key_rel ks hs kl"
      have "<Ha \<mapsto>\<^sub>a hl * Pa \<mapsto>\<^sub>a pl * Ka \<mapsto>\<^sub>a kl>
              sift_down_imp Ha Pa Ka (length ?hs) (last hs) (kl ! last hs) 0
            <\<lambda>_. \<exists>\<^sub>Ahl' pl'. Ha \<mapsto>\<^sub>a hl' * Pa \<mapsto>\<^sub>a pl' * Ka \<mapsto>\<^sub>a kl *
                 \<up>(heap_rel (sift_down ks ?hs 0) hl' pl')>"
      proof (rule sift_down_imp_rule)
        show "0 < length ?hs" by (rule l(1))
        show "?hs ! 0 = last hs" using l(1) by simp
        show "distinct ?hs" "set ?hs \<subseteq> {..<n}" using E(1,2) H(2) by auto
        show "hole_rel ?hs 0 hl pl"
          using rel(1) E(3,4) unfolding heap_rel_def hole_rel_def by auto
        show "key_rel ks ?hs kl" by (rule key_rel_mono[OF rel(2)]) (use E(2) in auto)
        show "queue_key (kl ! last hs) = ks (last hs)" using rel(2) lst(1) by (simp add: key_rel_def)
      qed
      thus "<Ha \<mapsto>\<^sub>a hl * Pa \<mapsto>\<^sub>a pl * Ka \<mapsto>\<^sub>a kl>
              sift_down_imp Ha Pa Ka (length hs - 1) (last hs) (kl ! last hs) 0
            <\<lambda>_. \<exists>\<^sub>Ahl' pl'. Ha \<mapsto>\<^sub>a hl' * Pa \<mapsto>\<^sub>a pl' * Ka \<mapsto>\<^sub>a kl *
                 \<up>(heap_rel (sift_down ks ?hs 0) hl' pl')>" using l(2) by simp
    qed
    have perm: "length (sift_down ks ?hs 0) = length hs - 1" "set (sift_down ks ?hs 0) \<subseteq> set hs"
      using sift_down_perm[OF l(1), of ks] l(2) E(2) by auto
    have K: "\<And>kl. key_rel ks hs kl \<Longrightarrow> key_rel ks (sift_down ks ?hs 0) kl"
      using key_rel_mono perm(2) by blast
    have hl: "\<And>hl pl. heap_rel hs hl pl \<Longrightarrow> hl ! (length hs - 1) = last hs"
      using lst ne unfolding heap_rel_def by auto
    have ln: "length hs - 1 \<noteq> 0" using c3 by (cases hs) (auto split: if_splits)
    have ex: "heap_extract_min (hs, ks) = ((sift_down ks ?hs 0, ks), Some (hs ! 0))"
      using c3 ne by simp
    have main: "<Ha \<mapsto>\<^sub>a hl * Pa \<mapsto>\<^sub>a pl * Ka \<mapsto>\<^sub>a kl * Sr \<mapsto>\<^sub>r length hs>
                  heap_extract_min_imp (Ha, Pa, Ka, Sr)
                <\<lambda>r. heap_assn (sift_down ks ?hs 0, ks) (Ha, Pa, Ka, Sr) * \<up>(r = Some (hs ! 0))>"
      if rel: "heap_rel hs hl pl" "key_rel ks hs kl" for hl pl kl
    proof -
      have lens: "0 < length hl" "length hs - 1 < length hl" "last hs < length kl"
        using heap_rel_len[OF rel(1)] key_rel_len[OF rel(2)] sl ne lst(3) by (auto simp: neq_Nil_conv)
      note R' = R[OF rel]
      have sd: "key_rel ks (sift_down ks ?hs 0) kl" "length (sift_down ks ?hs 0) = length hs - 1"
               "length (sift_down ks ?hs 0) \<le> n"
        using K[OF rel(2)] perm(1) sl by auto
      show ?thesis
        unfolding heap_extract_min_imp_def prod.case heap_assn.simps
        using ne ln lens h0[OF rel(1) ne] hl[OF rel(1)] sd
        by (sep_auto heap: R')
    qed
    show ?thesis
      unfolding heap_assn.simps ex fst_conv snd_conv
      by (sep_auto heap: main)
  qed
qed
(*
subsection \<open>The heap is a key-value queue\<close>

sublocale iheap: key_value_queue_imp U heap_empty heap_extract_min
 heap_decrease_key heap_insert
    "heap_invar U" heap_abstract  queue_key heap_assn "heap_empty_imp n k0" 
heap_extract_min_imp
    heap_decrease_key_imp heap_insert_imp
proof (rule key_value_queue_imp.intro[OF heap_key_value_queue], unfold_locales, goal_cases)
  case 1 show ?case by (rule heap_empty_imp_rule)
next
  case (2 H Hi)
  obtain hs ks where H: "H = (hs, ks)" by fastforce
  obtain Ha Pa Ka Sr where Hi: "Hi = (Ha, Pa, Ka, Sr)" by (cases Hi) auto
  show ?case using heap_extract_min_imp_rule 2 H Hi by simp
next
  case (3 H x Hi k)
  obtain hs ks where H: "H = (hs, ks)" by fastforce
  obtain Ha Pa Ka Sr where Hi: "Hi = (Ha, Pa, Ka, Sr)" by (cases Hi) auto
  have "x \<notin> set hs" using 3 H by auto
  thus ?case using heap_insert_imp_rule 3 H Hi by simp
next
  case (4 H x k' k Hi)
  obtain hs ks where H: "H = (hs, ks)" by fastforce
  obtain Ha Pa Ka Sr where Hi: "Hi = (Ha, Pa, Ka, Sr)" by (cases Hi) auto
  have "x \<in> set hs" using 4 H by auto
  thus ?case using heap_decrease_key_imp_rule 4 H Hi by simp
qed

qed
*)
end
definition heap_clear_imp :: "'ai heap_imp \<Rightarrow> unit Heap" where
  "heap_clear_imp Hi = (case Hi of (Ha, Pa, Ka, Sr) \<Rightarrow> (Sr := 0))"

definition heap_key_of_imp :: "'ai::{heap, linorder} heap_imp \<Rightarrow> nat \<Rightarrow> 'ai option Heap" where
  "heap_key_of_imp Hi x = (case Hi of (Ha, Pa, Ka, Sr) \<Rightarrow> do {
     sz \<leftarrow> !Sr;
     i \<leftarrow> Array.nth Pa x;
     if i < sz then do {
       y \<leftarrow> Array.nth Ha i;
       if y = x then do { k \<leftarrow> Array.nth Ka x; return (Some k) } else return None }
     else return None })"

context indexed_heap_imp
begin

subsection \<open>Reading the Heap\<close>

lemma heap_read_size_rule:
  "<heap_assn (hs, ks) (Ha, Pa, Ka, Sr)> !Sr
   <\<lambda>r. heap_assn (hs, ks) (Ha, Pa, Ka, Sr) * \<up>(r = length hs)>"
  by sep_auto

lemma heap_read_at_rule:
  "i < length hs \<Longrightarrow>
   <heap_assn (hs, ks) (Ha, Pa, Ka, Sr)> Array.nth Ha i
   <\<lambda>r. heap_assn (hs, ks) (Ha, Pa, Ka, Sr) * \<up>(r = hs ! i)>"
  by (sep_auto simp: heap_rel_def)

lemma heap_read_pos_rule:
  "x < n \<Longrightarrow>
   <heap_assn (hs, ks) (Ha, Pa, Ka, Sr)> Array.nth Pa x
   <\<lambda>r. heap_assn (hs, ks) (Ha, Pa, Ka, Sr) * \<up>(x \<in> set hs \<longrightarrow> r = idx hs x)>"
proof -
  assume x: "x < n"
  have "\<And>hl pl. heap_rel hs hl pl \<Longrightarrow> x < length pl \<and> (x \<in> set hs \<longrightarrow> pl ! x = idx hs x)"
    using x heap_rel_len heap_rel_pos by metis
  thus ?thesis by sep_auto
qed

lemma heap_read_key_rule:
  "\<lbrakk>x \<in> set hs; x < n\<rbrakk> \<Longrightarrow>
   <heap_assn (hs, ks) (Ha, Pa, Ka, Sr)> Array.nth Ka x
   <\<lambda>r. heap_assn (hs, ks) (Ha, Pa, Ka, Sr) * \<up>(queue_key r = ks x)>"
proof -
  assume x: "x \<in> set hs" "x < n"
  have "\<And>kl. key_rel ks hs kl \<Longrightarrow> x < length kl \<and> queue_key (kl ! x) = ks x"
    using x unfolding key_rel_def by simp
  thus ?thesis by sep_auto
qed

subsection \<open>The Additional Operations\<close>

lemma heap_clear_imp_rule:
  "<heap_assn H (Ha, Pa, Ka, Sr)> heap_clear_imp (Ha, Pa, Ka, Sr)
   <\<lambda>_. heap_assn heap_empty (Ha, Pa, Ka, Sr)>"
  by (cases H) (sep_auto simp: heap_clear_imp_def heap_empty_def heap_rel_def key_rel_def)

lemma heap_key_of_imp_rule:
  assumes "heap_invar U (hs, ks)" "x \<in> U"
  shows "<heap_assn (hs, ks) (Ha, Pa, Ka, Sr)> heap_key_of_imp (Ha, Pa, Ka, Sr) x
         <\<lambda>r. heap_assn (hs, ks) (Ha, Pa, Ka, Sr) *
              \<up>(case r of None \<Rightarrow> x \<notin> set hs | Some k \<Rightarrow> x \<in> set hs \<and> queue_key k = ks x)>"
proof -
  have xn: "x < n" using assms(2) U_bound by auto
  note heap_assn.simps[simp del]
  show ?thesis
  proof (cases "x \<in> set hs")
    case True
    have i: "idx hs x < length hs" using True by (rule idx_less)
    have pos: "<heap_assn (hs, ks) (Ha, Pa, Ka, Sr)> Array.nth Pa x
               <\<lambda>r. heap_assn (hs, ks) (Ha, Pa, Ka, Sr) * \<up>(r = idx hs x)>"
      by (sep_auto heap: heap_read_pos_rule[OF xn] simp: True)
    show ?thesis
      unfolding heap_key_of_imp_def prod.case
      by (sep_auto heap: heap_read_size_rule pos heap_read_at_rule[OF i]
                         heap_read_key_rule[OF True xn]
                   simp: i True)
  next
    case False
    hence nx: "x \<notin> set hs" .
    have pos: "<heap_assn (hs, ks) (Ha, Pa, Ka, Sr)> Array.nth Pa x
               <\<lambda>r. heap_assn (hs, ks) (Ha, Pa, Ka, Sr)>"
      by (sep_auto heap: heap_read_pos_rule[OF xn])
    have at: "\<And>i. i < length hs \<Longrightarrow> <heap_assn (hs, ks) (Ha, Pa, Ka, Sr)> Array.nth Ha i
               <\<lambda>r. heap_assn (hs, ks) (Ha, Pa, Ka, Sr) * \<up>(r \<noteq> x)>"
      using nx by (sep_auto heap: heap_read_at_rule)
    show ?thesis
      unfolding heap_key_of_imp_def prod.case
      by (sep_auto heap: heap_read_size_rule pos at simp: nx)
  qed
qed

lemma heap_extract_min_key_imp_rule:
  assumes "heap_invar U (hs, ks)"
  shows "<heap_assn (hs, ks) (Ha, Pa, Ka, Sr)> heap_extract_min_key_imp (Ha, Pa, Ka, Sr)
         <\<lambda>r. heap_assn (fst (heap_extract_min (hs, ks))) (Ha, Pa, Ka, Sr) *
              \<up>(map_option fst r = snd (heap_extract_min (hs, ks)) \<and>
                (\<forall>x k. r = Some (x, k) \<longrightarrow> x \<in> set hs \<and> queue_key k = ks x))>"
proof(cases "hs = []")
  case True
  thus ?thesis
    unfolding heap_extract_min_key_imp_def prod.case
    by (sep_auto heap: heap_read_size_rule)
next
  case False
  have h0: "hs ! 0 \<in> set hs" using False by simp
  have h0n: "hs ! 0 < n" using assms h0 U_bound by auto
  have ex: "snd (heap_extract_min (hs, ks)) = Some (hs ! 0)" using False by simp
  show ?thesis
    unfolding heap_extract_min_key_imp_def prod.case
    using False
    by (sep_auto heap: heap_read_size_rule heap_read_at_rule heap_read_key_rule[OF h0 h0n]
                       heap_extract_min_imp_rule[OF assms] simp: ex)
qed

subsection \<open>The Heap is a Queue for the Hungarian Method\<close>

lemma heap_key_value_queue_hungarian:
  "key_value_queue U heap_empty heap_extract_min heap_decrease_key heap_insert
     (heap_invar U) heap_abstract"
  using heap_key_value_queue
  unfolding key_value_queue_def  .

sublocale hqueue: key_value_queue_imp U heap_empty heap_extract_min heap_decrease_key
    heap_insert "heap_invar U" heap_abstract queue_key heap_assn "heap_empty_imp n k0"
    heap_clear_imp heap_extract_min_key_imp heap_key_of_imp heap_decrease_key_imp heap_insert_imp
proof (rule key_value_queue_imp.intro[OF heap_key_value_queue_hungarian], unfold_locales,
       goal_cases)
  case 1 show ?case by (rule heap_empty_imp_rule)
next
  case (2 H Hi)
  obtain hs ks where H: "H = (hs, ks)" by fastforce
  obtain Ha Pa Ka Sr where Hi: "Hi = (Ha, Pa, Ka, Sr)" by (cases Hi) auto
  show ?case unfolding H Hi by (rule heap_clear_imp_rule)
next
  case (3 H Hi)
  obtain hs ks where H: "H = (hs, ks)" by fastforce
  obtain Ha Pa Ka Sr where Hi: "Hi = (Ha, Pa, Ka, Sr)" by (cases Hi) auto
  note heap_assn.simps[simp del]
  show ?case
    unfolding H Hi
    by (rule ht_cons_post[OF heap_extract_min_key_imp_rule[OF 3[unfolded H]]]) sep_auto
next
  case (4 H x Hi)
  obtain hs ks where H: "H = (hs, ks)" by fastforce
  obtain Ha Pa Ka Sr where Hi: "Hi = (Ha, Pa, Ka, Sr)" by (cases Hi) auto
  note heap_assn.simps[simp del]
  show ?case
    unfolding H Hi
    by (rule ht_cons_post[OF heap_key_of_imp_rule[OF 4(1)[unfolded H] 4(2)]])
       (sep_auto split: option.splits)
next
  case (5 H x Hi k)
  obtain hs ks where H: "H = (hs, ks)" by fastforce
  obtain Ha Pa Ka Sr where Hi: "Hi = (Ha, Pa, Ka, Sr)" by (cases Hi) auto
  have "x \<notin> set hs" using 5(3) H by auto
  thus ?case unfolding H Hi by (rule heap_insert_imp_rule[OF 5(1)[unfolded H] 5(2)])
next
  case (6 H x k' k Hi)
  obtain hs ks where H: "H = (hs, ks)" by fastforce
  obtain Ha Pa Ka Sr where Hi: "Hi = (Ha, Pa, Ka, Sr)" by (cases Hi) auto
  have "x \<in> set hs" using 6(3) H by auto
  thus ?case unfolding H Hi by (rule heap_decrease_key_imp_rule[OF 6(1)[unfolded H]])
qed


end
end