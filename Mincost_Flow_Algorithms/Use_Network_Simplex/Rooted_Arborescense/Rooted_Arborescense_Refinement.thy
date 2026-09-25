theory Rooted_Arborescense_Refinement
  imports Rooted_Arborescense 
Separation_Logic_Imperative_HOL_Partial.Array_Blit
begin

record  ndtree_impl =
  prnt_impl :: "nat array"   \<comment> \<open>tree parent map\<close>
  thrd_impl :: "nat array"   \<comment> \<open>thread successor (preorder next)\<close>
  rvth_impl :: "nat array"    \<comment> \<open>thread predecessor (reverse thread)\<close>
  lsuc_impl :: "nat array"     \<comment> \<open>last successor: rightmost descendant of the subtree in the thread\<close>
  snum_impl :: "nat array"    \<comment> \<open>subtree size (number of successors, incl. the node itself)\<close>
  aux_impl :: "nat array"
subsection \<open>Imperative implementations over @{typ ndtree_impl}\<close>

text \<open>Each abstract map read @{term "prnt T v"} becomes an array read; @{term None} is encoded as
      @{term 0} and any @{term "Some u"} as @{term u} (the tree contains no @{term 0} vertex).  The
      loops mutate the arrays of @{term Ti} in place, so the record of array handles is threaded
      unchanged.  The functional dirty list @{text drt} is realised by the auxiliary array
      @{const aux_impl} together with a fill pointer @{text sp} (its current length): @{text stem_loop_imp}
      writes @{term j} to @{term "aux_impl Ti"} at index @{term 0} beforehand and pushes at index
      @{text sp}, then @{text dirty_pass_imp} sweeps indices @{term 0} to @{text sp} in the same order.\<close>

text \<open>Stem loop: reverse parents / re-thread from @{term stm} up to @{term p}; @{text sp} is the number
      of dirty entries already pushed into @{const aux_impl}.  Returns the new parent @{text pstm} of
      @{term p}, its last successor @{text lsx}, the trailing thread node @{text aft} (@{term 0} = none)
      and the final dirty count.\<close>
partial_function (heap) stem_loop_imp ::
  "ndtree_impl \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat) Heap" where
  "stem_loop_imp Ti stm pstm lsx aft sp p =
     (if stm = p then return (pstm, lsx, aft, sp)
      else do {
        nxt_stm \<leftarrow> Array.nth (prnt_impl Ti) stm;
        _ \<leftarrow> Array.upd lsx nxt_stm (thrd_impl Ti);
        _ \<leftarrow> Array.upd sp lsx (aux_impl Ti);
        bef \<leftarrow> Array.nth (rvth_impl Ti) stm;
        _ \<leftarrow> (if aft = 0
               then do { _ \<leftarrow> Array.upd bef 0 (thrd_impl Ti); return () }
               else do { _ \<leftarrow> Array.upd bef aft (thrd_impl Ti);
                         _ \<leftarrow> Array.upd aft bef (rvth_impl Ti); return () });
        _ \<leftarrow> Array.upd stm pstm (prnt_impl Ti);
        ls_stm \<leftarrow> Array.nth (lsuc_impl Ti) nxt_stm;
        ls_pstm \<leftarrow> Array.nth (lsuc_impl Ti) stm;
        lsx' \<leftarrow> (if ls_stm = ls_pstm then Array.nth (rvth_impl Ti) stm else return ls_stm);
        aft' \<leftarrow> Array.nth (thrd_impl Ti) lsx';
        stem_loop_imp Ti nxt_stm stm lsx' aft' (sp + 1) p
      })"

text \<open>Refresh the deferred reverse-thread links recorded in @{const aux_impl}, indices @{term k} to
      @{text sp}, in ascending (insertion) order.\<close>
partial_function (heap) dirty_pass_imp ::
  "ndtree_impl \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "dirty_pass_imp Ti k sp =
     (if sp \<le> k then return ()
      else do {
        u \<leftarrow> Array.nth (aux_impl Ti) k;
        w \<leftarrow> Array.nth (thrd_impl Ti) u;
        _ \<leftarrow> (if w = 0 then return () else do { _ \<leftarrow> Array.upd w u (rvth_impl Ti); return () });
        dirty_pass_imp Ti (k + 1) sp
      })"

text \<open>Recompute @{const snum_impl} and @{const lsuc_impl} for the reversed stem, walking parents from
      @{term p} down to @{term iv}.  No @{text sn0} snapshot is needed: for each node the original
      @{const snum} of the node and of its parent are read before @{const snum} is written there, and
      those cells are never overwritten by an earlier iteration.\<close>
partial_function (heap) stem_num_loop_imp ::
  "ndtree_impl \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "stem_num_loop_imp Ti u iv acc tls =
     (if u = iv then return ()
      else do {
        par \<leftarrow> Array.nth (prnt_impl Ti) u;
        (if par = 0 then return ()
         else do {
           snu \<leftarrow> Array.nth (snum_impl Ti) u;
           snpar \<leftarrow> Array.nth (snum_impl Ti) par;
           _ \<leftarrow> Array.upd u (acc + (snu - snpar)) (snum_impl Ti);
           _ \<leftarrow> Array.upd par tls (lsuc_impl Ti);
           stem_num_loop_imp Ti par iv (acc + (snu - snpar)) tls
         })
      })"

text \<open>Fused @{term j}-side pass: one walk from @{term u} extending @{const lsuc} while
      @{term "la \<and> lsuc u = jv"} and adding @{term d} to @{const snum} while @{term "sa \<and> u \<noteq> jn"}.\<close>
partial_function (heap) fused_vin_loop_imp ::
  "ndtree_impl \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> unit Heap" where
  "fused_vin_loop_imp Ti u jv jn lso d la sa =
     do {
        lsu \<leftarrow> Array.nth (lsuc_impl Ti) u;
        (if \<not> (la \<and> lsu = jv) \<and> \<not> (sa \<and> u \<noteq> jn) then return ()
         else do {
           _ \<leftarrow> (if la \<and> lsu = jv then do { _ \<leftarrow> Array.upd u lso (lsuc_impl Ti); return () } else return ());
           _ \<leftarrow> (if sa \<and> u \<noteq> jn
                  then do { snu \<leftarrow> Array.nth (snum_impl Ti) u; _ \<leftarrow> Array.upd u (snu + d) (snum_impl Ti); return () }
                  else return ());
           par \<leftarrow> Array.nth (prnt_impl Ti) u;
           (if par = 0 then return ()
            else fused_vin_loop_imp Ti par jv jn lso d (la \<and> lsu = jv) (sa \<and> u \<noteq> jn))
         })
      }"

text \<open>Fused @{term v_out}-side pass: one walk from @{term u} resetting @{const lsuc} while
      @{term "la \<and> u \<noteq> stp \<and> lsuc u = gv"} (encoded stop @{term stp}, @{term 0} = none) and subtracting
      @{term d} from @{const snum} while @{term "sa \<and> u \<noteq> jn"}.\<close>
partial_function (heap) fused_vout_loop_imp ::
  "ndtree_impl \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> unit Heap" where
  "fused_vout_loop_imp Ti u stp gv sv jn d la sa =
     do {
        lsu \<leftarrow> Array.nth (lsuc_impl Ti) u;
        (if \<not> (la \<and> u \<noteq> stp \<and> lsu = gv) \<and> \<not> (sa \<and> u \<noteq> jn) then return ()
         else do {
           _ \<leftarrow> (if la \<and> u \<noteq> stp \<and> lsu = gv then do { _ \<leftarrow> Array.upd u sv (lsuc_impl Ti); return () } else return ());
           _ \<leftarrow> (if sa \<and> u \<noteq> jn
                  then do { snu \<leftarrow> Array.nth (snum_impl Ti) u; _ \<leftarrow> Array.upd u (snu - d) (snum_impl Ti); return () }
                  else return ());
           par \<leftarrow> Array.nth (prnt_impl Ti) u;
           (if par = 0 then return ()
            else fused_vout_loop_imp Ti par stp gv sv jn d (la \<and> u \<noteq> stp \<and> lsu = gv) (sa \<and> u \<noteq> jn))
         })
      }"

text \<open>The orchestrator (imperative port of @{const update_tree}).  The @{typ ndtree_impl} arrays of
      @{term Ti} are mutated in place to realise @{term "update_tree S0 i j p jn"}.\<close>
definition update_tree_imp :: "ndtree_impl \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "update_tree_imp Ti i j p jn =
     do {
        v_out \<leftarrow> Array.nth (prnt_impl Ti) p;
        old_rev \<leftarrow> Array.nth (rvth_impl Ti) p;
        old_num \<leftarrow> Array.nth (snum_impl Ti) p;
        old_last \<leftarrow> Array.nth (lsuc_impl Ti) p;
        \<comment> \<open>--- restructure the thread / parent pointers (build S1 in place) ---\<close>
        _ \<leftarrow> (if i = p
         then do {
           _ \<leftarrow> Array.upd i j (prnt_impl Ti);
           tj \<leftarrow> Array.nth (thrd_impl Ti) j;
           (if tj = p then return ()
            else do {
              aft1 \<leftarrow> Array.nth (thrd_impl Ti) old_last;
              _ \<leftarrow> (if aft1 = 0 then do { _ \<leftarrow> Array.upd old_rev 0 (thrd_impl Ti); return () }
                     else do { _ \<leftarrow> Array.upd old_rev aft1 (thrd_impl Ti);
                               _ \<leftarrow> Array.upd aft1 old_rev (rvth_impl Ti); return () });
              aft2 \<leftarrow> Array.nth (thrd_impl Ti) j;
              _ \<leftarrow> Array.upd j p (thrd_impl Ti);
              _ \<leftarrow> Array.upd p j (rvth_impl Ti);
              (if aft2 = 0 then do { _ \<leftarrow> Array.upd old_last 0 (thrd_impl Ti); return () }
               else do { _ \<leftarrow> Array.upd old_last aft2 (thrd_impl Ti);
                         _ \<leftarrow> Array.upd aft2 old_last (rvth_impl Ti); return () })
            })
         }
         else do {
           thread_cont \<leftarrow> (if old_rev = j then Array.nth (thrd_impl Ti) old_last else Array.nth (thrd_impl Ti) j);
           lsx0 \<leftarrow> Array.nth (lsuc_impl Ti) i;
           aft0 \<leftarrow> Array.nth (thrd_impl Ti) lsx0;
           _ \<leftarrow> Array.upd j i (thrd_impl Ti);
           _ \<leftarrow> Array.upd 0 j (aux_impl Ti);
           r \<leftarrow> stem_loop_imp Ti i j lsx0 aft0 1 p;
           (case r of (pstm, lsx, aft, sp) \<Rightarrow> do {
              _ \<leftarrow> Array.upd p pstm (prnt_impl Ti);
              _ \<leftarrow> (if thread_cont = 0 then do { _ \<leftarrow> Array.upd lsx 0 (thrd_impl Ti); return () }
                     else do { _ \<leftarrow> Array.upd lsx thread_cont (thrd_impl Ti);
                               _ \<leftarrow> Array.upd thread_cont lsx (rvth_impl Ti); return () });
              _ \<leftarrow> Array.upd p lsx (lsuc_impl Ti);
              _ \<leftarrow> (if old_rev \<noteq> j
                     then (if aft = 0 then do { _ \<leftarrow> Array.upd old_rev 0 (thrd_impl Ti); return () }
                           else do { _ \<leftarrow> Array.upd old_rev aft (thrd_impl Ti);
                                     _ \<leftarrow> Array.upd aft old_rev (rvth_impl Ti); return () })
                     else return ());
              _ \<leftarrow> dirty_pass_imp Ti 0 sp;
              tls \<leftarrow> Array.nth (lsuc_impl Ti) p;
              _ \<leftarrow> stem_num_loop_imp Ti p i 0 tls;
              _ \<leftarrow> Array.upd i old_num (snum_impl Ti);
              return ()
           })
         });
        \<comment> \<open>--- fix lsuc and snum along the branches up to the join (fused passes) ---\<close>
        ls_jn \<leftarrow> Array.nth (lsuc_impl Ti) jn;
        last_out \<leftarrow> Array.nth (lsuc_impl Ti) p;
        up_limit \<leftarrow> return (if ls_jn = j then jn else 0);
        _ \<leftarrow> fused_vin_loop_imp Ti j j jn last_out old_num True True;
        (if jn \<noteq> old_rev \<and> j \<noteq> old_rev
         then fused_vout_loop_imp Ti v_out up_limit old_last old_rev jn old_num True True
         else if last_out \<noteq> old_last
              then fused_vout_loop_imp Ti v_out up_limit old_last last_out jn old_num True True
              else fused_vout_loop_imp Ti v_out up_limit old_last old_last jn old_num False True)
      }"

definition ndtree_assn :: "nat set \<Rightarrow> nat ndtree \<Rightarrow> ndtree_impl \<Rightarrow> assn" where
 "ndtree_assn V T Ti =
  (\<exists>\<^sub>A prnt_list thrd_list rvth_list lsuc_list snum_list aux_list.
      prnt_impl Ti \<mapsto>\<^sub>a prnt_list *
      thrd_impl Ti \<mapsto>\<^sub>a thrd_list *
      rvth_impl Ti \<mapsto>\<^sub>a rvth_list *
      lsuc_impl Ti \<mapsto>\<^sub>a lsuc_list *
      snum_impl Ti \<mapsto>\<^sub>a snum_list *
      aux_impl Ti \<mapsto>\<^sub>a aux_list *
     \<up> (  0 \<notin> V \<and>
         dom (prnt T) \<subseteq> V \<and> dom (thrd T) \<subseteq> V \<and> dom (rvth T) \<subseteq> V \<and>
         ran (prnt T) \<subseteq> V \<and> ran (thrd T) \<subseteq> V \<and> ran (rvth T) \<subseteq> V \<and>
        V \<subseteq> {0..<length prnt_list} \<and>
        V \<subseteq> {0..<length thrd_list} \<and>
        V \<subseteq> {0..<length rvth_list} \<and>
        V \<subseteq> {0..<length lsuc_list} \<and>
        V \<subseteq> {0..<length snum_list}\<and>
        V \<subseteq> {0..<length aux_list} \<and>
        (\<forall> v \<in> V. (\<forall> u. prnt T v = Some u \<longrightarrow> prnt_list ! v = u) \<and>
              (prnt T v = None \<longrightarrow> prnt_list ! v = 0)) \<and>
        (\<forall> v \<in> V. (\<forall> u. thrd T v = Some u \<longrightarrow> thrd_list ! v = u) \<and>
              (thrd T v = None \<longrightarrow> thrd_list ! v = 0)) \<and>
        (\<forall> v \<in> V. (\<forall> u. rvth T v = Some u \<longrightarrow> rvth_list ! v = u) \<and>
              (rvth T v = None \<longrightarrow> rvth_list ! v = 0)) \<and>
        (\<forall> v \<in> V. lsuc T v \<in> V) \<and>
        (\<forall> v \<in> V. lsuc T v = lsuc_list ! v \<and>
                   snum T v = snum_list ! v)
        )
        )
        "

subsection \<open>The pure refinement relation and its consistency lemmas\<close>

text \<open>Encoding of a partial map as an array cell: @{term 0} is @{term None}, any other @{term n} is
      @{term "Some n"}.\<close>
definition opt_of_nat :: "nat \<Rightarrow> nat option" where
  "opt_of_nat n = (if n = 0 then None else Some n)"

definition nat_of_opt :: "nat option \<Rightarrow> nat" where
  "nat_of_opt x = (case x of None \<Rightarrow> 0 | Some u \<Rightarrow> u)"

lemma nat_of_opt_simps[simp]:
  "nat_of_opt None = 0" "nat_of_opt (Some u) = u"
  by (simp_all add: nat_of_opt_def)

lemma opt_of_nat_simps[simp]:
  "opt_of_nat 0 = None" "n \<noteq> 0 \<Longrightarrow> opt_of_nat n = Some n"
  by (simp_all add: opt_of_nat_def)

text \<open>The pure part of @{const ndtree_assn}: the abstract tree @{term T} agrees with the six lists on
      the vertex set @{term V}.  Factoring it out lets us reason about domains, ranges, in-bounds and
      the read/write correspondences without unfolding the whole assertion.\<close>
definition ndtree_rel ::
  "nat set \<Rightarrow> nat ndtree \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool"
  where
  "ndtree_rel V T pl thl rl ll sl al \<longleftrightarrow>
     0 \<notin> V \<and>
     dom (prnt T) \<subseteq> V \<and> dom (thrd T) \<subseteq> V \<and> dom (rvth T) \<subseteq> V \<and>
     ran (prnt T) \<subseteq> V \<and> ran (thrd T) \<subseteq> V \<and> ran (rvth T) \<subseteq> V \<and>
     V \<subseteq> {0..<length pl} \<and> V \<subseteq> {0..<length thl} \<and> V \<subseteq> {0..<length rl} \<and>
     V \<subseteq> {0..<length ll} \<and> V \<subseteq> {0..<length sl} \<and> V \<subseteq> {0..<length al} \<and>
     (\<forall>v\<in>V. (\<forall>u. prnt T v = Some u \<longrightarrow> pl ! v = u) \<and> (prnt T v = None \<longrightarrow> pl ! v = 0)) \<and>
     (\<forall>v\<in>V. (\<forall>u. thrd T v = Some u \<longrightarrow> thl ! v = u) \<and> (thrd T v = None \<longrightarrow> thl ! v = 0)) \<and>
     (\<forall>v\<in>V. (\<forall>u. rvth T v = Some u \<longrightarrow> rl ! v = u) \<and> (rvth T v = None \<longrightarrow> rl ! v = 0)) \<and>
     (\<forall>v\<in>V. lsuc T v \<in> V) \<and>
     (\<forall>v\<in>V. lsuc T v = ll ! v \<and> snum T v = sl ! v)"

lemma ndtree_assn_unfold:
  "ndtree_assn V T Ti =
   (\<exists>\<^sub>A pl thl rl ll sl al.
      prnt_impl Ti \<mapsto>\<^sub>a pl * thrd_impl Ti \<mapsto>\<^sub>a thl * rvth_impl Ti \<mapsto>\<^sub>a rl *
      lsuc_impl Ti \<mapsto>\<^sub>a ll * snum_impl Ti \<mapsto>\<^sub>a sl * aux_impl Ti \<mapsto>\<^sub>a al *
      \<up> (ndtree_rel V T pl thl rl ll sl al))"
  by (simp add: ndtree_assn_def ndtree_rel_def)

text \<open>Generic read correspondence for an option-array pair under the @{term 0}-is-@{term None} encoding.\<close>
lemma opt_list_read:
  assumes "v \<in> V"
    and "\<forall>v\<in>V. (\<forall>u. m v = Some u \<longrightarrow> xs ! v = u) \<and> (m v = None \<longrightarrow> xs ! v = 0)"
  shows "xs ! v = (case m v of None \<Rightarrow> 0 | Some u \<Rightarrow> u)"
  using assms by (cases "m v") auto

text \<open>The encoding is invertible when the range avoids @{term 0}: a stored @{term 0} means @{term None}.\<close>
lemma opt_list_zero_iff:
  assumes "0 \<notin> V" "v \<in> V" "ran m \<subseteq> V"
    and "\<forall>v\<in>V. (\<forall>u. m v = Some u \<longrightarrow> xs ! v = u) \<and> (m v = None \<longrightarrow> xs ! v = 0)"
  shows "(xs ! v = 0) = (m v = None)"
proof (cases "m v")
  case None thus ?thesis using assms(2,4) by auto
next
  case (Some u)
  from Some assms(2,4) have "xs ! v = u" by auto
  moreover from Some assms(3) have "u \<in> V" using ranI by fastforce
  ultimately show ?thesis using Some assms(1) by fastforce
qed

subsubsection \<open>Domains, ranges and the no-zero invariant\<close>

lemma ndtree_rel_0_notin: 
"ndtree_rel V T pl thl rl ll sl al \<Longrightarrow> 0 \<notin> V"
  by (simp add: ndtree_rel_def)

lemma ndtree_rel_prnt_dom: "ndtree_rel V T pl thl rl ll sl al \<Longrightarrow> dom (prnt T) \<subseteq> V"
  and ndtree_rel_thrd_dom: "ndtree_rel V T pl thl rl ll sl al \<Longrightarrow> dom (thrd T) \<subseteq> V"
  and ndtree_rel_rvth_dom: "ndtree_rel V T pl thl rl ll sl al \<Longrightarrow> dom (rvth T) \<subseteq> V"
  by (simp_all add: ndtree_rel_def)

lemma ndtree_rel_prnt_ranI:
  assumes "ndtree_rel V T pl thl rl ll sl al" "prnt T v = Some u" shows "u \<in> V"
proof -
  have "ran (prnt T) \<subseteq> V" using assms(1) by (simp add: ndtree_rel_def)
  moreover have "u \<in> ran (prnt T)" unfolding ran_def using assms(2) by blast
  ultimately show ?thesis by blast
qed

lemma ndtree_rel_thrd_ranI:
  assumes "ndtree_rel V T pl thl rl ll sl al" "thrd T v = Some u" shows "u \<in> V"
proof -
  have "ran (thrd T) \<subseteq> V" using assms(1) by (simp add: ndtree_rel_def)
  moreover have "u \<in> ran (thrd T)" unfolding ran_def using assms(2) by blast
  ultimately show ?thesis by blast
qed

lemma ndtree_rel_rvth_ranI:
  assumes "ndtree_rel V T pl thl rl ll sl al" "rvth T v = Some u" shows "u \<in> V"
proof -
  have "ran (rvth T) \<subseteq> V" using assms(1) by (simp add: ndtree_rel_def)
  moreover have "u \<in> ran (rvth T)" unfolding ran_def using assms(2) by blast
  ultimately show ?thesis by blast
qed

lemma ndtree_rel_lsuc_V:
 "ndtree_rel V T pl thl rl ll sl al \<Longrightarrow> v \<in> V \<Longrightarrow> lsuc T v \<in> V"
  unfolding ndtree_rel_def by blast

subsubsection \<open>In-bounds facts for the six arrays\<close>

lemma ndtree_rel_len_prnt:
  assumes "ndtree_rel V T pl thl rl ll sl al" "v \<in> V" shows "v < length pl"
proof -
  have "V \<subseteq> {0..<length pl}" using assms(1) by (simp add: ndtree_rel_def)
  thus ?thesis using assms(2) by fastforce
qed

lemma ndtree_rel_len_thrd:
  assumes "ndtree_rel V T pl thl rl ll sl al" "v \<in> V" shows "v < length thl"
proof -
  have "V \<subseteq> {0..<length thl}" using assms(1) by (simp add: ndtree_rel_def)
  thus ?thesis using assms(2) by fastforce
qed

lemma ndtree_rel_len_rvth:
  assumes "ndtree_rel V T pl thl rl ll sl al" "v \<in> V" shows "v < length rl"
proof -
  have "V \<subseteq> {0..<length rl}" using assms(1) by (simp add: ndtree_rel_def)
  thus ?thesis using assms(2) by fastforce
qed

lemma ndtree_rel_len_lsuc:
  assumes "ndtree_rel V T pl thl rl ll sl al" "v \<in> V" shows "v < length ll"
proof -
  have "V \<subseteq> {0..<length ll}" using assms(1) by (simp add: ndtree_rel_def)
  thus ?thesis using assms(2) by fastforce
qed

lemma ndtree_rel_len_snum:
  assumes "ndtree_rel V T pl thl rl ll sl al" "v \<in> V" shows "v < length sl"
proof -
  have "V \<subseteq> {0..<length sl}" using assms(1) by (simp add: ndtree_rel_def)
  thus ?thesis using assms(2) by fastforce
qed

lemma ndtree_rel_len_aux:
  assumes "ndtree_rel V T pl thl rl ll sl al" "v \<in> V" shows "v < length al"
proof -
  have "V \<subseteq> {0..<length al}" using assms(1) by (simp add: ndtree_rel_def)
  thus ?thesis using assms(2) by fastforce
qed

subsubsection \<open>Read correspondences between the maps and their arrays\<close>

lemma ndtree_rel_prnt_read:
  "ndtree_rel V T pl thl rl ll sl al \<Longrightarrow> v \<in> V \<Longrightarrow> pl ! v = (case prnt T v of None \<Rightarrow> 0 | Some u \<Rightarrow> u)"
  by (intro opt_list_read) (auto simp: ndtree_rel_def)

lemma ndtree_rel_thrd_read:
  "ndtree_rel V T pl thl rl ll sl al \<Longrightarrow> v \<in> V \<Longrightarrow> thl ! v = (case thrd T v of None \<Rightarrow> 0 | Some u \<Rightarrow> u)"
  by (intro opt_list_read) (auto simp: ndtree_rel_def)

lemma ndtree_rel_rvth_read:
  "ndtree_rel V T pl thl rl ll sl al \<Longrightarrow> v \<in> V \<Longrightarrow> rl ! v = (case rvth T v of None \<Rightarrow> 0 | Some u \<Rightarrow> u)"
  by (intro opt_list_read) (auto simp: ndtree_rel_def)

lemma ndtree_rel_prnt_zero_iff:
  "ndtree_rel V T pl thl rl ll sl al \<Longrightarrow> v \<in> V \<Longrightarrow> (pl ! v = 0) = (prnt T v = None)"
  by (intro opt_list_zero_iff) (auto simp: ndtree_rel_def)

lemma ndtree_rel_thrd_zero_iff:
  "ndtree_rel V T pl thl rl ll sl al \<Longrightarrow> v \<in> V \<Longrightarrow> (thl ! v = 0) = (thrd T v = None)"
  by (intro opt_list_zero_iff) (auto simp: ndtree_rel_def)

lemma ndtree_rel_rvth_zero_iff:
  "ndtree_rel V T pl thl rl ll sl al \<Longrightarrow> v \<in> V \<Longrightarrow> (rl ! v = 0) = (rvth T v = None)"
  by (intro opt_list_zero_iff) (auto simp: ndtree_rel_def)

text \<open>Combined: the array cell equals @{term "nat_of_opt"} of the abstract map value.\<close>
lemma ndtree_rel_prnt_nat_of_opt:
  "ndtree_rel V T pl thl rl ll sl al \<Longrightarrow> v \<in> V \<Longrightarrow> pl ! v = nat_of_opt (prnt T v)"
  by (simp add: ndtree_rel_prnt_read nat_of_opt_def)

lemma ndtree_rel_thrd_nat_of_opt:
  "ndtree_rel V T pl thl rl ll sl al \<Longrightarrow> v \<in> V \<Longrightarrow> thl ! v = nat_of_opt (thrd T v)"
  by (simp add: ndtree_rel_thrd_read nat_of_opt_def)

lemma ndtree_rel_rvth_nat_of_opt:
  "ndtree_rel V T pl thl rl ll sl al \<Longrightarrow> v \<in> V \<Longrightarrow> rl ! v = nat_of_opt (rvth T v)"
  by (simp add: ndtree_rel_rvth_read nat_of_opt_def)

lemma ndtree_rel_lsuc: "ndtree_rel V T pl thl rl ll sl al \<Longrightarrow> v \<in> V \<Longrightarrow> ll ! v = lsuc T v"
  and ndtree_rel_snum: "ndtree_rel V T pl thl rl ll sl al \<Longrightarrow> v \<in> V \<Longrightarrow> sl ! v = snum T v"
  by (auto simp: ndtree_rel_def)

text \<open>The extended assertion used to couple @{text stem_loop_imp} with @{text dirty_pass_imp}: as
      @{const ndtree_assn}, but additionally the first @{text sp} cells of the auxiliary array hold the
      functional dirty list @{term xs}.  Weakening forgets that extra knowledge.\<close>
definition ndtree_drt_assn ::
  "nat set \<Rightarrow> nat ndtree \<Rightarrow> ndtree_impl \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> assn" where
  "ndtree_drt_assn V T Ti sp xs =
     (\<exists>\<^sub>A pl thl rl ll sl al.
        prnt_impl Ti \<mapsto>\<^sub>a pl * thrd_impl Ti \<mapsto>\<^sub>a thl * rvth_impl Ti \<mapsto>\<^sub>a rl *
        lsuc_impl Ti \<mapsto>\<^sub>a ll * snum_impl Ti \<mapsto>\<^sub>a sl * aux_impl Ti \<mapsto>\<^sub>a al *
        \<up> (ndtree_rel V T pl thl rl ll sl al \<and>
           sp = length xs \<and> length xs \<le> length al \<and> take (length xs) al = xs))"

lemma ndtree_drt_assn_weaken:
  "ndtree_drt_assn V T Ti sp xs \<Longrightarrow>\<^sub>A ndtree_assn V T Ti"
  unfolding ndtree_drt_assn_def ndtree_assn_unfold by sep_auto

subsection \<open>Primitive array operations preserve the refinement\<close>

text \<open>Pure invariant preservation for a single @{const lsuc} / @{const snum} cell update.\<close>
lemma ndtree_rel_upd_lsuc:
  assumes A: "ndtree_rel V S pl thl rl ll sl al" and u: "u \<in> V" and x: "x \<in> V"
  shows "ndtree_rel V (S\<lparr>lsuc := (lsuc S)(u := x)\<rparr>) pl thl rl (ll[u := x]) sl al"
proof -
  have ul: "u < length ll" using A u by (rule ndtree_rel_len_lsuc)
  show ?thesis using A u x ul unfolding ndtree_rel_def by (auto simp: nth_list_update)
qed

lemma ndtree_rel_upd_snum:
  assumes A: "ndtree_rel V S pl thl rl ll sl al" and u: "u \<in> V"
  shows "ndtree_rel V (S\<lparr>snum := (snum S)(u := x)\<rparr>) pl thl rl ll (sl[u := x]) al"
proof -
  have ul: "u < length sl" using A u by (rule ndtree_rel_len_snum)
  show ?thesis using A u ul unfolding ndtree_rel_def by (auto simp: nth_list_update)
qed

text \<open>Reading a cell returns the abstract value (option-valued maps decoded via @{const nat_of_opt}).\<close>
lemma ndtree_nth_prnt[sep_heap_rules]:
  "u \<in> V \<Longrightarrow> <ndtree_assn V S Ti> Array.nth (prnt_impl Ti) u
     <\<lambda>r. ndtree_assn V S Ti * \<up> (r = nat_of_opt (prnt S u))>"
  unfolding ndtree_assn_unfold
  by (sep_auto simp: ndtree_rel_len_prnt ndtree_rel_prnt_nat_of_opt)

lemma ndtree_nth_lsuc[sep_heap_rules]:
  "u \<in> V \<Longrightarrow> <ndtree_assn V S Ti> Array.nth (lsuc_impl Ti) u
     <\<lambda>r. ndtree_assn V S Ti * \<up> (r = lsuc S u)>"
  unfolding ndtree_assn_unfold
  by (sep_auto simp: ndtree_rel_len_lsuc ndtree_rel_lsuc)

lemma ndtree_nth_snum[sep_heap_rules]:
  "u \<in> V \<Longrightarrow> <ndtree_assn V S Ti> Array.nth (snum_impl Ti) u
     <\<lambda>r. ndtree_assn V S Ti * \<up> (r = snum S u)>"
  unfolding ndtree_assn_unfold
  by (sep_auto simp: ndtree_rel_len_snum ndtree_rel_snum)

text \<open>Writing a @{const lsuc} / @{const snum} cell yields the assertion for the point-updated tree.\<close>
lemma ndtree_upd_lsuc[sep_heap_rules]:
  "u \<in> V \<Longrightarrow> x \<in> V \<Longrightarrow> <ndtree_assn V S Ti> Array.upd u x (lsuc_impl Ti)
     <\<lambda>_. ndtree_assn V (S\<lparr>lsuc := (lsuc S)(u := x)\<rparr>) Ti>"
  unfolding ndtree_assn_unfold
  by (sep_auto simp: ndtree_rel_len_lsuc ndtree_rel_upd_lsuc)

lemma ndtree_upd_snum[sep_heap_rules]:
  "u \<in> V \<Longrightarrow> <ndtree_assn V S Ti> Array.upd u x (snum_impl Ti)
     <\<lambda>_. ndtree_assn V (S\<lparr>snum := (snum S)(u := x)\<rparr>) Ti>"
  unfolding ndtree_assn_unfold
  by (sep_auto simp: ndtree_rel_len_snum ndtree_rel_upd_snum)

text \<open>Conditional single-cell updates, matching the @{text "if c then \<dots> else return ()"} shape of the
      fused loops: they collapse the branch into one record update so the loop invariant stays folded.\<close>
lemma ndtree_cond_upd_lsuc[sep_heap_rules]:
  "u \<in> V \<Longrightarrow> x \<in> V \<Longrightarrow>
   <ndtree_assn V S Ti> (if c then Array.upd u x (lsuc_impl Ti) \<bind> (\<lambda>_. return ()) else return ())
   <\<lambda>_. ndtree_assn V (S\<lparr>lsuc := (if c then (lsuc S)(u := x) else lsuc S)\<rparr>) Ti>"
  by (cases c) (sep_auto simp: fun_upd_idem)+

lemma ndtree_cond_upd_snum[sep_heap_rules]:
  "u \<in> V \<Longrightarrow>
   <ndtree_assn V S Ti> (if c then Array.nth (snum_impl Ti) u \<bind> (\<lambda>snu. Array.upd u (snu + d) (snum_impl Ti) \<bind> (\<lambda>_. return ())) else return ())
   <\<lambda>_. ndtree_assn V (S\<lparr>snum := (if c then (snum S)(u := snum S u + d) else snum S)\<rparr>) Ti>"
  by (cases c) (sep_auto simp: fun_upd_idem)+

text \<open>Updating a reverse-thread cell (partial-map,  "w \<mapsto> u"); needs @{term "w \<in> V"} (domain)
      and @{term "u \<in> V"} (range, so the @{term 0}-encoding stays faithful).\<close>
lemma ndtree_rel_upd_rvth:
  assumes A: "ndtree_rel V S pl thl rl ll sl al" and w: "w \<in> V" and u: "u \<in> V"
  shows "ndtree_rel V (S\<lparr>rvth := (rvth S)(w \<mapsto> u)\<rparr>) pl thl (rl[w := u]) ll sl al"
proof -
  have wl: "w < length rl" using A w by (rule ndtree_rel_len_rvth)
  have ranr: "ran ((rvth S)(w \<mapsto> u)) \<subseteq> V"
  proof
    fix y assume "y \<in> ran ((rvth S)(w \<mapsto> u))"
    then obtain v where "((rvth S)(w \<mapsto> u)) v = Some y" by (auto simp: ran_def)
    thus "y \<in> V" using A u by (cases "v = w") (auto simp: ndtree_rel_def ran_def split: if_splits)
  qed
  show ?thesis using A w u wl ranr unfolding ndtree_rel_def by (auto simp: nth_list_update)
qed

subsection \<open>Primitive operations on the dirty-list assertion @{const ndtree_drt_assn}\<close>

lemma take_nth_eq: "take n xs = ys \<Longrightarrow> k < n \<Longrightarrow> xs ! k = ys ! k"
  by (metis nth_take)

lemma ndtree_drt_nth_aux[sep_heap_rules]:
  "k < length drt \<Longrightarrow> <ndtree_drt_assn V S Ti sp drt> Array.nth (aux_impl Ti) k
     <\<lambda>r. ndtree_drt_assn V S Ti sp drt * \<up>(r = drt ! k)>"
  unfolding ndtree_drt_assn_def by (sep_auto dest: take_nth_eq)

lemma ndtree_drt_nth_thrd[sep_heap_rules]:
  "u \<in> V \<Longrightarrow> <ndtree_drt_assn V S Ti sp drt> Array.nth (thrd_impl Ti) u
     <\<lambda>r. ndtree_drt_assn V S Ti sp drt * \<up>(r = nat_of_opt (thrd S u))>"
  unfolding ndtree_drt_assn_def by (sep_auto simp: ndtree_rel_len_thrd ndtree_rel_thrd_nat_of_opt)

lemma ndtree_drt_upd_rvth[sep_heap_rules]:
  "w \<in> V \<Longrightarrow> u \<in> V \<Longrightarrow> <ndtree_drt_assn V S Ti sp drt> Array.upd w u (rvth_impl Ti)
     <\<lambda>_. ndtree_drt_assn V (S\<lparr>rvth := (rvth S)(w \<mapsto> u)\<rparr>) Ti sp drt>"
  unfolding ndtree_drt_assn_def by (sep_auto simp: ndtree_rel_len_rvth ndtree_rel_upd_rvth)

text \<open>Pure invariant preservation for @{const thrd} / @{const prnt} cell updates (partial maps), used
      by the thread-surgery loop @{const stem_loop_imp}.\<close>
lemma ndtree_rel_upd_thrd_Some:
  assumes A: "ndtree_rel V S pl thl rl ll sl al" and w: "w \<in> V" and u: "u \<in> V"
  shows "ndtree_rel V (S\<lparr>thrd := (thrd S)(w \<mapsto> u)\<rparr>) pl (thl[w := u]) rl ll sl al"
proof -
  have wl: "w < length thl" using A w by (rule ndtree_rel_len_thrd)
  have ranr: "ran ((thrd S)(w \<mapsto> u)) \<subseteq> V"
  proof
    fix y assume "y \<in> ran ((thrd S)(w \<mapsto> u))"
    then obtain v where "((thrd S)(w \<mapsto> u)) v = Some y" by (auto simp: ran_def)
    thus "y \<in> V" using A u by (cases "v = w") (auto simp: ndtree_rel_def ran_def split: if_splits)
  qed
  show ?thesis using A w u wl ranr unfolding ndtree_rel_def by (auto simp: nth_list_update)
qed

lemma ndtree_rel_upd_thrd_None:
  assumes A: "ndtree_rel V S pl thl rl ll sl al" and w: "w \<in> V"
  shows "ndtree_rel V (S\<lparr>thrd := (thrd S)(w := None)\<rparr>) pl (thl[w := 0]) rl ll sl al"
proof -
  have wl: "w < length thl" using A w by (rule ndtree_rel_len_thrd)
  have ranr: "ran ((thrd S)(w := None)) \<subseteq> V" using A by (auto simp: ndtree_rel_def ran_def)
  show ?thesis using A w wl ranr unfolding ndtree_rel_def by (auto simp: nth_list_update)
qed

lemma ndtree_rel_upd_prnt_Some:
  assumes A: "ndtree_rel V S pl thl rl ll sl al" and w: "w \<in> V" and u: "u \<in> V"
  shows "ndtree_rel V (S\<lparr>prnt := (prnt S)(w \<mapsto> u)\<rparr>) (pl[w := u]) thl rl ll sl al"
proof -
  have wl: "w < length pl" using A w by (rule ndtree_rel_len_prnt)
  have ranr: "ran ((prnt S)(w \<mapsto> u)) \<subseteq> V"
  proof
    fix y assume "y \<in> ran ((prnt S)(w \<mapsto> u))"
    then obtain v where "((prnt S)(w \<mapsto> u)) v = Some y" by (auto simp: ran_def)
    thus "y \<in> V" using A u by (cases "v = w") (auto simp: ndtree_rel_def ran_def split: if_splits)
  qed
  show ?thesis using A w u wl ranr unfolding ndtree_rel_def by (auto simp: nth_list_update)
qed

lemma ndtree_drt_nth_prnt[sep_heap_rules]:
  "u \<in> V \<Longrightarrow> <ndtree_drt_assn V S Ti sp drt> Array.nth (prnt_impl Ti) u
     <\<lambda>r. ndtree_drt_assn V S Ti sp drt * \<up>(r = nat_of_opt (prnt S u))>"
  unfolding ndtree_drt_assn_def by (sep_auto simp: ndtree_rel_len_prnt ndtree_rel_prnt_nat_of_opt)

lemma ndtree_drt_nth_rvth[sep_heap_rules]:
  "u \<in> V \<Longrightarrow> <ndtree_drt_assn V S Ti sp drt> Array.nth (rvth_impl Ti) u
     <\<lambda>r. ndtree_drt_assn V S Ti sp drt * \<up>(r = nat_of_opt (rvth S u))>"
  unfolding ndtree_drt_assn_def by (sep_auto simp: ndtree_rel_len_rvth ndtree_rel_rvth_nat_of_opt)

lemma ndtree_drt_nth_lsuc[sep_heap_rules]:
  "u \<in> V \<Longrightarrow> <ndtree_drt_assn V S Ti sp drt> Array.nth (lsuc_impl Ti) u
     <\<lambda>r. ndtree_drt_assn V S Ti sp drt * \<up>(r = lsuc S u)>"
  unfolding ndtree_drt_assn_def by (sep_auto simp: ndtree_rel_len_lsuc ndtree_rel_lsuc)

lemma ndtree_drt_upd_thrd_Some[sep_heap_rules]:
  "w \<in> V \<Longrightarrow> u \<in> V \<Longrightarrow> <ndtree_drt_assn V S Ti sp drt> Array.upd w u (thrd_impl Ti)
     <\<lambda>_. ndtree_drt_assn V (S\<lparr>thrd := (thrd S)(w \<mapsto> u)\<rparr>) Ti sp drt>"
  unfolding ndtree_drt_assn_def by (sep_auto simp: ndtree_rel_len_thrd ndtree_rel_upd_thrd_Some)

lemma ndtree_drt_upd_thrd_None[sep_heap_rules]:
  "w \<in> V \<Longrightarrow> <ndtree_drt_assn V S Ti sp drt> Array.upd w 0 (thrd_impl Ti)
     <\<lambda>_. ndtree_drt_assn V (S\<lparr>thrd := (thrd S)(w := None)\<rparr>) Ti sp drt>"
  unfolding ndtree_drt_assn_def by (sep_auto simp: ndtree_rel_len_thrd ndtree_rel_upd_thrd_None)

lemma ndtree_drt_upd_prnt_Some[sep_heap_rules]:
  "w \<in> V \<Longrightarrow> u \<in> V \<Longrightarrow> <ndtree_drt_assn V S Ti sp drt> Array.upd w u (prnt_impl Ti)
     <\<lambda>_. ndtree_drt_assn V (S\<lparr>prnt := (prnt S)(w \<mapsto> u)\<rparr>) Ti sp drt>"
  unfolding ndtree_drt_assn_def by (sep_auto simp: ndtree_rel_len_prnt ndtree_rel_upd_prnt_Some)

text \<open>The auxiliary array always has a free slot for the next push: @{term "0 \<notin> V"} wastes index
      @{term 0}, so a distinct list of vertices is strictly shorter than the array.\<close>
lemma drt_push_cap:
  assumes "0 \<notin> V" "V \<subseteq> {0..<n}" "distinct xs" "set xs \<subseteq> V" "xs \<noteq> []"
  shows "length xs < n"
proof -
  have s: "set xs \<subseteq> {Suc 0..<n}"
  proof
    fix x assume "x \<in> set xs"
    hence xV: "x \<in> V" using assms(4) by auto
    have "0 < x" using xV assms(1) by (cases x) auto
    moreover have "x < n" using xV assms(2) by auto
    ultimately show "x \<in> {Suc 0..<n}" by simp
  qed
  have "length xs = card (set xs)" using assms(3) distinct_card by fastforce
  also have "... \<le> card {Suc 0..<n}" using card_mono[OF finite_atLeastLessThan s] .
  also have "... = n - 1" by simp
  finally have le: "length xs \<le> n - 1" .
  have "n \<ge> 1" using s assms(5) by (cases n) auto
  thus ?thesis using le by simp
qed

lemma ndtree_rel_aux_bound: "ndtree_rel V S pl thl rl ll sl al \<Longrightarrow> V \<subseteq> {0..<length al}"
  by (simp add: ndtree_rel_def)

lemma ndtree_rel_drt_cap:
  assumes "ndtree_rel V S pl thl rl ll sl al" "distinct xs" "set xs \<subseteq> V" "xs \<noteq> []"
  shows "length xs < length al"
  by (rule drt_push_cap[OF ndtree_rel_0_notin[OF assms(1)] ndtree_rel_aux_bound[OF assms(1)] assms(2,3,4)])

lemma ndtree_rel_upd_aux[simp]:
  "ndtree_rel V S pl thl rl ll sl (al[i := x]) = ndtree_rel V S pl thl rl ll sl al"
  by (simp add: ndtree_rel_def)

text \<open>Pushing @{term lsx} onto the dirty list: @{const stem_loop_imp} writes @{const aux_impl} at the
      fill pointer @{text "length drt"} and extends the represented list to @{term "drt @ [lsx]"}.\<close>
lemma ndtree_drt_push_aux:
  assumes dd: "distinct drt" and sdV: "set drt \<subseteq> V" and ne: "drt \<noteq> []"
  shows "<ndtree_drt_assn V S Ti (length drt) drt> Array.upd (length drt) lsx (aux_impl Ti)
         <\<lambda>_. ndtree_drt_assn V S Ti (Suc (length drt)) (drt @ [lsx])>"
  unfolding ndtree_drt_assn_def
  by (sep_auto simp: take_Suc_conv_app_nth nth_list_update_eq take_update_cancel ndtree_rel_drt_cap dd sdV ne)

lemma dp_base:
  "<ndtree_drt_assn V S Ti (length pre) pre> dirty_pass_imp Ti (length pre) (length pre) <\<lambda>_. ndtree_assn V S Ti>"
  apply (subst dirty_pass_imp.simps)
  apply simp
  apply (rule ht_cons_pre[OF ndtree_drt_assn_weaken])
  apply sep_auto
  done

text \<open>@{const dirty_pass_imp} from index @{term k} realises the @{const foldl} over @{term "drop k drt"}.\<close>
lemma dirty_pass_imp_aux:
  assumes V0: "0 \<notin> V" and drtV: "set drt \<subseteq> V"
  shows "ran (thrd S) \<subseteq> V \<Longrightarrow> k \<le> length drt \<Longrightarrow>
    <ndtree_drt_assn V S Ti (length drt) drt> dirty_pass_imp Ti k (length drt)
    <\<lambda>_. ndtree_assn V (foldl (\<lambda>S u. case thrd S u of None \<Rightarrow> S | Some w \<Rightarrow> S\<lparr>rvth := (rvth S)(w \<mapsto> u)\<rparr>) S (drop k drt)) Ti>"
proof (induction "length drt - k" arbitrary: k S)
  case 0
  hence keq: "k = length drt" by simp
  show ?case using dp_base[where pre = drt and S = S and Ti = Ti and V = V] keq by simp
next
  case (Suc n)
  have kl: "k < length drt" using Suc.hyps(2) Suc.prems(2) by simp
  have notle: "\<not> length drt \<le> k" using kl by simp
  have dkV: "drt ! k \<in> V" using drtV kl nth_mem by blast
  have dropk: "drop k drt = drt ! k # drop (Suc k) drt" using kl Cons_nth_drop_Suc by metis
  show ?case
  proof (cases "thrd S (drt ! k)")
    case None
    have feqN: "foldl (\<lambda>S u. case thrd S u of None \<Rightarrow> S | Some w \<Rightarrow> S\<lparr>rvth := (rvth S)(w \<mapsto> u)\<rparr>) S (drop k drt) = foldl (\<lambda>S u. case thrd S u of None \<Rightarrow> S | Some w \<Rightarrow> S\<lparr>rvth := (rvth S)(w \<mapsto> u)\<rparr>) S (drop (Suc k) drt)"
      using dropk None by simp
    have IH': "<ndtree_drt_assn V S Ti (length drt) drt> dirty_pass_imp Ti (Suc k) (length drt) <\<lambda>_. ndtree_assn V (foldl (\<lambda>S u. case thrd S u of None \<Rightarrow> S | Some w \<Rightarrow> S\<lparr>rvth := (rvth S)(w \<mapsto> u)\<rparr>) S (drop (Suc k) drt)) Ti>"
      using Suc.hyps(1)[of "Suc k" S] Suc.hyps(2) Suc.prems(1) kl by simp
    show ?thesis unfolding feqN
      apply (subst dirty_pass_imp.simps)
      apply (subst if_not_P[OF notle])
      apply (sep_auto simp: kl dkV None nat_of_opt_def heap: IH')
      done
  next
    case (Some w)
    have wV: "w \<in> V" using Some Suc.prems(1) ranI by fastforce
    have wne: "w \<noteq> 0" using wV V0 by metis
    define S2 where "S2 = S\<lparr>rvth := (rvth S)(w \<mapsto> drt ! k)\<rparr>"
    have thrdS2: "ran (thrd S2) \<subseteq> V" using Suc.prems(1) by (simp add: S2_def)
    have IH': "<ndtree_drt_assn V S2 Ti (length drt) drt> dirty_pass_imp Ti (Suc k) (length drt) <\<lambda>_. ndtree_assn V (foldl (\<lambda>S u. case thrd S u of None \<Rightarrow> S | Some w \<Rightarrow> S\<lparr>rvth := (rvth S)(w \<mapsto> u)\<rparr>) S2 (drop (Suc k) drt)) Ti>"
      using Suc.hyps(1)[of "Suc k" S2] Suc.hyps(2) thrdS2 kl by simp
    have feqS: "foldl (\<lambda>S u. case thrd S u of None \<Rightarrow> S | Some w \<Rightarrow> S\<lparr>rvth := (rvth S)(w \<mapsto> u)\<rparr>) S (drop k drt) = foldl (\<lambda>S u. case thrd S u of None \<Rightarrow> S | Some w \<Rightarrow> S\<lparr>rvth := (rvth S)(w \<mapsto> u)\<rparr>) S2 (drop (Suc k) drt)"
      using dropk Some by (simp add: S2_def)
    show ?thesis unfolding feqS
      apply (subst dirty_pass_imp.simps)
      apply (subst if_not_P[OF notle])
      apply (sep_auto simp: kl dkV Some wV wne nat_of_opt_def S2_def[symmetric] heap: IH')
      done
  qed
qed

subsection \<open>Refinement correspondences (Hoare triples)\<close>

text \<open>Weakened @{const stem_num_loop} refinement (companion to \<open>stem_loop_imp_wf\<close> below): the loop climbs the
      parent chain but mutates only @{const snum}/@{const lsuc}, so instead of the global \<open>prnt S = P\<close>
      it suffices that @{const prnt} of \<open>S\<close> agrees with a well-founded reference \<open>P\<close> on the climb.  This lets
      it be applied to the (possibly globally non-well-founded) reversed tree, using the reversed stem as the
      well-founded reference.\<close>
lemma stem_num_loop_imp_wf:
  assumes ps: "parent_spec P" and ranP: "ran P \<subseteq> V" and V0: "0 \<notin> V"
  shows "(\<forall>w \<in> set (follow P u). w \<noteq> iv \<longrightarrow> prnt S w = P w) \<and> u \<in> V \<and> tls \<in> V \<and> (\<forall>w \<in> set (follow P u). snum S w = sn0 w) \<longrightarrow>
    <ndtree_assn V S Ti> stem_num_loop_imp Ti u iv acc tls
    <\<lambda>_. ndtree_assn V (stem_num_loop S sn0 u iv acc tls) Ti>"
proof (induction arbitrary: S acc rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF ps, of u]])
  case (1 u)
  show ?case
  proof (intro impI, elim conjE)
    assume agr: "\<forall>w \<in> set (follow P u). w \<noteq> iv \<longrightarrow> prnt S w = P w" and uV: "u \<in> V" and tlsV: "tls \<in> V"
       and inv: "\<forall>w \<in> set (follow P u). snum S w = sn0 w"
    have uin: "u \<in> set (follow P u)"
      using follow_ne_ps[OF ps, of u] follow_hd_ps[OF ps, of u] by (cases "follow P u") auto
    show "<ndtree_assn V S Ti> stem_num_loop_imp Ti u iv acc tls <\<lambda>_. ndtree_assn V (stem_num_loop S sn0 u iv acc tls) Ti>"
    proof (cases "u = iv")
      case True
      have f: "stem_num_loop S sn0 u iv acc tls = S" by (subst stem_num_loop.simps) (simp add: True)
      show ?thesis unfolding f using True by (subst stem_num_loop_imp.simps) sep_auto
    next
      case False
      have prntSu: "prnt S u = P u" using agr uin False by blast
      show ?thesis
      proof (cases "P u")
        case None
        have f: "stem_num_loop S sn0 u iv acc tls = S" using None prntSu False by (subst stem_num_loop.simps) simp
        show ?thesis unfolding f
          apply (subst stem_num_loop_imp.simps)
          apply (sep_auto simp: uV prntSu None nat_of_opt_def False)
          done
      next
        case (Some w)
        have wV: "w \<in> V" using ranP Some unfolding ran_def by blast
        have wne: "w \<noteq> 0" using wV V0 by metis
        have fuP: "follow P u = u # follow P w" using Some by (subst follow_ps_simps[OF ps]) simp
        have win: "w \<in> set (follow P u)" using fuP follow_hd_ps[OF ps, of w] follow_ne_ps[OF ps, of w] by (cases "follow P w") auto
        have unotin: "u \<notin> set (follow P w)" using fuP follow_distinct_ps[OF ps, of u] by simp
        have snu: "snum S u = sn0 u" using inv uin by blast
        have snpar: "snum S w = sn0 w" using inv win by blast
        define acc' where "acc' = acc + (sn0 u - sn0 w)"
        define S' where "S' = S\<lparr>snum := (snum S)(u := acc'), lsuc := (lsuc S)(w := tls)\<rparr>"
        have agr': "\<forall>v \<in> set (follow P w). v \<noteq> iv \<longrightarrow> prnt S' v = P v" using agr fuP by (auto simp: S'_def)
        have invS': "\<forall>v \<in> set (follow P w). snum S' v = sn0 v" using inv fuP unotin by (auto simp: S'_def)
        have prntSuw: "prnt S u = Some w" using prntSu Some by simp
        have fu: "stem_num_loop S sn0 u iv acc tls = stem_num_loop S' sn0 w iv acc' tls"
          using False prntSuw by (subst stem_num_loop.simps) (simp add: acc'_def S'_def Let_def)
        have ante: "(\<forall>v \<in> set (follow P w). v \<noteq> iv \<longrightarrow> prnt S' v = P v) \<and> w \<in> V \<and> tls \<in> V \<and> (\<forall>v \<in> set (follow P w). snum S' v = sn0 v)"
          using agr' wV tlsV invS' by blast
        have IHw: "<ndtree_assn V S' Ti> stem_num_loop_imp Ti w iv acc' tls <\<lambda>_. ndtree_assn V (stem_num_loop S' sn0 w iv acc' tls) Ti>"
          by (rule 1(2)[OF Some, THEN mp, OF ante])
        show ?thesis unfolding fu
          apply (subst stem_num_loop_imp.simps)
          apply (sep_auto simp: uV wV tlsV prntSu Some nat_of_opt_def wne False snu snpar acc'_def[symmetric] S'_def[symmetric] heap: IHw)
          done
      qed
    qed
  qed
qed

subsection \<open>Stem-loop, dirty-pass and stem-number-loop refinement\<close>

text \<open>The auxiliary array + fill pointer @{text sp} realise the functional dirty list.  The aux push stays
      in bounds because the number of pushes is bounded by the length of the (simple) parent climb from
      @{term stm} to @{term p}, hence by @{term "card V"}; this cap is carried directly in
      \<open>stem_loop_imp_wf\<close>, whose side conditions are discharged for the concrete move from
      @{const arb_invar} (no separate geometry locale is needed).\<close>

lemma dirty_pass_imp_rule:
  assumes V0: "0 \<notin> V" and drtV: "set drt \<subseteq> V" and thrdV: "ran (thrd S) \<subseteq> V"
  shows "<ndtree_drt_assn V S Ti (length drt) drt> dirty_pass_imp Ti 0 (length drt)
         <\<lambda>_. ndtree_assn V (dirty_pass S drt) Ti>"
  using dirty_pass_imp_aux[OF V0 drtV thrdV, of 0] by (simp add: dirty_pass_def)

subsection \<open>Primitives for the top-level composition\<close>

text \<open>The @{const ndtree_assn} counterparts of the @{const ndtree_drt_assn} read/write rules (the aux
      array is not tracked here), plus a bridge that introduces the singleton dirty list @{term "[j]"} by
      writing @{term j} to @{term "aux ! 0"} --- turning @{const ndtree_assn} into @{const ndtree_drt_assn}
      for the @{const stem_loop} call.  All mirror the pure @{const ndtree_rel} update lemmas.\<close>

lemma ndtree_nth_rvth[sep_heap_rules]:
  "u \<in> V \<Longrightarrow> <ndtree_assn V S Ti> Array.nth (rvth_impl Ti) u
     <\<lambda>r. ndtree_assn V S Ti * \<up> (r = nat_of_opt (rvth S u))>"
  unfolding ndtree_assn_unfold by (sep_auto simp: ndtree_rel_len_rvth ndtree_rel_rvth_nat_of_opt)

lemma ndtree_nth_thrd[sep_heap_rules]:
  "u \<in> V \<Longrightarrow> <ndtree_assn V S Ti> Array.nth (thrd_impl Ti) u
     <\<lambda>r. ndtree_assn V S Ti * \<up> (r = nat_of_opt (thrd S u))>"
  unfolding ndtree_assn_unfold by (sep_auto simp: ndtree_rel_len_thrd ndtree_rel_thrd_nat_of_opt)

lemma ndtree_upd_prnt_Some[sep_heap_rules]:
  "w \<in> V \<Longrightarrow> u \<in> V \<Longrightarrow> <ndtree_assn V S Ti> Array.upd w u (prnt_impl Ti)
     <\<lambda>_. ndtree_assn V (S\<lparr>prnt := (prnt S)(w \<mapsto> u)\<rparr>) Ti>"
  unfolding ndtree_assn_unfold by (sep_auto simp: ndtree_rel_len_prnt ndtree_rel_upd_prnt_Some)

lemma ndtree_upd_thrd_Some[sep_heap_rules]:
  "w \<in> V \<Longrightarrow> u \<in> V \<Longrightarrow> <ndtree_assn V S Ti> Array.upd w u (thrd_impl Ti)
     <\<lambda>_. ndtree_assn V (S\<lparr>thrd := (thrd S)(w \<mapsto> u)\<rparr>) Ti>"
  unfolding ndtree_assn_unfold by (sep_auto simp: ndtree_rel_len_thrd ndtree_rel_upd_thrd_Some)

lemma ndtree_upd_thrd_None[sep_heap_rules]:
  "w \<in> V \<Longrightarrow> <ndtree_assn V S Ti> Array.upd w 0 (thrd_impl Ti)
     <\<lambda>_. ndtree_assn V (S\<lparr>thrd := (thrd S)(w := None)\<rparr>) Ti>"
  unfolding ndtree_assn_unfold by (sep_auto simp: ndtree_rel_len_thrd ndtree_rel_upd_thrd_None)

lemma ndtree_upd_rvth[sep_heap_rules]:
  "w \<in> V \<Longrightarrow> u \<in> V \<Longrightarrow> <ndtree_assn V S Ti> Array.upd w u (rvth_impl Ti)
     <\<lambda>_. ndtree_assn V (S\<lparr>rvth := (rvth S)(w \<mapsto> u)\<rparr>) Ti>"
  unfolding ndtree_assn_unfold by (sep_auto simp: ndtree_rel_len_rvth ndtree_rel_upd_rvth)

text \<open>Bridge: writing @{term j} into @{term "aux ! 0"} realises the initial dirty list @{term "[j]"} of the
      @{const stem_loop} call.  Capacity @{term "0 < length al"} comes from @{thm ndtree_rel_aux_bound}
      (@{term "j \<in> V"} and @{term "V \<subseteq> {0..<length al}"}); @{const ndtree_rel} ignores the aux contents (@{thm ndtree_rel_upd_aux}).\<close>
lemma ndtree_assn_to_drt:
  assumes jV: "j \<in> V"
  shows "<ndtree_assn V S Ti> Array.upd 0 j (aux_impl Ti) <\<lambda>_. ndtree_drt_assn V S Ti 1 [j]>"
   using jV 
   by (sep_auto simp: ndtree_rel_upd_aux take_Suc_conv_app_nth ndtree_rel_upd_aux
                      ndtree_assn_unfold ndtree_drt_assn_def
                dest: ndtree_rel_aux_bound)

text \<open>The pre @{const ndtree_assn} already implies @{term "0 \<notin> V"} (the encoding); pull it out so the loop
      rules' side conditions can use it.\<close>
lemma ndtree_assn_0_notin_pre: "ndtree_assn V S Ti \<Longrightarrow>\<^sub>A ndtree_assn V S Ti * \<up>(0 \<notin> V)"
  unfolding ndtree_assn_unfold by (sep_auto simp: ndtree_rel_0_notin)

lemma zero_not_in_V_ndtree_assn_extract:
     "<ndtree_assn V S0 Ti> program <Q> =
      (0 \<notin> V \<longrightarrow> <ndtree_assn V S0 Ti> program <Q>)"
  by(sep_auto simp: ndtree_assn_def)


text \<open>\<^emph>\<open>Unconditional\<close> refinement of the fused loops by \<^emph>\<open>fixpoint\<close> induction on the heap
      @{command partial_function} (its \<open>fixp_induct\<close> rule), rather than @{thm[source] parent_spec_i.follow.pinduct}.
      This needs NO @{const parent_spec} / agreement --- only @{term "ran (prnt S) \<subseteq> V"} for the climb to stay
      in @{term V}.  For an \<^emph>\<open>invalid\<close> move the tree may be cyclic and the loop diverges, but under partial
      correctness the triple then holds vacuously.  This is what lets @{const update_tree_imp} shed the join
      geometry (@{term jn}).  Admissibility and the bottom case close by @{method simp} (as in the framework's
      own \<open>while.fixp_induct\<close> example); the step mirrors the @{text "_wf"} step with the IH supplied as a
      general heap rule.\<close>
lemma fused_vin_loop_imp_uncond:
  assumes V0: "0 \<notin> V"
  shows "u \<in> V \<and> lso \<in> V \<and> ran (prnt S) \<subseteq> V \<longrightarrow>
    <ndtree_assn V S Ti> fused_vin_loop_imp Ti u jv jn lso d la sa
    <\<lambda>_. ndtree_assn V (fused_vin_loop S u jv jn lso d la sa) Ti>"
  apply (induction arbitrary: S u la sa jv jn lso d rule: fused_vin_loop_imp.fixp_induct)
    apply simp
   apply simp
  subgoal premises IH for f S u la sa jv jn lso d
  proof (intro impI, elim conjE)
    assume uV: "u \<in> V" and lsoV: "lso \<in> V" and ranS: "ran (prnt S) \<subseteq> V"
    have IHr: "\<And>S2 u2 la2 sa2 jv2 jn2 lso2 d2. u2 \<in> V \<Longrightarrow> lso2 \<in> V \<Longrightarrow> ran (prnt S2) \<subseteq> V \<Longrightarrow> <ndtree_assn V S2 Ti> f Ti u2 jv2 jn2 lso2 d2 la2 sa2 <\<lambda>_. ndtree_assn V (fused_vin_loop S2 u2 jv2 jn2 lso2 d2 la2 sa2) Ti>"
      using IH by blast
    define la' where "la' = (la \<and> lsuc S u = jv)"
    define sa' where "sa' = (sa \<and> u \<noteq> jn)"
    define S' where "S' = S\<lparr>lsuc := (if la' then (lsuc S)(u := lso) else lsuc S), snum := (if sa' then (snum S)(u := snum S u + d) else snum S)\<rparr>"
    have prntS'eq: "prnt S' = prnt S" by (simp add: S'_def)
    have unfoldF: "fused_vin_loop S u jv jn lso d la sa = (if \<not> la' \<and> \<not> sa' then S else (case prnt S' u of None \<Rightarrow> S' | Some par \<Rightarrow> fused_vin_loop S' par jv jn lso d la' sa'))"
      by (subst fused_vin_loop.simps) (simp only: la'_def sa'_def S'_def Let_def)
    show "<ndtree_assn V S Ti> Array.nth (lsuc_impl Ti) u \<bind> (\<lambda>lsu. if \<not> (la \<and> lsu = jv) \<and> \<not> (sa \<and> u \<noteq> jn) then return () else (if la \<and> lsu = jv then Array.upd u lso (lsuc_impl Ti) \<bind> (\<lambda>_. return ()) else return ()) \<bind> (\<lambda>_. (if sa \<and> u \<noteq> jn then Array.nth (snum_impl Ti) u \<bind> (\<lambda>snu. Array.upd u (snu + d) (snum_impl Ti) \<bind> (\<lambda>_. return ())) else return ()) \<bind> (\<lambda>_. Array.nth (prnt_impl Ti) u \<bind> (\<lambda>par. if par = 0 then return () else f Ti par jv jn lso d (la \<and> lsu = jv) (sa \<and> u \<noteq> jn))))) <\<lambda>_. ndtree_assn V (fused_vin_loop S u jv jn lso d la sa) Ti>"
    proof (cases "prnt S u")
      case (Some w)
      have wV: "w \<in> V" using ranS Some unfolding ran_def by blast
      have wne: "w \<noteq> 0" using wV V0 by metis
      have fu: "fused_vin_loop S u jv jn lso d la sa = (if \<not> la' \<and> \<not> sa' then S else fused_vin_loop S' w jv jn lso d la' sa')"
        using unfoldF prntS'eq Some by simp
      show ?thesis unfolding fu S'_def la'_def sa'_def
        apply (sep_auto simp: uV lsoV ranS Some nat_of_opt_def wV wne heap: IHr split: if_split_asm)
        done
    next
      case None
      have fu: "fused_vin_loop S u jv jn lso d la sa = (if \<not> la' \<and> \<not> sa' then S else S')"
        using unfoldF prntS'eq None by simp
      show ?thesis unfolding fu S'_def la'_def sa'_def
        apply (sep_auto simp: uV lsoV None nat_of_opt_def)
        done
    qed
  qed
  done

lemma fused_vout_loop_imp_uncond:
  assumes V0: "0 \<notin> V"
  shows "u \<in> V \<and> sv \<in> V \<and> ran (prnt S) \<subseteq> V \<longrightarrow>
    <ndtree_assn V S Ti> fused_vout_loop_imp Ti u stp gv sv jn d la sa
    <\<lambda>_. ndtree_assn V (fused_vout_loop S u (opt_of_nat stp) gv sv jn d la sa) Ti>"
  apply (induction arbitrary: S u la sa stp gv sv jn d rule: fused_vout_loop_imp.fixp_induct)
    apply simp
   apply simp
  subgoal premises IH for f S u la sa stp gv sv jn d
  proof (intro impI, elim conjE)
    assume uV: "u \<in> V" and svV: "sv \<in> V" and ranS: "ran (prnt S) \<subseteq> V"
    have une: "u \<noteq> 0" using uV V0 by metis
    have stpb: "(Some u \<noteq> opt_of_nat stp) = (u \<noteq> stp)" using une by (auto simp: opt_of_nat_def)
    have IHr: "\<And>S2 u2 la2 sa2 stp2 gv2 sv2 jn2 d2. u2 \<in> V \<Longrightarrow> sv2 \<in> V \<Longrightarrow> ran (prnt S2) \<subseteq> V \<Longrightarrow> <ndtree_assn V S2 Ti> f Ti u2 stp2 gv2 sv2 jn2 d2 la2 sa2 <\<lambda>_. ndtree_assn V (fused_vout_loop S2 u2 (opt_of_nat stp2) gv2 sv2 jn2 d2 la2 sa2) Ti>"
      using IH by blast
    define la' where "la' = (la \<and> Some u \<noteq> opt_of_nat stp \<and> lsuc S u = gv)"
    define sa' where "sa' = (sa \<and> u \<noteq> jn)"
    define S' where "S' = S\<lparr>lsuc := (if la' then (lsuc S)(u := sv) else lsuc S), snum := (if sa' then (snum S)(u := snum S u - d) else snum S)\<rparr>"
    have prntS'eq: "prnt S' = prnt S" by (simp add: S'_def)
    have unfoldF: "fused_vout_loop S u (opt_of_nat stp) gv sv jn d la sa = (if \<not> la' \<and> \<not> sa' then S else (case prnt S' u of None \<Rightarrow> S' | Some par \<Rightarrow> fused_vout_loop S' par (opt_of_nat stp) gv sv jn d la' sa'))"
      by (subst fused_vout_loop.simps) (simp only: la'_def sa'_def S'_def Let_def)
    show "<ndtree_assn V S Ti> Array.nth (lsuc_impl Ti) u \<bind> (\<lambda>lsu. if \<not> (la \<and> u \<noteq> stp \<and> lsu = gv) \<and> \<not> (sa \<and> u \<noteq> jn) then return () else (if la \<and> u \<noteq> stp \<and> lsu = gv then Array.upd u sv (lsuc_impl Ti) \<bind> (\<lambda>_. return ()) else return ()) \<bind> (\<lambda>_. (if sa \<and> u \<noteq> jn then Array.nth (snum_impl Ti) u \<bind> (\<lambda>snu. Array.upd u (snu - d) (snum_impl Ti) \<bind> (\<lambda>_. return ())) else return ()) \<bind> (\<lambda>_. Array.nth (prnt_impl Ti) u \<bind> (\<lambda>par. if par = 0 then return () else f Ti par stp gv sv jn d (la \<and> u \<noteq> stp \<and> lsu = gv) (sa \<and> u \<noteq> jn))))) <\<lambda>_. ndtree_assn V (fused_vout_loop S u (opt_of_nat stp) gv sv jn d la sa) Ti>"
    proof (cases "prnt S u")
      case (Some w)
      have wV: "w \<in> V" using ranS Some unfolding ran_def by blast
      have wne: "w \<noteq> 0" using wV V0 by metis
      have fu: "fused_vout_loop S u (opt_of_nat stp) gv sv jn d la sa = (if \<not> la' \<and> \<not> sa' then S else fused_vout_loop S' w (opt_of_nat stp) gv sv jn d la' sa')"
        using unfoldF prntS'eq Some by simp
      show ?thesis unfolding fu S'_def la'_def sa'_def
        apply (sep_auto simp: uV svV ranS Some nat_of_opt_def wV wne stpb heap: IHr split: if_split_asm)
        done
    next
      case None
      have fu: "fused_vout_loop S u (opt_of_nat stp) gv sv jn d la sa = (if \<not> la' \<and> \<not> sa' then S else S')"
        using unfoldF prntS'eq None by simp
      show ?thesis unfolding fu S'_def la'_def sa'_def
        apply (sep_auto simp: uV svV None nat_of_opt_def stpb)
        done
    qed
  qed
  done

text \<open>Pull @{term "ran (prnt S) \<subseteq> V"} out of an @{const ndtree_assn} precondition: it is a conjunct of the
      underlying @{const ndtree_rel}, so if it fails the precondition is unsatisfiable (@{term false}) and the
      triple holds vacuously.  This lets the fused-loop tail read \<open>ran (prnt Sa) \<subseteq> V\<close> off the assertion
      instead of from @{thm fused_vin_loop_fields} (which would need @{const parent_spec}).\<close>
lemma ran_prnt_ndtree_assn_extract:
  "<ndtree_assn V S Ti> program <Q> = (ran (prnt S) \<subseteq> V \<longrightarrow> <ndtree_assn V S Ti> program <Q>)"
proof (cases "ran (prnt S) \<subseteq> V")
  case True thus ?thesis by simp
next
  case False
  have "ndtree_assn V S Ti = false"
    unfolding ndtree_assn_def using False by (auto simp: ndtree_rel_def)
  thus ?thesis by simp
qed

text \<open>Likewise \<open>lsuc S p \<in> V\<close> (for @{term "p \<in> V"}) is a consequence of @{const ndtree_rel}
      (@{term "\<forall>v\<in>V. lsuc S v \<in> V"}), so it too can be read off the precondition.\<close>
lemma lsuc_ndtree_assn_extract:
  assumes pV: "p \<in> V"
  shows "<ndtree_assn V S Ti> program <Q> = (lsuc S p \<in> V \<longrightarrow> <ndtree_assn V S Ti> program <Q>)"
proof (cases "lsuc S p \<in> V")
  case True thus ?thesis by simp
next
  case False
  hence keyf: "(\<forall>v\<in>V. lsuc S v \<in> V) = False" using pV by blast
  have "ndtree_assn V S Ti = false"
    unfolding ndtree_assn_def by (simp add: ndtree_rel_def keyf)
  thus ?thesis by simp
qed

lemma UT_tail:
  fixes S1 :: "nat ndtree"
  assumes jV: "j \<in> V" and jnV: "jn \<in> V" and pV: "p \<in> V"
      and voutV: "v_out \<in> V" and oldrevV: "old_rev \<in> V" and oldlastV: "old_last \<in> V"
  shows "<ndtree_assn V S1 Ti>
     Array.nth (lsuc_impl Ti) jn \<bind> (\<lambda>ls_jn.
     Array.nth (lsuc_impl Ti) p \<bind> (\<lambda>last_out.
     return (if ls_jn = j then jn else 0) \<bind> (\<lambda>up_limit.
     fused_vin_loop_imp Ti j j jn last_out old_num True True \<bind> (\<lambda>_.
     if jn \<noteq> old_rev \<and> j \<noteq> old_rev then fused_vout_loop_imp Ti v_out up_limit old_last old_rev jn old_num True True
     else if last_out \<noteq> old_last then fused_vout_loop_imp Ti v_out up_limit old_last last_out jn old_num True True
     else fused_vout_loop_imp Ti v_out up_limit old_last old_last jn old_num False True))))
   <\<lambda>_. ndtree_assn V (
     if jn \<noteq> old_rev \<and> j \<noteq> old_rev
     then fused_vout_loop (fused_vin_loop S1 j j jn (lsuc S1 p) old_num True True) v_out (if lsuc S1 jn = j then Some jn else None) old_last old_rev jn old_num True True
     else if lsuc S1 p \<noteq> old_last
          then fused_vout_loop (fused_vin_loop S1 j j jn (lsuc S1 p) old_num True True) v_out (if lsuc S1 jn = j then Some jn else None) old_last (lsuc S1 p) jn old_num True True
          else fused_vout_loop (fused_vin_loop S1 j j jn (lsuc S1 p) old_num True True) v_out (if lsuc S1 jn = j then Some jn else None) old_last old_last jn old_num False True) Ti>"
proof(subst zero_not_in_V_ndtree_assn_extract, subst ran_prnt_ndtree_assn_extract,
      subst lsuc_ndtree_assn_extract[OF pV], (rule impI)+, goal_cases)
  case 1
  note V0 = this(1) and ran1 = this(2) and lastoutV = this(3)
  define Sa where "Sa = fused_vin_loop S1 j j jn (lsuc S1 p) old_num True True"
  have vin: "<ndtree_assn V S1 Ti> fused_vin_loop_imp Ti j j jn (lsuc S1 p) old_num True True
             <\<lambda>_. ndtree_assn V Sa Ti>"
    using fused_vin_loop_imp_uncond[OF V0] jV lastoutV ran1 by (simp add: Sa_def)
  have uleq: "opt_of_nat (if lsuc S1 jn = j then jn else 0) = (if lsuc S1 jn = j then Some jn else None)"
    using jnV V0 by (auto simp: opt_of_nat_def)
  have voutT: "<ndtree_assn V Sa Ti> fused_vout_loop_imp Ti v_out (if lsuc S1 jn = j then jn else 0) gv sv jn old_num la True
       <\<lambda>_. ndtree_assn V (fused_vout_loop Sa v_out (if lsuc S1 jn = j then Some jn else None) gv sv jn old_num la True) Ti>"
    if svV: "sv \<in> V" for gv sv la
    apply (subst ran_prnt_ndtree_assn_extract, rule impI)
    apply (subst uleq[symmetric])
    apply (rule fused_vout_loop_imp_uncond[OF V0, THEN mp])
    using voutV svV by blast
  have tail_if: "<ndtree_assn V Sa Ti>
     (if jn \<noteq> old_rev \<and> j \<noteq> old_rev then fused_vout_loop_imp Ti v_out (if lsuc S1 jn = j then jn else 0) old_last old_rev jn old_num True True
      else if lsuc S1 p \<noteq> old_last then fused_vout_loop_imp Ti v_out (if lsuc S1 jn = j then jn else 0) old_last (lsuc S1 p) jn old_num True True
      else fused_vout_loop_imp Ti v_out (if lsuc S1 jn = j then jn else 0) old_last old_last jn old_num False True)
     <\<lambda>_. ndtree_assn V (
       if jn \<noteq> old_rev \<and> j \<noteq> old_rev then fused_vout_loop Sa v_out (if lsuc S1 jn = j then Some jn else None) old_last old_rev jn old_num True True
       else if lsuc S1 p \<noteq> old_last then fused_vout_loop Sa v_out (if lsuc S1 jn = j then Some jn else None) old_last (lsuc S1 p) jn old_num True True
       else fused_vout_loop Sa v_out (if lsuc S1 jn = j then Some jn else None) old_last old_last jn old_num False True) Ti>"
  proof (cases "jn \<noteq> old_rev \<and> j \<noteq> old_rev")
    case c1: True
    show ?thesis by (subst if_P[OF c1], subst if_P[OF c1]) (rule voutT[OF oldrevV])
  next
    case c1: False
    show ?thesis
    proof (cases "lsuc S1 p \<noteq> old_last")
      case c2: True
      show ?thesis
        by (subst if_not_P[OF c1], subst if_not_P[OF c1], subst if_P[OF c2], subst if_P[OF c2]) (rule voutT[OF lastoutV])
    next
      case c2: False
      show ?thesis
        by (subst if_not_P[OF c1], subst if_not_P[OF c1], subst if_not_P[OF c2], subst if_not_P[OF c2]) (rule voutT[OF oldlastV])
    qed
  qed
  show ?thesis
    unfolding Sa_def[symmetric]
    apply (rule ht_bind[OF ndtree_nth_lsuc[OF jnV]], rule ht_extract_pre_pure, hypsubst)
    apply (rule ht_bind[OF ndtree_nth_lsuc[OF pV]], rule ht_extract_pre_pure, hypsubst)
    apply (simp only: return_bind)
    apply (rule ht_bind[OF vin])
    apply (rule tail_if)
    done
qed

lemma no_None: "nat_of_opt None = 0" by (simp add: nat_of_opt_def)
lemma no_Some: "nat_of_opt (Some a) = a" by (simp add: nat_of_opt_def)

text \<open>The recurring aftn-style thread/reverse-thread edit: when \<open>aft = 0\<close> it clears \<open>thrd bef\<close>, else it
      sets \<open>thrd bef := aft\<close> and \<open>rvth aft := bef\<close>.  Occurs in both the simple (\<open>i = p\<close>) and reversal
      branches of @{const update_tree}, and in the tail of the reversal branch.  Proved by @{thm ht_bind}
      (avoids the @{const None} / @{const Some}-@{term "0::nat"} overlap).\<close>
lemma aftT:
  assumes V0: "0 \<notin> V" and befV: "bef \<in> V" and aV: "\<And>a. aft_opt = Some a \<Longrightarrow> a \<in> V"
  shows "<ndtree_assn V St Ti>
     (if nat_of_opt aft_opt = 0 then Array.upd bef 0 (thrd_impl Ti) \<bind> (\<lambda>_. return ())
      else Array.upd bef (nat_of_opt aft_opt) (thrd_impl Ti) \<bind> (\<lambda>_. Array.upd (nat_of_opt aft_opt) bef (rvth_impl Ti) \<bind> (\<lambda>_. return ())))
   <\<lambda>_. ndtree_assn V (case aft_opt of None \<Rightarrow> St\<lparr>thrd := (thrd St)(bef := None)\<rparr>
                        | Some a \<Rightarrow> St\<lparr>thrd := (thrd St)(bef \<mapsto> a), rvth := (rvth St)(a \<mapsto> bef)\<rparr>) Ti>"
proof (cases aft_opt)
  case None
  show ?thesis unfolding None
    apply (simp only: no_None if_P[OF refl] option.case)
    apply (rule ht_bind[OF ndtree_upd_thrd_None[OF befV]])
    apply sep_auto
    done
next
  case (Some a)
  have aV': "a \<in> V" using aV Some by simp
  have aneq: "a \<noteq> 0" using aV' V0 by metis
  show ?thesis unfolding Some
    apply (simp only: no_Some if_not_P[OF aneq] option.case bind_bind return_bind)
    apply (rule ht_bind[OF ndtree_upd_thrd_Some[OF befV aV']])
    apply (rule ht_bind[OF ndtree_upd_rvth[OF aV' befV]])
    apply sep_auto
    done
qed

text \<open>The @{const ndtree_drt_assn} counterparts needed inside the reversal branch (the aux array is live
      until @{const dirty_pass_imp}): an @{const lsuc} write and the aft-case edit.\<close>
lemma ndtree_drt_upd_lsuc[sep_heap_rules]:
  "w \<in> V \<Longrightarrow> x \<in> V \<Longrightarrow> <ndtree_drt_assn V S Ti sp drt> Array.upd w x (lsuc_impl Ti)
     <\<lambda>_. ndtree_drt_assn V (S\<lparr>lsuc := (lsuc S)(w := x)\<rparr>) Ti sp drt>"
  unfolding ndtree_drt_assn_def by (sep_auto simp: ndtree_rel_len_lsuc ndtree_rel_upd_lsuc)

lemma aftT_drt:
  assumes V0: "0 \<notin> V" and befV: "bef \<in> V" and aV: "\<And>a. aft_opt = Some a \<Longrightarrow> a \<in> V"
  shows "<ndtree_drt_assn V St Ti sp drt>
     (if nat_of_opt aft_opt = 0 then Array.upd bef 0 (thrd_impl Ti) \<bind> (\<lambda>_. return ())
      else Array.upd bef (nat_of_opt aft_opt) (thrd_impl Ti) \<bind> (\<lambda>_. Array.upd (nat_of_opt aft_opt) bef (rvth_impl Ti) \<bind> (\<lambda>_. return ())))
   <\<lambda>_. ndtree_drt_assn V (case aft_opt of None \<Rightarrow> St\<lparr>thrd := (thrd St)(bef := None)\<rparr>
                        | Some a \<Rightarrow> St\<lparr>thrd := (thrd St)(bef \<mapsto> a), rvth := (rvth St)(a \<mapsto> bef)\<rparr>) Ti sp drt>"
proof (cases aft_opt)
  case None
  show ?thesis unfolding None
    apply (simp only: no_None if_P[OF refl] option.case)
    apply (rule ht_bind[OF ndtree_drt_upd_thrd_None[OF befV]])
    apply sep_auto
    done
next
  case (Some a)
  have aV': "a \<in> V" using aV Some by simp
  have aneq: "a \<noteq> 0" using aV' V0 by metis
  show ?thesis unfolding Some
    apply (simp only: no_Some if_not_P[OF aneq] option.case bind_bind return_bind)
    apply (rule ht_bind[OF ndtree_drt_upd_thrd_Some[OF befV aV']])
    apply (rule ht_bind[OF ndtree_drt_upd_rvth[OF aV' befV]])
    apply sep_auto
    done
qed

text \<open>The simple (@{term "i = p"}) branch of @{const update_tree_imp}: relocate @{term i}'s parent to
      @{term j}, and (unless @{term j} is already threaded before @{term p}) splice the thread so @{term p}
      follows @{term j}.  Two @{thm [source] aftT} edits (at \<open>old_rev\<close> on \<open>Sa\<close>, at \<open>old_last\<close> on
      \<open>Sc\<close>) plus the \<open>j \<mapsto> p\<close> / \<open>p \<mapsto> j\<close> thread/reverse-thread links.\<close>
lemma UT_simple:
  fixes S0 :: "nat ndtree"
  assumes iV: "i \<in> V" and jV: "j \<in> V" and pV: "p \<in> V"
      and oldrevV: "old_rev \<in> V" and oldlastV: "old_last \<in> V"
      and thrdV: "ran (thrd S0) \<subseteq> V"
  shows "<ndtree_assn V S0 Ti>
     do {
        _ \<leftarrow> Array.upd i j (prnt_impl Ti);
        tj \<leftarrow> Array.nth (thrd_impl Ti) j;
        (if tj = p then return ()
         else do {
           aft1 \<leftarrow> Array.nth (thrd_impl Ti) old_last;
           _ \<leftarrow> (if aft1 = 0 then do { _ \<leftarrow> Array.upd old_rev 0 (thrd_impl Ti); return () }
                  else do { _ \<leftarrow> Array.upd old_rev aft1 (thrd_impl Ti);
                            _ \<leftarrow> Array.upd aft1 old_rev (rvth_impl Ti); return () });
           aft2 \<leftarrow> Array.nth (thrd_impl Ti) j;
           _ \<leftarrow> Array.upd j p (thrd_impl Ti);
           _ \<leftarrow> Array.upd p j (rvth_impl Ti);
           (if aft2 = 0 then do { _ \<leftarrow> Array.upd old_last 0 (thrd_impl Ti); return () }
            else do { _ \<leftarrow> Array.upd old_last aft2 (thrd_impl Ti);
                      _ \<leftarrow> Array.upd aft2 old_last (rvth_impl Ti); return () })
         })
     }
   <\<lambda>_. ndtree_assn V (
     let Sa = S0\<lparr>prnt := (prnt S0)(i \<mapsto> j)\<rparr>
     in if thrd Sa j = Some p then Sa
        else (let Sb = (case thrd Sa old_last of None \<Rightarrow> Sa\<lparr>thrd := (thrd Sa)(old_rev := None)\<rparr>
                        | Some a \<Rightarrow> Sa\<lparr>thrd := (thrd Sa)(old_rev \<mapsto> a), rvth := (rvth Sa)(a \<mapsto> old_rev)\<rparr>);
                  Sc = Sb\<lparr>thrd := (thrd Sb)(j \<mapsto> p), rvth := (rvth Sb)(p \<mapsto> j)\<rparr>
              in (case thrd Sb j of None \<Rightarrow> Sc\<lparr>thrd := (thrd Sc)(old_last := None)\<rparr>
                  | Some a \<Rightarrow> Sc\<lparr>thrd := (thrd Sc)(old_last \<mapsto> a), rvth := (rvth Sc)(a \<mapsto> old_last)\<rparr>))) Ti>"
proof(subst zero_not_in_V_ndtree_assn_extract, rule impI, goal_cases)
  case 1
  note V0 = this
  define Sa where "Sa = S0\<lparr>prnt := (prnt S0)(i \<mapsto> j)\<rparr>"
  define Sb where "Sb = (case thrd Sa old_last of None \<Rightarrow> Sa\<lparr>thrd := (thrd Sa)(old_rev := None)\<rparr>
                        | Some a \<Rightarrow> Sa\<lparr>thrd := (thrd Sa)(old_rev \<mapsto> a), rvth := (rvth Sa)(a \<mapsto> old_rev)\<rparr>)"
  define Sc where "Sc = Sb\<lparr>thrd := (thrd Sb)(j \<mapsto> p), rvth := (rvth Sb)(p \<mapsto> j)\<rparr>"
  have thrdSa: "thrd Sa = thrd S0" by (simp add: Sa_def)
  have pne0: "p \<noteq> 0" using pV V0 by metis
  have rvth_thrd: "\<And>St x. rvth (St\<lparr>thrd := x\<rparr>) = rvth St" by simp
  have aft1V: "\<And>a. thrd Sa old_last = Some a \<Longrightarrow> a \<in> V" using thrdV thrdSa by (auto simp: ran_def)
  have ranSb: "ran (thrd Sb) \<subseteq> V" using thrdV thrdSa aft1V by (cases "thrd Sa old_last") (auto simp: Sb_def ran_def)
  have aft2V: "\<And>a. thrd Sb j = Some a \<Longrightarrow> a \<in> V" using ranSb by (auto simp: ran_def)
  have condeq: "(nat_of_opt (thrd Sa j) = p) = (thrd Sa j = Some p)"
    using pne0 by (cases "thrd Sa j") (auto simp: no_None no_Some)
  have aft1: "<ndtree_assn V Sa Ti>
      (if nat_of_opt (thrd Sa old_last) = 0 then Array.upd old_rev 0 (thrd_impl Ti) \<bind> (\<lambda>_. return ())
       else Array.upd old_rev (nat_of_opt (thrd Sa old_last)) (thrd_impl Ti) \<bind> (\<lambda>_. Array.upd (nat_of_opt (thrd Sa old_last)) old_rev (rvth_impl Ti) \<bind> (\<lambda>_. return ())))
      <\<lambda>_. ndtree_assn V Sb Ti>"
    using aftT[OF V0 oldrevV aft1V] by (simp add: Sb_def)
  have aft2: "<ndtree_assn V Sc Ti>
      (if nat_of_opt (thrd Sb j) = 0 then Array.upd old_last 0 (thrd_impl Ti) \<bind> (\<lambda>_. return ())
       else Array.upd old_last (nat_of_opt (thrd Sb j)) (thrd_impl Ti) \<bind> (\<lambda>_. Array.upd (nat_of_opt (thrd Sb j)) old_last (rvth_impl Ti) \<bind> (\<lambda>_. return ())))
      <\<lambda>_. ndtree_assn V (case thrd Sb j of None \<Rightarrow> Sc\<lparr>thrd := (thrd Sc)(old_last := None)\<rparr>
                          | Some a \<Rightarrow> Sc\<lparr>thrd := (thrd Sc)(old_last \<mapsto> a), rvth := (rvth Sc)(a \<mapsto> old_last)\<rparr>) Ti>"
    using aftT[OF V0 oldlastV aft2V] by simp
  show ?thesis
    unfolding Let_def Sa_def[symmetric] Sb_def[symmetric] Sc_def[symmetric]
    apply (rule ht_bind[OF ndtree_upd_prnt_Some[OF iV jV]])
    apply (fold Sa_def)
    apply (rule ht_bind[OF ndtree_nth_thrd[OF jV]], rule ht_extract_pre_pure, hypsubst)
    apply (simp only: condeq)
    apply (cases "thrd Sa j = Some p")
    subgoal premises P
      apply (simp only: if_P[OF P(1)])
      apply sep_auto
      done
    subgoal premises P
      apply (simp only: if_not_P[OF P(1)])
      apply (rule ht_bind[OF ndtree_nth_thrd[OF oldlastV]], rule ht_extract_pre_pure, hypsubst)
      apply (rule ht_bind[OF aft1])
      apply (rule ht_bind[OF ndtree_nth_thrd[OF jV]], rule ht_extract_pre_pure, hypsubst)
      apply (rule ht_bind[OF ndtree_upd_thrd_Some[OF jV pV]])
      apply (rule ht_bind[OF ndtree_upd_rvth[OF pV jV]])
      apply (simp only: rvth_thrd)
      apply (fold Sc_def)
      apply (rule aft2)
      done
    done
qed

text \<open>The path-reversal (@{term "i \<noteq> p"}) branch of @{const update_tree_imp}, as a standalone program, and
      its functional twin (the @{term "i \<noteq> p"} arm of @{const update_tree}), read off @{thm [source] update_tree_def}.\<close>
definition ut_reversal_imp :: "ndtree_impl \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "ut_reversal_imp Ti i j p old_rev old_num old_last =
     do {
        thread_cont \<leftarrow> (if old_rev = j then Array.nth (thrd_impl Ti) old_last else Array.nth (thrd_impl Ti) j);
        lsx0 \<leftarrow> Array.nth (lsuc_impl Ti) i;
        aft0 \<leftarrow> Array.nth (thrd_impl Ti) lsx0;
        _ \<leftarrow> Array.upd j i (thrd_impl Ti);
        _ \<leftarrow> Array.upd 0 j (aux_impl Ti);
        r \<leftarrow> stem_loop_imp Ti i j lsx0 aft0 1 p;
        (case r of (pstm, lsx, aft, sp) \<Rightarrow> do {
           _ \<leftarrow> Array.upd p pstm (prnt_impl Ti);
           _ \<leftarrow> (if thread_cont = 0 then do { _ \<leftarrow> Array.upd lsx 0 (thrd_impl Ti); return () }
                  else do { _ \<leftarrow> Array.upd lsx thread_cont (thrd_impl Ti);
                            _ \<leftarrow> Array.upd thread_cont lsx (rvth_impl Ti); return () });
           _ \<leftarrow> Array.upd p lsx (lsuc_impl Ti);
           _ \<leftarrow> (if old_rev \<noteq> j
                  then (if aft = 0 then do { _ \<leftarrow> Array.upd old_rev 0 (thrd_impl Ti); return () }
                        else do { _ \<leftarrow> Array.upd old_rev aft (thrd_impl Ti);
                                  _ \<leftarrow> Array.upd aft old_rev (rvth_impl Ti); return () })
                  else return ());
           _ \<leftarrow> dirty_pass_imp Ti 0 sp;
           tls \<leftarrow> Array.nth (lsuc_impl Ti) p;
           _ \<leftarrow> stem_num_loop_imp Ti p i 0 tls;
           _ \<leftarrow> Array.upd i old_num (snum_impl Ti);
           return ()
        })
     }"

definition ut_reversal_fun :: "nat ndtree \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat ndtree" where
  "ut_reversal_fun S0 i j p old_rev old_num old_last =
     (let thread_cont = (if old_rev = j then thrd S0 old_last else thrd S0 j)
     in let Sinit = S0\<lparr>thrd := (thrd S0)(j \<mapsto> i)\<rparr>
     in (case stem_loop Sinit i j (lsuc S0 i) (thrd S0 (lsuc S0 i)) [j] p of (Sl, pstm, lsx, aft, drt) \<Rightarrow>
        let Sp = Sl\<lparr>prnt := (prnt Sl)(p \<mapsto> pstm)\<rparr>
        in let Sq = (case thread_cont of None \<Rightarrow> Sp\<lparr>thrd := (thrd Sp)(lsx := None)\<rparr>
                     | Some a \<Rightarrow> Sp\<lparr>thrd := (thrd Sp)(lsx \<mapsto> a), rvth := (rvth Sp)(a \<mapsto> lsx)\<rparr>)
        in let Sr = Sq\<lparr>lsuc := (lsuc Sq)(p := lsx)\<rparr>
        in let Ss = (if old_rev \<noteq> j
                     then (case aft of None \<Rightarrow> Sr\<lparr>thrd := (thrd Sr)(old_rev := None)\<rparr>
                           | Some a \<Rightarrow> Sr\<lparr>thrd := (thrd Sr)(old_rev \<mapsto> a), rvth := (rvth Sr)(a \<mapsto> old_rev)\<rparr>)
                     else Sr)
        in let St = dirty_pass Ss drt
        in let Su = stem_num_loop St (snum S0) p i 0 (lsuc St p)
        in Su\<lparr>snum := (snum Su)(i := old_num)\<rparr>))"

text \<open>Aux-push capacity via a \<^emph>\<open>counting\<close> bound (@{term "length drt \<le> card V"}) instead of distinctness of the
      dirty list --- because without the move geometry the dirty list need not be distinct, but the number of
      pushes is still bounded by the length of the (simple) parent climb, hence by @{term "card V"}.\<close>
lemma drt_push_cap_cnt:
  assumes V0: "0 \<notin> V" and Vn: "V \<subseteq> {0..<n}" and finV: "finite V" and Vne: "V \<noteq> {}"
      and cnt: "length xs \<le> card V"
  shows "length xs < n"
proof -
  have s: "V \<subseteq> {Suc 0..<n}"
  proof
    fix x assume xV: "x \<in> V"
    have "0 < x" using xV V0 by (cases x) auto
    moreover have "x < n" using xV Vn by auto
    ultimately show "x \<in> {Suc 0..<n}" by simp
  qed
  have cle: "card V \<le> n - 1" using card_mono[OF finite_atLeastLessThan s] by simp
  have "0 < card V" using Vne finV by (simp add: card_gt_0_iff)
  hence "0 < n" using cle by (cases n) auto
  thus ?thesis using cnt cle by simp
qed

lemma ndtree_rel_drt_cap_cnt:
  assumes "ndtree_rel V S pl thl rl ll sl al" "finite V" "V \<noteq> {}" "length xs \<le> card V"
  shows "length xs < length al"
  by (rule drt_push_cap_cnt[OF ndtree_rel_0_notin[OF assms(1)] ndtree_rel_aux_bound[OF assms(1)] assms(2,3,4)])

lemma ndtree_drt_push_aux_cnt:
  assumes finV: "finite V" and Vne: "V \<noteq> {}" and cnt: "length drt \<le> card V"
  shows "<ndtree_drt_assn V S Ti (length drt) drt> Array.upd (length drt) lsx (aux_impl Ti)
         <\<lambda>_. ndtree_drt_assn V S Ti (Suc (length drt)) (drt @ [lsx])>"
  unfolding ndtree_drt_assn_def
  by (sep_auto simp: take_Suc_conv_app_nth nth_list_update_eq take_update_cancel
                     ndtree_rel_drt_cap_cnt finV Vne cnt)

text \<open>The @{const ndtree_drt_assn} assertion already entails the range / @{const lsuc} / fill-pointer / @{term "0 \<notin> V"}
      / finiteness facts (they live in @{const ndtree_rel}); this lets us drop them from the preconditions of
      @{text stem_loop_imp_wf} and recover them locally where the induction needs them as plain facts.\<close>
lemma ndtree_drt_assn_facts:
  "ndtree_drt_assn V S Ti sp drt \<Longrightarrow>\<^sub>A ndtree_drt_assn V S Ti sp drt *
     \<up>(ran (thrd S) \<subseteq> V \<and> ran (rvth S) \<subseteq> V \<and> (\<forall>v \<in> V. lsuc S v \<in> V)
       \<and> sp = length drt \<and> 0 \<notin> V \<and> finite V)"
  unfolding ndtree_drt_assn_def
  apply (subst ent_pure_post_iff, rule conjI, rule ent_refl)
  apply (clarsimp simp: mod_ex_dist mod_pure_star_dist)
  by (auto simp: ran_def ndtree_rel_lsuc_V ndtree_rel_0_notin
           dest: ndtree_rel_thrd_ranI ndtree_rel_rvth_ranI
           intro: finite_subset[OF ndtree_rel_aux_bound finite_atLeastLessThan])

text \<open>Leaner @{const stem_loop} refinement (work in progress): instead of the full move geometry it needs
      only \<^emph>\<open>well-foundedness of the parent map\<close> (@{const parent_spec}) plus reachability of \<open>p\<close> along the
      parent climb.  The one crash risk --- overflowing the aux array at the \<open>Array.upd sp\<close> push --- is ruled out
      because @{const parent_spec} makes the climb \<open>follow P stm\<close> a distinct, \<open>\<subseteq> V\<close> simple path,
      so \<open>sp \<le> card V < length aux\<close> (using \<open>0 \<notin> V\<close>).  Proved by well-founded induction on the
      parent @{const follow}, carrying the invariant that the mutated @{const prnt} still agrees with \<open>P\<close>
      on the un-visited tail of the climb.\<close>
lemma stem_loop_imp_wf:
  assumes ps: "parent_spec P" and ranP: "ran P \<subseteq> V"
  shows "(\<forall>v \<in> set (follow P stm). prnt S v = P v) \<and> p \<in> set (follow P stm)
         \<and> stm \<in> V \<and> pstm \<in> V \<and> lsx \<in> V \<and> (\<forall>a. aft = Some a \<longrightarrow> a \<in> V)
         \<and> length drt + length (follow P stm) \<le> Suc (card V)
         \<and> (\<forall>v \<in> set (follow P stm). p \<in> set (follow P v) \<and> v \<noteq> p \<longrightarrow> rvth S v \<noteq> None)
     \<longrightarrow> <ndtree_drt_assn V S Ti sp drt> stem_loop_imp Ti stm pstm lsx (nat_of_opt aft) sp p
         <\<lambda>(pstm', lsx', aft', sp'). case stem_loop S stm pstm lsx aft drt p of (Sl, pst, ls, af, dr) \<Rightarrow>
             ndtree_drt_assn V Sl Ti sp' dr * \<up>(pstm' = pst \<and> lsx' = ls \<and> aft' = nat_of_opt af \<and> sp' = length dr)>"
proof (induction arbitrary: S pstm lsx aft drt sp rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF ps, of stm]])
  case (1 stm)
  show ?case
  proof (intro impI, elim conjE)
    assume agr: "\<forall>v \<in> set (follow P stm). prnt S v = P v" and pin: "p \<in> set (follow P stm)"
       and stmV: "stm \<in> V" and pstmV: "pstm \<in> V" and lsxV: "lsx \<in> V"
       and aftV: "\<forall>a. aft = Some a \<longrightarrow> a \<in> V"
       and cap: "length drt + length (follow P stm) \<le> Suc (card V)"
       and rvthdef: "\<forall>v \<in> set (follow P stm). p \<in> set (follow P v) \<and> v \<noteq> p \<longrightarrow> rvth S v \<noteq> None"
    show "<ndtree_drt_assn V S Ti sp drt> stem_loop_imp Ti stm pstm lsx (nat_of_opt aft) sp p
          <\<lambda>(pstm', lsx', aft', sp'). case stem_loop S stm pstm lsx aft drt p of (Sl, pst, ls, af, dr) \<Rightarrow>
             ndtree_drt_assn V Sl Ti sp' dr * \<up>(pstm' = pst \<and> lsx' = ls \<and> aft' = nat_of_opt af \<and> sp' = length dr)>"
    proof (rule ht_cons_pre[OF ndtree_drt_assn_facts], rule ht_extract_pre_pure)
      assume "ran (thrd S) \<subseteq> V \<and> ran (rvth S) \<subseteq> V \<and> (\<forall>v \<in> V. lsuc S v \<in> V) \<and> sp = length drt \<and> 0 \<notin> V \<and> finite V"
      then have ranthrd: "ran (thrd S) \<subseteq> V" and ranrvth: "ran (rvth S) \<subseteq> V"
        and lsucVV: "\<forall>v \<in> V. lsuc S v \<in> V" and spd: "sp = length drt" and V0: "0 \<notin> V" and finV: "finite V" by auto
      show "<ndtree_drt_assn V S Ti sp drt> stem_loop_imp Ti stm pstm lsx (nat_of_opt aft) sp p
            <\<lambda>(pstm', lsx', aft', sp'). case stem_loop S stm pstm lsx aft drt p of (Sl, pst, ls, af, dr) \<Rightarrow>
               ndtree_drt_assn V Sl Ti sp' dr * \<up>(pstm' = pst \<and> lsx' = ls \<and> aft' = nat_of_opt af \<and> sp' = length dr)>"
      proof (cases "stm = p")
      case True
      have f: "stem_loop S stm pstm lsx aft drt p = (S, pstm, lsx, aft, drt)" using True by (subst stem_loop.simps) simp
      show ?thesis unfolding f using True by (subst stem_loop_imp.simps) (sep_auto simp: spd)
    next
      case False
      obtain nxt where Pnxt: "P stm = Some nxt" using pin False by (cases "P stm") (auto simp: follow_ps_simps[OF ps])
      have fstm: "follow P stm = stm # follow P nxt" using Pnxt by (subst follow_ps_simps[OF ps]) simp
      have nxtV: "nxt \<in> V" using ranP Pnxt unfolding ran_def by blast
      have pnxt: "p \<in> set (follow P nxt)" using pin fstm False by auto
      have stmnotin: "stm \<notin> set (follow P nxt)" using fstm follow_distinct_ps[OF ps, of stm] by simp
      have prntstm: "prnt S stm = Some nxt" using agr fstm Pnxt by auto
      have stmin: "stm \<in> set (follow P stm)" using fstm by simp
      have rvthstm: "rvth S stm \<noteq> None" using rvthdef stmin pin False by blast
      have befV: "the (rvth S stm) \<in> V" using rvthstm ranrvth by (cases "rvth S stm") (auto simp: ran_def)
      define S1 where "S1 = S\<lparr>thrd := (thrd S)(lsx \<mapsto> nxt)\<rparr>"
      define S2 where "S2 = (case aft of None \<Rightarrow> S1\<lparr>thrd := (thrd S1)(the (rvth S1 stm) := None)\<rparr>
                            | Some a \<Rightarrow> S1\<lparr>thrd := (thrd S1)(the (rvth S1 stm) \<mapsto> a), rvth := (rvth S1)(a \<mapsto> the (rvth S1 stm))\<rparr>)"
      define S3 where "S3 = S2\<lparr>prnt := (prnt S2)(stm \<mapsto> pstm)\<rparr>"
      define lsx' where "lsx' = (if lsuc S3 nxt = lsuc S3 stm then the (rvth S3 stm) else lsuc S3 nxt)"
      define aft' where "aft' = thrd S3 lsx'"
      have fstep: "stem_loop S stm pstm lsx aft drt p = stem_loop S3 nxt stm lsx' aft' (drt @ [lsx]) p"
        using False prntstm by (subst stem_loop.simps) (simp add: S1_def S2_def S3_def lsx'_def aft'_def Let_def cong: if_cong split: option.split)
      have prntS3: "prnt S3 = (prnt S)(stm \<mapsto> pstm)" by (simp add: S3_def S2_def S1_def split: option.split)
      have agr': "\<forall>v \<in> set (follow P nxt). prnt S3 v = P v" using agr fstm stmnotin prntS3 by auto
      have cap': "length (drt @ [lsx]) + length (follow P nxt) \<le> Suc (card V)" using cap fstm by simp
      have ranthrd3: "ran (thrd S3) \<subseteq> V" using ranthrd nxtV aftV by (cases aft) (auto simp: S3_def S2_def S1_def ran_def)
      have ranrvth3: "ran (rvth S3) \<subseteq> V" using ranrvth befV by (cases aft) (auto simp: S3_def S2_def S1_def ran_def)
      have lsuc3: "lsuc S3 = lsuc S" by (simp add: S3_def S2_def S1_def split: option.split)
      have rvth3stmV: "the (rvth S3 stm) \<in> V" using rvthstm befV ranrvth by (cases aft) (auto simp: S3_def S2_def S1_def ran_def)
      have lsx'V: "lsx' \<in> V" using rvth3stmV lsucVV nxtV lsuc3 by (auto simp: lsx'_def)
      have aft'V: "\<forall>a. aft' = Some a \<longrightarrow> a \<in> V" using ranthrd3 by (auto simp: aft'_def ran_def)
      have rvthdef3: "\<forall>v \<in> set (follow P nxt). p \<in> set (follow P v) \<and> v \<noteq> p \<longrightarrow> rvth S3 v \<noteq> None"
        using rvthdef fstm by (cases aft) (auto simp: S3_def S2_def S1_def)
      have lsucVV3: "\<forall>v \<in> V. lsuc S3 v \<in> V" using lsucVV lsuc3 by simp
      have ante: "(\<forall>v \<in> set (follow P nxt). prnt S3 v = P v) \<and> p \<in> set (follow P nxt) \<and> nxt \<in> V \<and> stm \<in> V \<and> lsx' \<in> V \<and> (\<forall>a. aft' = Some a \<longrightarrow> a \<in> V) \<and> length (drt @ [lsx]) + length (follow P nxt) \<le> Suc (card V) \<and> (\<forall>v \<in> set (follow P nxt). p \<in> set (follow P v) \<and> v \<noteq> p \<longrightarrow> rvth S3 v \<noteq> None)"
        using agr' pnxt nxtV stmV lsx'V aft'V cap' rvthdef3 by simp
      have IH: "<ndtree_drt_assn V S3 Ti (Suc sp) (drt @ [lsx])> stem_loop_imp Ti nxt stm lsx' (nat_of_opt aft') (Suc sp) p
          <\<lambda>(pstm', lsx'', aft'', sp'). case stem_loop S3 nxt stm lsx' aft' (drt @ [lsx]) p of (Sl, pst, ls, af, dr) \<Rightarrow>
             ndtree_drt_assn V Sl Ti sp' dr * \<up>(pstm' = pst \<and> lsx'' = ls \<and> aft'' = nat_of_opt af \<and> sp' = length dr)>"
        by (rule 1(2)[OF Pnxt, THEN mp, OF ante])
      have nxt_val: "nat_of_opt (prnt S stm) = nxt" using prntstm by (simp add: nat_of_opt_def)
      have rvthS1_bef: "nat_of_opt (rvth S1 stm) = the (rvth S stm)" using rvthstm by (cases "rvth S stm") (auto simp: S1_def nat_of_opt_def)
      have Vne: "V \<noteq> {}" using stmV by auto
      have cntdrt: "length drt \<le> card V" using cap fstm by simp
      have rvth3stm_ne: "rvth S3 stm \<noteq> None" using rvthstm by (cases aft) (auto simp: S3_def S2_def S1_def)
      have rvthS3_bef: "nat_of_opt (rvth S3 stm) = the (rvth S3 stm)" using rvth3stm_ne by (cases "rvth S3 stm") (auto simp: nat_of_opt_def)
      have aftS3: "nat_of_opt (thrd S3 lsx') = nat_of_opt aft'" by (simp add: aft'_def)
      have rvth_thrd: "\<And>St x. rvth (St\<lparr>thrd := x\<rparr>) = rvth St" by simp
      have RP: "<ndtree_drt_assn V S Ti sp drt> Array.nth (prnt_impl Ti) stm <\<lambda>r. ndtree_drt_assn V S Ti sp drt * \<up>(r = nxt)>"
        by (sep_auto simp: stmV nxt_val)
      have RR1: "<ndtree_drt_assn V S1 Ti (Suc sp) (drt @ [lsx])> Array.nth (rvth_impl Ti) stm <\<lambda>r. ndtree_drt_assn V S1 Ti (Suc sp) (drt @ [lsx]) * \<up>(r = the (rvth S stm))>"
        by (sep_auto simp: stmV rvthS1_bef)
      have RLa: "<ndtree_drt_assn V S3 Ti (Suc sp) (drt @ [lsx])> Array.nth (lsuc_impl Ti) nxt <\<lambda>r. ndtree_drt_assn V S3 Ti (Suc sp) (drt @ [lsx]) * \<up>(r = lsuc S nxt)>"
        by (sep_auto simp: nxtV lsuc3)
      have RLb: "<ndtree_drt_assn V S3 Ti (Suc sp) (drt @ [lsx])> Array.nth (lsuc_impl Ti) stm <\<lambda>r. ndtree_drt_assn V S3 Ti (Suc sp) (drt @ [lsx]) * \<up>(r = lsuc S stm)>"
        by (sep_auto simp: stmV lsuc3)
      have RT: "<ndtree_drt_assn V S3 Ti (Suc sp) (drt @ [lsx])> Array.nth (thrd_impl Ti) lsx' <\<lambda>r. ndtree_drt_assn V S3 Ti (Suc sp) (drt @ [lsx]) * \<up>(r = nat_of_opt aft')>"
        by (sep_auto simp: lsx'V aftS3)
      have LSX: "<ndtree_drt_assn V S3 Ti (Suc sp) (drt @ [lsx])> (if lsuc S nxt = lsuc S stm then Array.nth (rvth_impl Ti) stm else return (lsuc S nxt)) <\<lambda>r. ndtree_drt_assn V S3 Ti (Suc sp) (drt @ [lsx]) * \<up>(r = lsx')>"
      proof (cases "lsuc S nxt = lsuc S stm")
        case True thus ?thesis by (sep_auto simp: stmV rvthS3_bef lsx'_def lsuc3)
      next
        case False thus ?thesis by (sep_auto simp: lsx'_def lsuc3)
      qed
      show ?thesis
      proof (cases aft)
        case None
        have no_None: "nat_of_opt aft = 0" by (simp add: None nat_of_opt_def)
        have S2N: "S2 = S1\<lparr>thrd := (thrd S1)(the (rvth S stm) := None)\<rparr>" using None by (simp add: S2_def S1_def)
        show ?thesis
          apply (subst stem_loop_imp.simps)
          apply (simp only: if_not_P[OF False] no_None)
          apply (rule ht_bind[OF RP], rule ht_extract_pre_pure, hypsubst)
          apply (rule ht_bind[OF ndtree_drt_upd_thrd_Some[OF lsxV nxtV]], fold S1_def)
          apply (simp only: spd)
          apply (rule ht_bind[OF ndtree_drt_push_aux_cnt[OF finV Vne cntdrt]])
          apply (simp only: spd[symmetric])
          apply (rule ht_bind[OF RR1], rule ht_extract_pre_pure, hypsubst)
          apply (subst if_P[OF refl])
          apply (simp only: bind_bind return_bind)
          apply (rule ht_bind[OF ndtree_drt_upd_thrd_None[OF befV]], fold S2N)
          apply (rule ht_bind[OF ndtree_drt_upd_prnt_Some[OF stmV pstmV]], fold S3_def)
          apply (rule ht_bind[OF RLa], rule ht_extract_pre_pure, hypsubst)
          apply (rule ht_bind[OF RLb], rule ht_extract_pre_pure, hypsubst)
          apply (rule ht_bind[OF LSX], rule ht_extract_pre_pure, hypsubst)
          apply (rule ht_bind[OF RT], rule ht_extract_pre_pure, hypsubst)
          apply (simp only: Suc_eq_plus1[symmetric])
          apply (rule IH[unfolded fstep[symmetric]])
          done
      next
        case (Some a)
        have aV: "a \<in> V" using aftV Some by simp
        have aneq: "a \<noteq> 0" using aV V0 by metis
        have no_Some: "nat_of_opt aft = a" by (simp add: Some nat_of_opt_def)
        have S2S: "S2 = S1\<lparr>thrd := (thrd S1)(the (rvth S stm) \<mapsto> a), rvth := (rvth S1)(a \<mapsto> the (rvth S stm))\<rparr>" using Some by (simp add: S2_def S1_def)
        show ?thesis
          apply (subst stem_loop_imp.simps)
          apply (simp only: if_not_P[OF False] no_Some)
          apply (rule ht_bind[OF RP], rule ht_extract_pre_pure, hypsubst)
          apply (rule ht_bind[OF ndtree_drt_upd_thrd_Some[OF lsxV nxtV]], fold S1_def)
          apply (simp only: spd)
          apply (rule ht_bind[OF ndtree_drt_push_aux_cnt[OF finV Vne cntdrt]])
          apply (simp only: spd[symmetric])
          apply (rule ht_bind[OF RR1], rule ht_extract_pre_pure, hypsubst)
          apply (subst if_not_P[OF aneq])
          apply (simp only: bind_bind return_bind)
          apply (rule ht_bind[OF ndtree_drt_upd_thrd_Some[OF befV aV]])
          apply (rule ht_bind[OF ndtree_drt_upd_rvth[OF aV befV]])
          apply (simp only: rvth_thrd)
          apply (fold S2S)
          apply (rule ht_bind[OF ndtree_drt_upd_prnt_Some[OF stmV pstmV]], fold S3_def)
          apply (rule ht_bind[OF RLa], rule ht_extract_pre_pure, hypsubst)
          apply (rule ht_bind[OF RLb], rule ht_extract_pre_pure, hypsubst)
          apply (rule ht_bind[OF LSX], rule ht_extract_pre_pure, hypsubst)
          apply (rule ht_bind[OF RT], rule ht_extract_pre_pure, hypsubst)
          apply (simp only: Suc_eq_plus1[symmetric])
          apply (rule IH[unfolded fstep[symmetric]])
          done
      qed
    qed
    qed
  qed
qed

text \<open>The path-reversal branch refines its functional twin: the @{const stem_loop} pass (via the aux array,
      refined by @{thm [source] stem_loop_imp_wf}), the parent/thread
      fix-ups, the @{const dirty_pass} refresh, and the @{const stem_num_loop} recomputation.\<close>
text \<open>Functional characterisation of @{const stem_loop}'s effect on @{const prnt}, \<^emph>\<open>without\<close> the stem geometry:
      it only rewrites @{const prnt} on the visited stem (frame), and there it reverses the chain (each visited
      node points back to its predecessor).  These let @{text stem_num_loop_imp_wf} run over the reversed tree
      against the reversed-stem reference, with no @{term "jn = join_of"} needed.\<close>
lemma stem_loop_prnt_frame:
  assumes ps: "parent_spec P"
  shows "(\<forall>v \<in> set (follow P stm). prnt S v = P v) \<and> p \<in> set (follow P stm) \<longrightarrow>
    (\<forall>v. v \<notin> set (follow P stm) \<longrightarrow> prnt (fst (stem_loop S stm pstm lsx aft drt p)) v = prnt S v)"
proof (induction arbitrary: S pstm lsx aft drt rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF ps, of stm]])
  case (1 stm)
  show ?case
  proof (intro impI, elim conjE)
    assume agr: "\<forall>v \<in> set (follow P stm). prnt S v = P v" and pin: "p \<in> set (follow P stm)"
    show "\<forall>v. v \<notin> set (follow P stm) \<longrightarrow> prnt (fst (stem_loop S stm pstm lsx aft drt p)) v = prnt S v"
    proof (intro allI impI)
      fix v assume vnotin: "v \<notin> set (follow P stm)"
      show "prnt (fst (stem_loop S stm pstm lsx aft drt p)) v = prnt S v"
      proof (cases "stm = p")
        case True
        thus ?thesis by (subst stem_loop.simps) simp
      next
        case False
        obtain nxt where Pnxt: "P stm = Some nxt" using pin False by (cases "P stm") (auto simp: follow_ps_simps[OF ps])
        have fstm: "follow P stm = stm # follow P nxt" using Pnxt by (subst follow_ps_simps[OF ps]) simp
        have prntstm: "prnt S stm = Some nxt" using agr fstm Pnxt by auto
        have stmnotin: "stm \<notin> set (follow P nxt)" using fstm follow_distinct_ps[OF ps, of stm] by simp
        have pnxt: "p \<in> set (follow P nxt)" using pin fstm False by auto
        define S1 where "S1 = S\<lparr>thrd := (thrd S)(lsx \<mapsto> nxt)\<rparr>"
        define S2 where "S2 = (case aft of None \<Rightarrow> S1\<lparr>thrd := (thrd S1)(the (rvth S1 stm) := None)\<rparr>
                              | Some a \<Rightarrow> S1\<lparr>thrd := (thrd S1)(the (rvth S1 stm) \<mapsto> a), rvth := (rvth S1)(a \<mapsto> the (rvth S1 stm))\<rparr>)"
        define S3 where "S3 = S2\<lparr>prnt := (prnt S2)(stm \<mapsto> pstm)\<rparr>"
        define lsx' where "lsx' = (if lsuc S3 nxt = lsuc S3 stm then the (rvth S3 stm) else lsuc S3 nxt)"
        define aft' where "aft' = thrd S3 lsx'"
        have fstep: "stem_loop S stm pstm lsx aft drt p = stem_loop S3 nxt stm lsx' aft' (drt @ [lsx]) p"
          using False prntstm by (subst stem_loop.simps) (simp add: S1_def S2_def S3_def lsx'_def aft'_def Let_def cong: if_cong split: option.split)
        have prntS3: "prnt S3 = (prnt S)(stm \<mapsto> pstm)" by (simp add: S3_def S2_def S1_def split: option.split)
        have agr': "\<forall>w \<in> set (follow P nxt). prnt S3 w = P w" using agr fstm stmnotin prntS3 by auto
        have vns1: "v \<noteq> stm" and vns2: "v \<notin> set (follow P nxt)" using vnotin fstm by auto
        have IHrec: "prnt (fst (stem_loop S3 nxt stm lsx' aft' (drt @ [lsx]) p)) v = prnt S3 v"
          using 1(2)[OF Pnxt, THEN mp, OF conjI[OF agr' pnxt]] vns2 by blast
        show ?thesis using fstep IHrec prntS3 vns1 by simp
      qed
    qed
  qed
qed

text \<open>Along the visited stem, @{const stem_loop} reverses @{const prnt}: the head node points back to its
      @{term pstm} (the rest follow by re-applying this to the recursion via the frame lemma).\<close>
lemma stem_loop_prnt_stm:
  assumes ps: "parent_spec P"
  shows "(\<forall>v \<in> set (follow P stm). prnt S v = P v) \<and> p \<in> set (follow P stm) \<and> stm \<noteq> p \<longrightarrow>
    prnt (fst (stem_loop S stm pstm lsx aft drt p)) stm = Some pstm"
proof (intro impI, elim conjE)
  assume agr: "\<forall>v \<in> set (follow P stm). prnt S v = P v" and pin: "p \<in> set (follow P stm)" and stmp: "stm \<noteq> p"
  obtain nxt where Pnxt: "P stm = Some nxt" using pin stmp by (cases "P stm") (auto simp: follow_ps_simps[OF ps])
  have fstm: "follow P stm = stm # follow P nxt" using Pnxt by (subst follow_ps_simps[OF ps]) simp
  have prntstm: "prnt S stm = Some nxt" using agr fstm Pnxt by auto
  have stmnotin: "stm \<notin> set (follow P nxt)" using fstm follow_distinct_ps[OF ps, of stm] by simp
  have pnxt: "p \<in> set (follow P nxt)" using pin fstm stmp by auto
  define S1 where "S1 = S\<lparr>thrd := (thrd S)(lsx \<mapsto> nxt)\<rparr>"
  define S2 where "S2 = (case aft of None \<Rightarrow> S1\<lparr>thrd := (thrd S1)(the (rvth S1 stm) := None)\<rparr>
                        | Some a \<Rightarrow> S1\<lparr>thrd := (thrd S1)(the (rvth S1 stm) \<mapsto> a), rvth := (rvth S1)(a \<mapsto> the (rvth S1 stm))\<rparr>)"
  define S3 where "S3 = S2\<lparr>prnt := (prnt S2)(stm \<mapsto> pstm)\<rparr>"
  define lsx' where "lsx' = (if lsuc S3 nxt = lsuc S3 stm then the (rvth S3 stm) else lsuc S3 nxt)"
  define aft' where "aft' = thrd S3 lsx'"
  have fstep: "stem_loop S stm pstm lsx aft drt p = stem_loop S3 nxt stm lsx' aft' (drt @ [lsx]) p"
    using stmp prntstm by (subst stem_loop.simps) (simp add: S1_def S2_def S3_def lsx'_def aft'_def Let_def cong: if_cong split: option.split)
  have prntS3: "prnt S3 = (prnt S)(stm \<mapsto> pstm)" by (simp add: S3_def S2_def S1_def split: option.split)
  have agr': "\<forall>w \<in> set (follow P nxt). prnt S3 w = P w" using agr fstm stmnotin prntS3 by auto
  have "prnt (fst (stem_loop S3 nxt stm lsx' aft' (drt @ [lsx]) p)) stm = prnt S3 stm"
    using stem_loop_prnt_frame[OF ps, THEN mp, OF conjI[OF agr' pnxt]] stmnotin by blast
  thus "prnt (fst (stem_loop S stm pstm lsx aft drt p)) stm = Some pstm"
    using fstep prntS3 by simp
qed

text \<open>The full reversal: for every visited stem edge \<open>P u = Some w\<close> (with \<open>w\<close> strictly before
      \<open>p\<close>), @{const stem_loop} sets the output's @{const prnt} of \<open>w\<close> to \<open>Some u\<close>.  Together with
      @{thm stem_loop_prnt_stm} (the head) this pins @{const prnt} of the output on the whole visited stem,
      with no geometry.\<close>
lemma stem_loop_prnt_rev:
  assumes ps: "parent_spec P"
  shows "(\<forall>v \<in> set (follow P stm). prnt S v = P v) \<and> p \<in> set (follow P stm) \<longrightarrow>
    (\<forall>u w. u \<in> set (follow P stm) \<and> P u = Some w \<and> p \<in> set (follow P w) \<and> w \<noteq> p \<longrightarrow>
       prnt (fst (stem_loop S stm pstm lsx aft drt p)) w = Some u)"
proof (induction arbitrary: S pstm lsx aft drt rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF ps, of stm]])
  case (1 stm)
  show ?case
  proof (intro impI, elim conjE)
    assume agr: "\<forall>v \<in> set (follow P stm). prnt S v = P v" and pin: "p \<in> set (follow P stm)"
    show "\<forall>u w. u \<in> set (follow P stm) \<and> P u = Some w \<and> p \<in> set (follow P w) \<and> w \<noteq> p \<longrightarrow>
            prnt (fst (stem_loop S stm pstm lsx aft drt p)) w = Some u"
    proof (intro allI impI)
      fix u w assume asm: "u \<in> set (follow P stm) \<and> P u = Some w \<and> p \<in> set (follow P w) \<and> w \<noteq> p"
      have uin: "u \<in> set (follow P stm)" and Puw: "P u = Some w" and pw: "p \<in> set (follow P w)" and wp: "w \<noteq> p" using asm by auto
      have stmp: "stm \<noteq> p"
      proof
        assume e: "stm = p"
        have wf: "w \<in> set (follow P p)" using follow_parent_in_tail[OF ps uin[unfolded e] Puw] by simp
        show False using ancestor_antisym[OF ps wf pw] wp by simp
      qed
      obtain nxt where Pnxt: "P stm = Some nxt" using pin stmp by (cases "P stm") (auto simp: follow_ps_simps[OF ps])
      have fstm: "follow P stm = stm # follow P nxt" using Pnxt by (subst follow_ps_simps[OF ps]) simp
      have prntstm: "prnt S stm = Some nxt" using agr fstm Pnxt by auto
      have stmnotin: "stm \<notin> set (follow P nxt)" using fstm follow_distinct_ps[OF ps, of stm] by simp
      have pnxt: "p \<in> set (follow P nxt)" using pin fstm stmp by auto
      define S1 where "S1 = S\<lparr>thrd := (thrd S)(lsx \<mapsto> nxt)\<rparr>"
      define S2 where "S2 = (case aft of None \<Rightarrow> S1\<lparr>thrd := (thrd S1)(the (rvth S1 stm) := None)\<rparr>
                            | Some a \<Rightarrow> S1\<lparr>thrd := (thrd S1)(the (rvth S1 stm) \<mapsto> a), rvth := (rvth S1)(a \<mapsto> the (rvth S1 stm))\<rparr>)"
      define S3 where "S3 = S2\<lparr>prnt := (prnt S2)(stm \<mapsto> pstm)\<rparr>"
      define lsx' where "lsx' = (if lsuc S3 nxt = lsuc S3 stm then the (rvth S3 stm) else lsuc S3 nxt)"
      define aft' where "aft' = thrd S3 lsx'"
      have fstep: "stem_loop S stm pstm lsx aft drt p = stem_loop S3 nxt stm lsx' aft' (drt @ [lsx]) p"
        using stmp prntstm by (subst stem_loop.simps) (simp add: S1_def S2_def S3_def lsx'_def aft'_def Let_def cong: if_cong split: option.split)
      have prntS3: "prnt S3 = (prnt S)(stm \<mapsto> pstm)" by (simp add: S3_def S2_def S1_def split: option.split)
      have agr': "\<forall>x \<in> set (follow P nxt). prnt S3 x = P x" using agr fstm stmnotin prntS3 by auto
      have poutw: "prnt (fst (stem_loop S stm pstm lsx aft drt p)) w = prnt (fst (stem_loop S3 nxt stm lsx' aft' (drt @ [lsx]) p)) w"
        using fstep by simp
      show "prnt (fst (stem_loop S stm pstm lsx aft drt p)) w = Some u"
      proof (cases "u = stm")
        case True
        hence wnxt: "w = nxt" using Puw Pnxt by simp
        have nxtnep: "nxt \<noteq> p" using wp wnxt by simp
        have ante_nxt: "(\<forall>v \<in> set (follow P nxt). prnt S3 v = P v) \<and> p \<in> set (follow P nxt) \<and> nxt \<noteq> p"
          using agr' pnxt nxtnep by blast
        have "prnt (fst (stem_loop S3 nxt stm lsx' aft' (drt @ [lsx]) p)) nxt = Some stm"
          using stem_loop_prnt_stm[OF ps, THEN mp, OF ante_nxt] by blast
        thus ?thesis using poutw wnxt True by simp
      next
        case False
        have uinnxt: "u \<in> set (follow P nxt)" using uin fstm False by auto
        have "prnt (fst (stem_loop S3 nxt stm lsx' aft' (drt @ [lsx]) p)) w = Some u"
          using 1(2)[OF Pnxt, THEN mp, OF conjI[OF agr' pnxt]] uinnxt Puw pw wp by blast
        thus ?thesis using poutw by simp
      qed
    qed
  qed
qed

text \<open>The reversed-stem \<^emph>\<open>reference\<close> map (sending \<open>s j\<close> to \<open>s (j-1)\<close> along an injective stem sequence,
      undefined at the head) is well-founded --- a finite chain of strictly-decreasing index.  This is the
      well-founded @{const parent_spec} reference that \<open>stem_num_loop_imp_wf\<close> climbs on the reversed tree.\<close>
lemma parent_spec_rev_seq:
  assumes inj: "inj_on s {..k}"
  shows "parent_spec (\<lambda>w. if w \<in> s ` {Suc 0..k} then Some (s (inv_into {..k} s w - 1)) else None)"
  unfolding parent_spec_def
proof (rule wf_subset[OF wf_measure], safe)
  fix x y assume h: "Some x = (if y \<in> s ` {Suc 0..k} then Some (s (inv_into {..k} s y - 1)) else None)"
  hence yin: "y \<in> s ` {Suc 0..k}" by (auto split: if_splits)
  then obtain j where jj: "j \<in> {Suc 0..k}" and yj: "y = s j" by auto
  have jk: "j \<in> {..k}" using jj by auto
  have jm1k: "j - 1 \<in> {..k}" using jj by auto
  have iy: "inv_into {..k} s y = j" using inj jk yj by (simp add: inv_into_f_f)
  have xval: "x = s (j - 1)" using h yin iy by (auto split: if_splits)
  have ix: "inv_into {..k} s x = j - 1" using inj jm1k xval by (simp add: inv_into_f_f)
  show "(x, y) \<in> measure (inv_into {..k} s)" using iy ix jj by simp
qed

text \<open>Membership of @{const stem_loop}'s output tuple: the returned @{term pstm}, @{term lsx}, the @{term aft}
      option's value, and every element of the dirty list stay in @{term V} --- carried by the same \<open>\<in> V\<close>
      invariant as \<open>stem_loop_imp_wf\<close>, but read off the functional result directly.\<close>
lemma stem_loop_out_V:
  assumes ps: "parent_spec P" and ranP: "ran P \<subseteq> V"
  shows "(\<forall>v \<in> set (follow P stm). prnt S v = P v) \<and> p \<in> set (follow P stm) \<and> stm \<in> V \<and> pstm \<in> V \<and> lsx \<in> V \<and> (\<forall>a. aft = Some a \<longrightarrow> a \<in> V) \<and> ran (thrd S) \<subseteq> V \<and> ran (rvth S) \<subseteq> V \<and> (\<forall>v \<in> V. lsuc S v \<in> V) \<and> (\<forall>v \<in> set (follow P stm). p \<in> set (follow P v) \<and> v \<noteq> p \<longrightarrow> rvth S v \<noteq> None) \<and> set drt \<subseteq> V \<longrightarrow>
    (case stem_loop S stm pstm lsx aft drt p of (Sl, pst, ls, af, dr) \<Rightarrow> pst \<in> V \<and> ls \<in> V \<and> (\<forall>a. af = Some a \<longrightarrow> a \<in> V) \<and> set dr \<subseteq> V)"
proof (induction arbitrary: S pstm lsx aft drt rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF ps, of stm]])
  case (1 stm)
  show ?case
  proof (intro impI, elim conjE)
    assume agr: "\<forall>v \<in> set (follow P stm). prnt S v = P v" and pin: "p \<in> set (follow P stm)"
       and stmV: "stm \<in> V" and pstmV: "pstm \<in> V" and lsxV: "lsx \<in> V" and aftV: "\<forall>a. aft = Some a \<longrightarrow> a \<in> V"
       and ranthrd: "ran (thrd S) \<subseteq> V" and ranrvth: "ran (rvth S) \<subseteq> V" and lsucVV: "\<forall>v \<in> V. lsuc S v \<in> V"
       and rvthdef: "\<forall>v \<in> set (follow P stm). p \<in> set (follow P v) \<and> v \<noteq> p \<longrightarrow> rvth S v \<noteq> None" and drtV: "set drt \<subseteq> V"
    show "case stem_loop S stm pstm lsx aft drt p of (Sl, pst, ls, af, dr) \<Rightarrow> pst \<in> V \<and> ls \<in> V \<and> (\<forall>a. af = Some a \<longrightarrow> a \<in> V) \<and> set dr \<subseteq> V"
    proof (cases "stm = p")
      case True
      have "stem_loop S stm pstm lsx aft drt p = (S, pstm, lsx, aft, drt)" using True by (subst stem_loop.simps) simp
      thus ?thesis using pstmV lsxV aftV drtV by simp
    next
      case False
      obtain nxt where Pnxt: "P stm = Some nxt" using pin False by (cases "P stm") (auto simp: follow_ps_simps[OF ps])
      have fstm: "follow P stm = stm # follow P nxt" using Pnxt by (subst follow_ps_simps[OF ps]) simp
      have nxtV: "nxt \<in> V" using ranP Pnxt unfolding ran_def by blast
      have pnxt: "p \<in> set (follow P nxt)" using pin fstm False by auto
      have stmnotin: "stm \<notin> set (follow P nxt)" using fstm follow_distinct_ps[OF ps, of stm] by simp
      have prntstm: "prnt S stm = Some nxt" using agr fstm Pnxt by auto
      have stmin: "stm \<in> set (follow P stm)" using fstm by simp
      have rvthstm: "rvth S stm \<noteq> None" using rvthdef stmin pin False by blast
      have befV: "the (rvth S stm) \<in> V" using rvthstm ranrvth by (cases "rvth S stm") (auto simp: ran_def)
      define S1 where "S1 = S\<lparr>thrd := (thrd S)(lsx \<mapsto> nxt)\<rparr>"
      define S2 where "S2 = (case aft of None \<Rightarrow> S1\<lparr>thrd := (thrd S1)(the (rvth S1 stm) := None)\<rparr>
                            | Some a \<Rightarrow> S1\<lparr>thrd := (thrd S1)(the (rvth S1 stm) \<mapsto> a), rvth := (rvth S1)(a \<mapsto> the (rvth S1 stm))\<rparr>)"
      define S3 where "S3 = S2\<lparr>prnt := (prnt S2)(stm \<mapsto> pstm)\<rparr>"
      define lsx' where "lsx' = (if lsuc S3 nxt = lsuc S3 stm then the (rvth S3 stm) else lsuc S3 nxt)"
      define aft' where "aft' = thrd S3 lsx'"
      have fstep: "stem_loop S stm pstm lsx aft drt p = stem_loop S3 nxt stm lsx' aft' (drt @ [lsx]) p"
        using False prntstm by (subst stem_loop.simps) (simp add: S1_def S2_def S3_def lsx'_def aft'_def Let_def cong: if_cong split: option.split)
      have ranthrd3: "ran (thrd S3) \<subseteq> V" using ranthrd nxtV aftV by (cases aft) (auto simp: S3_def S2_def S1_def ran_def)
      have ranrvth3: "ran (rvth S3) \<subseteq> V" using ranrvth befV by (cases aft) (auto simp: S3_def S2_def S1_def ran_def)
      have lsuc3: "lsuc S3 = lsuc S" by (simp add: S3_def S2_def S1_def split: option.split)
      have rvth3stmV: "the (rvth S3 stm) \<in> V" using rvthstm befV ranrvth by (cases aft) (auto simp: S3_def S2_def S1_def ran_def)
      have lsx'V: "lsx' \<in> V" using rvth3stmV lsucVV nxtV lsuc3 by (auto simp: lsx'_def)
      have aft'V: "\<forall>a. aft' = Some a \<longrightarrow> a \<in> V" using ranthrd3 by (auto simp: aft'_def ran_def)
      have rvthdef3: "\<forall>v \<in> set (follow P nxt). p \<in> set (follow P v) \<and> v \<noteq> p \<longrightarrow> rvth S3 v \<noteq> None"
        using rvthdef fstm by (cases aft) (auto simp: S3_def S2_def S1_def)
      have prntS3: "prnt S3 = (prnt S)(stm \<mapsto> pstm)" by (simp add: S3_def S2_def S1_def split: option.split)
      have agr': "\<forall>v \<in> set (follow P nxt). prnt S3 v = P v" using agr fstm stmnotin prntS3 by auto
      have lsucVV3: "\<forall>v \<in> V. lsuc S3 v \<in> V" using lsucVV lsuc3 by simp
      have ante: "(\<forall>v \<in> set (follow P nxt). prnt S3 v = P v) \<and> p \<in> set (follow P nxt) \<and> nxt \<in> V \<and> stm \<in> V \<and> lsx' \<in> V \<and> (\<forall>a. aft' = Some a \<longrightarrow> a \<in> V) \<and> ran (thrd S3) \<subseteq> V \<and> ran (rvth S3) \<subseteq> V \<and> (\<forall>v \<in> V. lsuc S3 v \<in> V) \<and> (\<forall>v \<in> set (follow P nxt). p \<in> set (follow P v) \<and> v \<noteq> p \<longrightarrow> rvth S3 v \<noteq> None) \<and> set (drt @ [lsx]) \<subseteq> V"
        using agr' pnxt nxtV stmV lsx'V aft'V ranthrd3 ranrvth3 lsucVV3 rvthdef3 drtV lsxV by auto
      have "case stem_loop S3 nxt stm lsx' aft' (drt @ [lsx]) p of (Sl, pst, ls, af, dr) \<Rightarrow> pst \<in> V \<and> ls \<in> V \<and> (\<forall>a. af = Some a \<longrightarrow> a \<in> V) \<and> set dr \<subseteq> V"
        by (rule 1(2)[OF Pnxt, THEN mp, OF ante])
      thus ?thesis using fstep by simp
    qed
  qed
qed

text \<open>The returned @{term pstm} of @{const stem_loop} is the node just before @{term p} on the stem (the unique
      predecessor @{term u} with @{term "P u = Some p"}).  This makes the reversed-stem reference chain connect at
      @{term p}: \<open>prnt St p = pstm = s (k-1)\<close>.\<close>
lemma stem_loop_ret:
  assumes ps: "parent_spec P"
  shows "(\<forall>v \<in> set (follow P stm). prnt S v = P v) \<and> p \<in> set (follow P stm) \<and> stm \<noteq> p \<longrightarrow>
    (\<exists>u. u \<in> set (follow P stm) \<and> P u = Some p \<and> fst (snd (stem_loop S stm pstm lsx aft drt p)) = u)"
proof (induction arbitrary: S pstm lsx aft drt rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF ps, of stm]])
  case (1 stm)
  show ?case
  proof (intro impI, elim conjE)
    assume agr: "\<forall>v \<in> set (follow P stm). prnt S v = P v" and pin: "p \<in> set (follow P stm)" and stmp: "stm \<noteq> p"
    obtain nxt where Pnxt: "P stm = Some nxt" using pin stmp by (cases "P stm") (auto simp: follow_ps_simps[OF ps])
    have fstm: "follow P stm = stm # follow P nxt" using Pnxt by (subst follow_ps_simps[OF ps]) simp
    have prntstm: "prnt S stm = Some nxt" using agr fstm Pnxt by auto
    have stmnotin: "stm \<notin> set (follow P nxt)" using fstm follow_distinct_ps[OF ps, of stm] by simp
    define S1 where "S1 = S\<lparr>thrd := (thrd S)(lsx \<mapsto> nxt)\<rparr>"
    define S2 where "S2 = (case aft of None \<Rightarrow> S1\<lparr>thrd := (thrd S1)(the (rvth S1 stm) := None)\<rparr>
                          | Some a \<Rightarrow> S1\<lparr>thrd := (thrd S1)(the (rvth S1 stm) \<mapsto> a), rvth := (rvth S1)(a \<mapsto> the (rvth S1 stm))\<rparr>)"
    define S3 where "S3 = S2\<lparr>prnt := (prnt S2)(stm \<mapsto> pstm)\<rparr>"
    define lsx' where "lsx' = (if lsuc S3 nxt = lsuc S3 stm then the (rvth S3 stm) else lsuc S3 nxt)"
    define aft' where "aft' = thrd S3 lsx'"
    have fstep: "stem_loop S stm pstm lsx aft drt p = stem_loop S3 nxt stm lsx' aft' (drt @ [lsx]) p"
      using stmp prntstm by (subst stem_loop.simps) (simp add: S1_def S2_def S3_def lsx'_def aft'_def Let_def cong: if_cong split: option.split)
    have prntS3: "prnt S3 = (prnt S)(stm \<mapsto> pstm)" by (simp add: S3_def S2_def S1_def split: option.split)
    have agr': "\<forall>v \<in> set (follow P nxt). prnt S3 v = P v" using agr fstm stmnotin prntS3 by auto
    have pnxt: "p \<in> set (follow P nxt)" using pin fstm stmp by auto
    show "\<exists>u. u \<in> set (follow P stm) \<and> P u = Some p \<and> fst (snd (stem_loop S stm pstm lsx aft drt p)) = u"
    proof (cases "nxt = p")
      case True
      have base: "stem_loop S3 nxt stm lsx' aft' (drt @ [lsx]) p = (S3, stm, lsx', aft', drt @ [lsx])"
        using True by (subst stem_loop.simps) simp
      have "fst (snd (stem_loop S stm pstm lsx aft drt p)) = stm" using fstep base by simp
      moreover have "P stm = Some p" using Pnxt True by simp
      moreover have "stm \<in> set (follow P stm)" using fstm by simp
      ultimately show ?thesis by blast
    next
      case False
      have ante: "(\<forall>v \<in> set (follow P nxt). prnt S3 v = P v) \<and> p \<in> set (follow P nxt) \<and> nxt \<noteq> p"
        using agr' pnxt False by blast
      obtain u where u: "u \<in> set (follow P nxt) \<and> P u = Some p \<and> fst (snd (stem_loop S3 nxt stm lsx' aft' (drt @ [lsx]) p)) = u"
        using 1(2)[OF Pnxt, THEN mp, OF ante] by blast
      have "u \<in> set (follow P stm)" using u fstm by simp
      moreover have "fst (snd (stem_loop S stm pstm lsx aft drt p)) = u" using fstep u by simp
      ultimately show ?thesis using u by blast
    qed
  qed
qed

text \<open>On a @{const follow} path (a simple parent-chain), a node's predecessor is unique: two elements with the
      same parent coincide.  This pins \<open>pst = s (k-1)\<close> (the returned @{term pstm} is exactly the stem node
      just below @{term p}), so the reversed-stem reference agrees with the reversed tree at @{term p}.\<close>
lemma follow_pred_unique:
  assumes ps: "parent_spec P"
  shows "x \<in> set (follow P u) \<and> y \<in> set (follow P u) \<and> P x = Some z \<and> P y = Some z \<longrightarrow> x = y"
proof (induction arbitrary: x y z rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF ps, of u]])
  case (1 u)
  show ?case
  proof (intro impI, elim conjE)
    assume xin: "x \<in> set (follow P u)" and yin: "y \<in> set (follow P u)" and px: "P x = Some z" and py: "P y = Some z"
    show "x = y"
    proof (cases "P u")
      case None
      hence "follow P u = [u]" by (subst follow_ps_simps[OF ps]) simp
      thus ?thesis using xin yin by simp
    next
      case (Some w)
      have fu: "follow P u = u # follow P w" using Some by (subst follow_ps_simps[OF ps]) simp
      have contra: "\<And>a. a \<in> set (follow P w) \<Longrightarrow> P a = Some w \<Longrightarrow> False"
        using follow_parent_in_tail[OF ps] by blast
      have xcase: "x = u \<or> x \<in> set (follow P w)" using xin fu by auto
      have ycase: "y = u \<or> y \<in> set (follow P w)" using yin fu by auto
      show "x = y"
      proof (cases "x = u")
        case True
        hence zw: "z = w" using px Some by simp
        have "y = u"
        proof (rule ccontr)
          assume "y \<noteq> u"
          hence "y \<in> set (follow P w)" using ycase by simp
          moreover have "P y = Some w" using py zw by simp
          ultimately show False using contra by blast
        qed
        thus ?thesis using True by simp
      next
        case False
        hence xw: "x \<in> set (follow P w)" using xcase by simp
        have "y \<noteq> u"
        proof
          assume "y = u"
          hence "z = w" using py Some by simp
          hence "P x = Some w" using px by simp
          thus False using xw contra by blast
        qed
        hence yw: "y \<in> set (follow P w)" using ycase by simp
        show ?thesis using 1(2)[OF Some] xw yw px py by blast
      qed
    qed
  qed
qed

text \<open>Along a parent-sequence \<open>s\<close> (with \<open>P (s t) = Some (s (Suc t))\<close>), the endpoint \<open>s k\<close> is reachable
      from every earlier node \<open>s t\<close> --- i.e. \<open>s k \<in> follow P (s t)\<close>.  Used to place \<open>p\<close> on the stem for
      the reversal-edge lemma.\<close>
lemma seq_p_in_follow:
  assumes ps: "parent_spec P" and step: "\<forall>t<k. P (s t) = Some (s (Suc t))"
  shows "t \<le> k \<longrightarrow> s k \<in> set (follow P (s t))"
proof (induction "k - t" arbitrary: t)
  case 0
  show ?case
  proof (intro impI)
    assume "t \<le> k"
    hence "t = k" using 0 by simp
    thus "s k \<in> set (follow P (s t))" by (subst follow_ps_simps[OF ps]) (simp split: option.split)
  qed
next
  case (Suc d)
  show ?case
  proof (intro impI)
    assume tk: "t \<le> k"
    have tltk: "t < k" using Suc.hyps(2) tk by simp
    have pst: "P (s t) = Some (s (Suc t))" using step tltk by simp
    have "k - Suc t = d" using Suc.hyps(2) by simp
    hence "s k \<in> set (follow P (s (Suc t)))" using Suc.hyps(1)[of "Suc t"] tltk by simp
    thus "s k \<in> set (follow P (s t))" using pst by (subst follow_ps_simps[OF ps]) simp
  qed
qed

text \<open>Every node on a @{const follow} climb is either the start or a parent-value: \<open>follow P u \<subseteq> {u} \<union> ran P\<close>.
      Instantiated at @{term P_snl} this confines @{term "follow P_snl p"} to the stem \<open>s ` {..k}\<close>.\<close>
lemma follow_ran_subset:
  assumes ps: "parent_spec P"
  shows "set (follow P u) \<subseteq> insert u (ran P)"
proof (induction rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF ps, of u]])
  case (1 u)
  show ?case
  proof (cases "P u")
    case None
    thus ?thesis by (subst follow_ps_simps[OF ps]) simp
  next
    case (Some w)
    have fu: "follow P u = u # follow P w" using Some by (subst follow_ps_simps[OF ps]) simp
    have win: "w \<in> ran P" using Some by (auto simp: ran_def)
    have "set (follow P w) \<subseteq> insert w (ran P)" using 1(2)[OF Some] .
    also have "insert w (ran P) = ran P" using win by auto
    finally have "set (follow P w) \<subseteq> ran P" .
    thus ?thesis using fu by auto
  qed
qed

text \<open>@{const dirty_pass} only rewrites @{const rvth}, so @{const prnt}, @{const snum}, @{const lsuc} and
      @{const thrd} pass through unchanged --- letting us read \<open>prnt St\<close> / \<open>lsuc St\<close> / \<open>snum St\<close> off the
      pre-@{const dirty_pass} state.\<close>
lemma dirty_pass_keeps:
  "prnt (dirty_pass S drt) = prnt S \<and> snum (dirty_pass S drt) = snum S \<and> lsuc (dirty_pass S drt) = lsuc S \<and> thrd (dirty_pass S drt) = thrd S"
  unfolding dirty_pass_def
  by (induction drt arbitrary: S) (auto split: option.split)

text \<open>@{const stem_loop} rewrites only @{const thrd}/@{const rvth}/@{const prnt}, so @{const snum} passes through
      it unchanged.  Combined with @{thm[source] dirty_pass_keeps} this makes the SNL \<open>snum\<close>-invariant trivial:
      \<open>snum St = snum S0\<close>.\<close>
lemma stem_loop_snum:
  assumes ps: "parent_spec P"
  shows "(\<forall>v \<in> set (follow P stm). prnt S v = P v) \<and> p \<in> set (follow P stm) \<longrightarrow>
    snum (fst (stem_loop S stm pstm lsx aft drt p)) = snum S"
proof (induction arbitrary: S pstm lsx aft drt rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF ps, of stm]])
  case (1 stm)
  show ?case
  proof (intro impI, elim conjE)
    assume agr: "\<forall>v \<in> set (follow P stm). prnt S v = P v" and pin: "p \<in> set (follow P stm)"
    show "snum (fst (stem_loop S stm pstm lsx aft drt p)) = snum S"
    proof (cases "stm = p")
      case True
      thus ?thesis by (subst stem_loop.simps) simp
    next
      case False
      obtain nxt where Pnxt: "P stm = Some nxt" using pin False by (cases "P stm") (auto simp: follow_ps_simps[OF ps])
      have fstm: "follow P stm = stm # follow P nxt" using Pnxt by (subst follow_ps_simps[OF ps]) simp
      have prntstm: "prnt S stm = Some nxt" using agr fstm Pnxt by auto
      have stmnotin: "stm \<notin> set (follow P nxt)" using fstm follow_distinct_ps[OF ps, of stm] by simp
      have pnxt: "p \<in> set (follow P nxt)" using pin fstm False by auto
      define S1 where "S1 = S\<lparr>thrd := (thrd S)(lsx \<mapsto> nxt)\<rparr>"
      define S2 where "S2 = (case aft of None \<Rightarrow> S1\<lparr>thrd := (thrd S1)(the (rvth S1 stm) := None)\<rparr>
                            | Some a \<Rightarrow> S1\<lparr>thrd := (thrd S1)(the (rvth S1 stm) \<mapsto> a), rvth := (rvth S1)(a \<mapsto> the (rvth S1 stm))\<rparr>)"
      define S3 where "S3 = S2\<lparr>prnt := (prnt S2)(stm \<mapsto> pstm)\<rparr>"
      define lsx' where "lsx' = (if lsuc S3 nxt = lsuc S3 stm then the (rvth S3 stm) else lsuc S3 nxt)"
      define aft' where "aft' = thrd S3 lsx'"
      have fstep: "stem_loop S stm pstm lsx aft drt p = stem_loop S3 nxt stm lsx' aft' (drt @ [lsx]) p"
        using False prntstm by (subst stem_loop.simps) (simp add: S1_def S2_def S3_def lsx'_def aft'_def Let_def cong: if_cong split: option.split)
      have snumS3: "snum S3 = snum S" by (simp add: S3_def S2_def S1_def split: option.split)
      have prntS3: "prnt S3 = (prnt S)(stm \<mapsto> pstm)" by (simp add: S3_def S2_def S1_def split: option.split)
      have agr': "\<forall>w \<in> set (follow P nxt). prnt S3 w = P w" using agr fstm stmnotin prntS3 by auto
      have IHrec: "snum (fst (stem_loop S3 nxt stm lsx' aft' (drt @ [lsx]) p)) = snum S3"
        using 1(2)[OF Pnxt, THEN mp, OF conjI[OF agr' pnxt]] by blast
      show ?thesis using fstep IHrec snumS3 by simp
    qed
  qed
qed

text \<open>Companion to @{thm[source] stem_loop_out_V}: under the same precondition the output state's @{const thrd}
      and @{const rvth} ranges also stay within @{term V}.  Needed for \<open>ran (thrd Ss) \<subseteq> V\<close>, the side-condition
      of @{text dirty_pass_imp_rule} in the op-thread.\<close>
lemma stem_loop_ran_thrd:
  assumes ps: "parent_spec P" and ranP: "ran P \<subseteq> V"
  shows "(\<forall>v \<in> set (follow P stm). prnt S v = P v) \<and> p \<in> set (follow P stm) \<and> stm \<in> V \<and> pstm \<in> V \<and> lsx \<in> V \<and> (\<forall>a. aft = Some a \<longrightarrow> a \<in> V) \<and> ran (thrd S) \<subseteq> V \<and> ran (rvth S) \<subseteq> V \<and> (\<forall>v \<in> V. lsuc S v \<in> V) \<and> (\<forall>v \<in> set (follow P stm). p \<in> set (follow P v) \<and> v \<noteq> p \<longrightarrow> rvth S v \<noteq> None) \<and> set drt \<subseteq> V \<longrightarrow>
    ran (thrd (fst (stem_loop S stm pstm lsx aft drt p))) \<subseteq> V \<and> ran (rvth (fst (stem_loop S stm pstm lsx aft drt p))) \<subseteq> V"
proof (induction arbitrary: S pstm lsx aft drt rule: parent_spec_i.follow.pinduct[OF follow_dom_ps[OF ps, of stm]])
  case (1 stm)
  show ?case
  proof (intro impI, elim conjE)
    assume agr: "\<forall>v \<in> set (follow P stm). prnt S v = P v" and pin: "p \<in> set (follow P stm)"
       and stmV: "stm \<in> V" and pstmV: "pstm \<in> V" and lsxV: "lsx \<in> V" and aftV: "\<forall>a. aft = Some a \<longrightarrow> a \<in> V"
       and ranthrd: "ran (thrd S) \<subseteq> V" and ranrvth: "ran (rvth S) \<subseteq> V" and lsucVV: "\<forall>v \<in> V. lsuc S v \<in> V"
       and rvthdef: "\<forall>v \<in> set (follow P stm). p \<in> set (follow P v) \<and> v \<noteq> p \<longrightarrow> rvth S v \<noteq> None" and drtV: "set drt \<subseteq> V"
    show "ran (thrd (fst (stem_loop S stm pstm lsx aft drt p))) \<subseteq> V \<and> ran (rvth (fst (stem_loop S stm pstm lsx aft drt p))) \<subseteq> V"
    proof (cases "stm = p")
      case True
      have "stem_loop S stm pstm lsx aft drt p = (S, pstm, lsx, aft, drt)" using True by (subst stem_loop.simps) simp
      thus ?thesis using ranthrd ranrvth by simp
    next
      case False
      obtain nxt where Pnxt: "P stm = Some nxt" using pin False by (cases "P stm") (auto simp: follow_ps_simps[OF ps])
      have fstm: "follow P stm = stm # follow P nxt" using Pnxt by (subst follow_ps_simps[OF ps]) simp
      have nxtV: "nxt \<in> V" using ranP Pnxt unfolding ran_def by blast
      have pnxt: "p \<in> set (follow P nxt)" using pin fstm False by auto
      have stmnotin: "stm \<notin> set (follow P nxt)" using fstm follow_distinct_ps[OF ps, of stm] by simp
      have prntstm: "prnt S stm = Some nxt" using agr fstm Pnxt by auto
      have stmin: "stm \<in> set (follow P stm)" using fstm by simp
      have rvthstm: "rvth S stm \<noteq> None" using rvthdef stmin pin False by blast
      have befV: "the (rvth S stm) \<in> V" using rvthstm ranrvth by (cases "rvth S stm") (auto simp: ran_def)
      define S1 where "S1 = S\<lparr>thrd := (thrd S)(lsx \<mapsto> nxt)\<rparr>"
      define S2 where "S2 = (case aft of None \<Rightarrow> S1\<lparr>thrd := (thrd S1)(the (rvth S1 stm) := None)\<rparr>
                            | Some a \<Rightarrow> S1\<lparr>thrd := (thrd S1)(the (rvth S1 stm) \<mapsto> a), rvth := (rvth S1)(a \<mapsto> the (rvth S1 stm))\<rparr>)"
      define S3 where "S3 = S2\<lparr>prnt := (prnt S2)(stm \<mapsto> pstm)\<rparr>"
      define lsx' where "lsx' = (if lsuc S3 nxt = lsuc S3 stm then the (rvth S3 stm) else lsuc S3 nxt)"
      define aft' where "aft' = thrd S3 lsx'"
      have fstep: "stem_loop S stm pstm lsx aft drt p = stem_loop S3 nxt stm lsx' aft' (drt @ [lsx]) p"
        using False prntstm by (subst stem_loop.simps) (simp add: S1_def S2_def S3_def lsx'_def aft'_def Let_def cong: if_cong split: option.split)
      have ranthrd3: "ran (thrd S3) \<subseteq> V" using ranthrd nxtV aftV by (cases aft) (auto simp: S3_def S2_def S1_def ran_def)
      have ranrvth3: "ran (rvth S3) \<subseteq> V" using ranrvth befV by (cases aft) (auto simp: S3_def S2_def S1_def ran_def)
      have lsuc3: "lsuc S3 = lsuc S" by (simp add: S3_def S2_def S1_def split: option.split)
      have rvth3stmV: "the (rvth S3 stm) \<in> V" using rvthstm befV ranrvth by (cases aft) (auto simp: S3_def S2_def S1_def ran_def)
      have lsx'V: "lsx' \<in> V" using rvth3stmV lsucVV nxtV lsuc3 by (auto simp: lsx'_def)
      have aft'V: "\<forall>a. aft' = Some a \<longrightarrow> a \<in> V" using ranthrd3 by (auto simp: aft'_def ran_def)
      have rvthdef3: "\<forall>v \<in> set (follow P nxt). p \<in> set (follow P v) \<and> v \<noteq> p \<longrightarrow> rvth S3 v \<noteq> None"
        using rvthdef fstm by (cases aft) (auto simp: S3_def S2_def S1_def)
      have prntS3: "prnt S3 = (prnt S)(stm \<mapsto> pstm)" by (simp add: S3_def S2_def S1_def split: option.split)
      have agr': "\<forall>v \<in> set (follow P nxt). prnt S3 v = P v" using agr fstm stmnotin prntS3 by auto
      have lsucVV3: "\<forall>v \<in> V. lsuc S3 v \<in> V" using lsucVV lsuc3 by simp
      have ante: "(\<forall>v \<in> set (follow P nxt). prnt S3 v = P v) \<and> p \<in> set (follow P nxt) \<and> nxt \<in> V \<and> stm \<in> V \<and> lsx' \<in> V \<and> (\<forall>a. aft' = Some a \<longrightarrow> a \<in> V) \<and> ran (thrd S3) \<subseteq> V \<and> ran (rvth S3) \<subseteq> V \<and> (\<forall>v \<in> V. lsuc S3 v \<in> V) \<and> (\<forall>v \<in> set (follow P nxt). p \<in> set (follow P v) \<and> v \<noteq> p \<longrightarrow> rvth S3 v \<noteq> None) \<and> set (drt @ [lsx]) \<subseteq> V"
        using agr' pnxt nxtV stmV lsx'V aft'V ranthrd3 ranrvth3 lsucVV3 rvthdef3 drtV lsxV by auto
      have "ran (thrd (fst (stem_loop S3 nxt stm lsx' aft' (drt @ [lsx]) p))) \<subseteq> V \<and> ran (rvth (fst (stem_loop S3 nxt stm lsx' aft' (drt @ [lsx]) p))) \<subseteq> V"
        by (rule 1(2)[OF Pnxt, THEN mp, OF ante])
      thus ?thesis using fstep by simp
    qed
  qed
qed

lemma UT_reversal:
  fixes S0 :: "nat ndtree"
  assumes arb: "arb_invar r V S0" and iV: "i \<in> V" and jV: "j \<in> V"
      and pi: "p \<in> set (follow (prnt S0) i)"
      and pnr: "p \<noteq> r"
      and ipne: "i \<noteq> p"
      and old_rev_def: "old_rev = the (rvth S0 p)"
      and old_num_def: "old_num = snum S0 p"
      and old_last_def: "old_last = lsuc S0 p"
  shows "<ndtree_assn V S0 Ti> ut_reversal_imp Ti i j p old_rev old_num old_last
   <\<lambda>_. ndtree_assn V (ut_reversal_fun S0 i j p old_rev old_num old_last) Ti>"
proof(subst zero_not_in_V_ndtree_assn_extract, rule impI, goal_cases)
  case 1
  note V0 = this
  have rinv: "rooted_arborescense_invar r V (prnt S0)" using arb by (simp add: arb_invar_def)
  have ps0: "parent_spec (prnt S0)" using rinv by (rule rooted_arborescense_invar_parent_spec)
  have pV: "p \<in> V" using pi follow_subset_V[OF rinv iV] by auto
  have lsucVV0: "\<forall>v \<in> V. lsuc S0 v \<in> V" using arb by (simp add: arb_invar_def)
  have domR0: "dom (rvth S0) = V - {r}" using arb by (simp add: arb_invar_def)
  have bij0: "\<forall>v v'. thrd S0 v = Some v' \<longleftrightarrow> rvth S0 v' = Some v" using arb by (simp add: arb_invar_def)
  have domT0: "dom (thrd S0) = V - {lsuc S0 r}" using arb by (simp add: arb_invar_def)
  have finV: "finite V" using arb by (auto simp: arb_invar_def)
  have ranT0: "ran (thrd S0) \<subseteq> V"
  proof
    fix w assume "w \<in> ran (thrd S0)"
    then obtain v where "thrd S0 v = Some w" by (auto simp: ran_def)
    hence "rvth S0 w = Some v" using bij0 by blast
    thus "w \<in> V" using domR0 by (auto simp: dom_def)
  qed
  have ranR0: "ran (rvth S0) \<subseteq> V"
  proof
    fix w assume "w \<in> ran (rvth S0)"
    then obtain v where "rvth S0 v = Some w" by (auto simp: ran_def)
    hence "thrd S0 w = Some v" using bij0 by blast
    thus "w \<in> V" using domT0 by (auto simp: dom_def)
  qed
  have ranP0: "ran (prnt S0) \<subseteq> V"
  proof
    fix z assume "z \<in> ran (prnt S0)"
    then obtain y0 where "prnt S0 y0 = Some z" by (auto simp: ran_def)
    hence "(y0, z) \<in> {(y, x) |x y. Some x = prnt S0 y}" by auto
    hence "z \<in> dVs {(y, x) |x y. Some x = prnt S0 y}" by (rule dVsI(2))
    thus "z \<in> V" using rinv rooted_arborescense_invar_dVs by blast
  qed
  have prntrN: "prnt S0 r = None" using rooted_arborescense_invar_dom[OF rinv] by (auto simp: dom_def)
  have lsx0V: "lsuc S0 i \<in> V" using lsucVV0 iV by auto
  have old_lastV: "old_last \<in> V" using lsucVV0 pV old_last_def by simp
  have rvthpN: "rvth S0 p \<noteq> None" using pV pnr domR0 by (auto simp: dom_def)
  have old_revV: "old_rev \<in> V" using rvthpN ranR0 old_rev_def by (cases "rvth S0 p") (auto simp: ran_def)
  have tcV: "\<And>a. (if old_rev = j then thrd S0 old_last else thrd S0 j) = Some a \<Longrightarrow> a \<in> V"
    using ranT0 by (cases "old_rev = j") (auto simp: ran_def)
  define Sinit where "Sinit = S0\<lparr>thrd := (thrd S0)(j \<mapsto> i)\<rparr>"
  have prntSinit: "prnt Sinit = prnt S0" by (simp add: Sinit_def)
  have rvthSinit: "rvth Sinit = rvth S0" by (simp add: Sinit_def)
  obtain Sl pst ls af dr where steq: "stem_loop Sinit i j (lsuc S0 i) (thrd S0 (lsuc S0 i)) [j] p = (Sl, pst, ls, af, dr)"
    by (cases "stem_loop Sinit i j (lsuc S0 i) (thrd S0 (lsuc S0 i)) [j] p") auto
  have agr0: "\<forall>v \<in> set (follow (prnt S0) i). prnt Sinit v = prnt S0 v" by (simp add: prntSinit)
  have EX: "\<exists>s k. s 0 = i \<and> s k = p \<and> (\<forall>t<k. prnt S0 (s t) = Some (s (Suc t))) \<and> inj_on s {..k} \<and> (\<forall>t\<le>k. s t \<in> set (follow (prnt S0) i))"
    by (rule follow_path[OF ps0 pi]) auto
  obtain s k where s0: "s 0 = i" and sk: "s k = p" and step: "\<forall>t<k. prnt S0 (s t) = Some (s (Suc t))"
    and inj: "inj_on s {..k}" and smem: "\<forall>t\<le>k. s t \<in> set (follow (prnt S0) i)"
    using EX by blast
  have kpos: "0 < k" using ipne s0 sk by (cases k) auto
  define P_snl where "P_snl = (\<lambda>w. if w \<in> s ` {Suc 0..k} then Some (s (inv_into {..k} s w - 1)) else None)"
  have psN: "parent_spec P_snl" unfolding P_snl_def by (rule parent_spec_rev_seq[OF inj])
  have Psnl_val: "\<And>t. t \<in> {Suc 0..k} \<Longrightarrow> P_snl (s t) = Some (s (t - 1))"
  proof -
    fix t assume t: "t \<in> {Suc 0..k}"
    have "inv_into {..k} s (s t) = t" using inj t by (simp add: inv_into_f_f)
    thus "P_snl (s t) = Some (s (t - 1))" using t by (simp add: P_snl_def)
  qed
  have ranPsnlS: "ran P_snl \<subseteq> s ` {..k}"
  proof
    fix z assume "z \<in> ran P_snl"
    then obtain w where "P_snl w = Some z" by (auto simp: ran_def)
    then obtain t where t: "t \<in> {Suc 0..k}" and "w = s t" and "z = s (inv_into {..k} s w - 1)" by (auto simp: P_snl_def split: if_splits)
    hence "z = s (t - 1)" using inj t by (auto simp: inv_into_f_f)
    moreover have "t - 1 \<le> k" using t by auto
    ultimately show "z \<in> s ` {..k}" by auto
  qed
  have ranPsnl: "ran P_snl \<subseteq> V" using ranPsnlS smem follow_subset_V[OF rinv iV] by auto
  have retante: "(\<forall>v \<in> set (follow (prnt S0) i). prnt Sinit v = prnt S0 v) \<and> p \<in> set (follow (prnt S0) i) \<and> i \<noteq> p"
    using agr0 pi ipne by blast
  have retpst: "\<exists>u. u \<in> set (follow (prnt S0) i) \<and> prnt S0 u = Some p \<and> pst = u"
    using stem_loop_ret[OF ps0, where S = Sinit and stm = i and pstm = j and lsx = "lsuc S0 i" and aft = "thrd S0 (lsuc S0 i)" and drt = "[j]", THEN mp, OF retante] steq by auto
  have skm1: "prnt S0 (s (k - 1)) = Some p" using step kpos sk by (metis Suc_diff_1 diff_less less_numeral_extra(1))
  have skm1mem: "s (k - 1) \<in> set (follow (prnt S0) i)" using smem by auto
  have pstsk: "pst = s (k - 1)"
  proof -
    obtain u where u: "u \<in> set (follow (prnt S0) i)" "prnt S0 u = Some p" "pst = u" using retpst by blast
    have "u = s (k - 1)" using follow_pred_unique[OF ps0] u(1) skm1mem u(2) skm1 by blast
    thus ?thesis using u(3) by simp
  qed
  have rvthdef0: "\<forall>v \<in> set (follow (prnt S0) i). p \<in> set (follow (prnt S0) v) \<and> v \<noteq> p \<longrightarrow> rvth Sinit v \<noteq> None"
  proof (intro ballI impI, elim conjE)
    fix v assume vin: "v \<in> set (follow (prnt S0) i)" and pv: "p \<in> set (follow (prnt S0) v)" and vp: "v \<noteq> p"
    have vV: "v \<in> V" using vin follow_subset_V[OF rinv iV] by auto
    have "v \<noteq> r"
    proof
      assume vr: "v = r"
      have "follow (prnt S0) v = [r]" using prntrN vr by (subst follow_ps_simps[OF ps0]) simp
      thus False using pv vr pnr by simp
    qed
    hence "v \<in> dom (rvth S0)" using vV domR0 by auto
    thus "rvth Sinit v \<noteq> None" using rvthSinit by (auto simp: dom_def)
  qed
  have outpre: "(\<forall>v \<in> set (follow (prnt S0) i). prnt Sinit v = prnt S0 v) \<and> p \<in> set (follow (prnt S0) i) \<and> i \<in> V \<and> j \<in> V \<and> lsuc S0 i \<in> V \<and> (\<forall>a. thrd S0 (lsuc S0 i) = Some a \<longrightarrow> a \<in> V) \<and> ran (thrd Sinit) \<subseteq> V \<and> ran (rvth Sinit) \<subseteq> V \<and> (\<forall>v \<in> V. lsuc Sinit v \<in> V) \<and> (\<forall>v \<in> set (follow (prnt S0) i). p \<in> set (follow (prnt S0) v) \<and> v \<noteq> p \<longrightarrow> rvth Sinit v \<noteq> None) \<and> set [j] \<subseteq> V"
    using pi iV jV lsx0V ranT0 ranR0 lsucVV0 rvthdef0 by (auto simp: prntSinit rvthSinit Sinit_def ran_def)
  have memb: "case stem_loop Sinit i j (lsuc S0 i) (thrd S0 (lsuc S0 i)) [j] p of (Sl, pst, ls, af, dr) \<Rightarrow> pst \<in> V \<and> ls \<in> V \<and> (\<forall>a. af = Some a \<longrightarrow> a \<in> V) \<and> set dr \<subseteq> V"
    using stem_loop_out_V[OF ps0 ranP0, THEN mp, OF outpre] .
  have pstV: "pst \<in> V" and lsV: "ls \<in> V" and afV: "\<forall>a. af = Some a \<longrightarrow> a \<in> V" and drV: "set dr \<subseteq> V"
    using memb steq by auto
  have ranfacts: "ran (thrd Sl) \<subseteq> V \<and> ran (rvth Sl) \<subseteq> V"
    using stem_loop_ran_thrd[OF ps0 ranP0, THEN mp, OF outpre] steq by simp
  have ranthrdSl: "ran (thrd Sl) \<subseteq> V" using ranfacts by simp
  have cap: "length [j] + length (follow (prnt S0) i) \<le> Suc (card V)"
  proof -
    have "length (follow (prnt S0) i) = card (set (follow (prnt S0) i))"
      using follow_distinct_ps[OF ps0, of i] by (simp add: distinct_card)
    also have "... \<le> card V" using follow_subset_V[OF rinv iV] finV by (simp add: card_mono)
    finally show ?thesis by simp
  qed
  have SLpre: "(\<forall>v \<in> set (follow (prnt S0) i). prnt Sinit v = prnt S0 v) \<and> p \<in> set (follow (prnt S0) i) \<and> i \<in> V \<and> j \<in> V \<and> lsuc S0 i \<in> V \<and> (\<forall>a. thrd S0 (lsuc S0 i) = Some a \<longrightarrow> a \<in> V) \<and> length [j] + length (follow (prnt S0) i) \<le> Suc (card V) \<and> (\<forall>v \<in> set (follow (prnt S0) i). p \<in> set (follow (prnt S0) v) \<and> v \<noteq> p \<longrightarrow> rvth Sinit v \<noteq> None)"
    using pi iV jV lsx0V ranT0 rvthdef0 cap by (auto simp: prntSinit ran_def)
  have SL: "<ndtree_drt_assn V Sinit Ti 1 [j]> stem_loop_imp Ti i j (lsuc S0 i) (nat_of_opt (thrd S0 (lsuc S0 i))) 1 p <\<lambda>(pstm', lsx', aft', sp'). ndtree_drt_assn V Sl Ti sp' dr * \<up>(pstm' = pst \<and> lsx' = ls \<and> aft' = nat_of_opt af \<and> sp' = length dr)>"
    using stem_loop_imp_wf[OF ps0 ranP0, THEN mp, OF SLpre] by (simp add: steq)
  have revante: "(\<forall>v \<in> set (follow (prnt S0) i). prnt Sinit v = prnt S0 v) \<and> p \<in> set (follow (prnt S0) i)"
    using agr0 pi by blast
  have revrule: "\<forall>u w. u \<in> set (follow (prnt S0) i) \<and> prnt S0 u = Some w \<and> p \<in> set (follow (prnt S0) w) \<and> w \<noteq> p \<longrightarrow> prnt Sl w = Some u"
    using stem_loop_prnt_rev[OF ps0, where S = Sinit and stm = i and pstm = j and lsx = "lsuc S0 i" and aft = "thrd S0 (lsuc S0 i)" and drt = "[j]", THEN mp, OF revante] steq by auto
  have revfact: "\<And>t. t \<in> {Suc 0..<k} \<Longrightarrow> prnt Sl (s t) = Some (s (t - 1))"
  proof -
    fix t assume t: "t \<in> {Suc 0..<k}"
    hence tk: "t < k" and t1: "Suc 0 \<le> t" by auto
    have e1: "s (t - 1) \<in> set (follow (prnt S0) i)" using smem t by auto
    have "t - 1 < k" using tk t1 by simp
    hence "prnt S0 (s (t - 1)) = Some (s (Suc (t - 1)))" using step by simp
    hence e2: "prnt S0 (s (t - 1)) = Some (s t)" using t1 by simp
    have e3: "p \<in> set (follow (prnt S0) (s t))" using seq_p_in_follow[OF ps0 step] sk tk by auto
    have e4: "s t \<noteq> p"
    proof
      assume "s t = p"
      hence "s t = s k" using sk by simp
      from inj_onD[OF inj this] tk have "t = k" by simp
      thus False using tk by simp
    qed
    show "prnt Sl (s t) = Some (s (t - 1))" by (rule revrule[rule_format, OF conjI[OF e1 conjI[OF e2 conjI[OF e3 e4]]]])
  qed
  define Sp where "Sp = Sl\<lparr>prnt := (prnt Sl)(p \<mapsto> pst)\<rparr>"
  define Sq where "Sq = (case (if old_rev = j then thrd S0 old_last else thrd S0 j) of
                          None \<Rightarrow> Sp\<lparr>thrd := (thrd Sp)(ls := None)\<rparr>
                        | Some a \<Rightarrow> Sp\<lparr>thrd := (thrd Sp)(ls \<mapsto> a), rvth := (rvth Sp)(a \<mapsto> ls)\<rparr>)"
  define Sr where "Sr = Sq\<lparr>lsuc := (lsuc Sq)(p := ls)\<rparr>"
  define Ss where "Ss = (if old_rev \<noteq> j
                         then (case af of None \<Rightarrow> Sr\<lparr>thrd := (thrd Sr)(old_rev := None)\<rparr>
                               | Some a \<Rightarrow> Sr\<lparr>thrd := (thrd Sr)(old_rev \<mapsto> a), rvth := (rvth Sr)(a \<mapsto> old_rev)\<rparr>)
                         else Sr)"
  define St where "St = dirty_pass Ss dr"
  define Su where "Su = stem_num_loop St (snum S0) p i 0 (lsuc St p)"
  define Sv where "Sv = Su\<lparr>snum := (snum Su)(i := old_num)\<rparr>"
  have prntSt: "prnt St = (prnt Sl)(p \<mapsto> pst)"
    by (simp add: St_def dirty_pass_keeps Ss_def Sr_def Sq_def Sp_def split: option.split)
  have snumSt: "snum St = snum S0"
  proof -
    have "snum St = snum Sl" by (simp add: St_def dirty_pass_keeps Ss_def Sr_def Sq_def Sp_def split: option.split)
    also have "snum Sl = snum Sinit"
      using stem_loop_snum[OF ps0, where S = Sinit and stm = i and pstm = j and lsx = "lsuc S0 i" and aft = "thrd S0 (lsuc S0 i)" and drt = "[j]", THEN mp, OF revante] steq by simp
    also have "snum Sinit = snum S0" by (simp add: Sinit_def)
    finally show ?thesis .
  qed
  have lsucStp: "lsuc St p = ls"
    by (simp add: St_def dirty_pass_keeps Ss_def Sr_def Sq_def Sp_def split: option.split)
  have thrdSsV: "ran (thrd Ss) \<subseteq> V"
    using ranthrdSl tcV afV by (cases "old_rev = j"; cases af)
       (auto simp: Ss_def Sr_def Sq_def Sp_def ran_def split: option.split if_split_asm)
  have agrstem: "\<And>t. t \<in> {Suc 0..k} \<Longrightarrow> prnt St (s t) = P_snl (s t)"
  proof -
    fix t assume t: "t \<in> {Suc 0..k}"
    have pval: "P_snl (s t) = Some (s (t - 1))" using Psnl_val t by simp
    show "prnt St (s t) = P_snl (s t)"
    proof (cases "t = k")
      case True
      have "s t = p" using True sk by simp
      hence "prnt St (s t) = Some pst" using prntSt by simp
      thus ?thesis using pstsk True pval by simp
    next
      case False
      hence tk: "t < k" using t by auto
      hence tin: "t \<in> {Suc 0..<k}" using t by auto
      have "s t \<noteq> p"
      proof
        assume "s t = p"
        hence "s t = s k" using sk by simp
        from inj_onD[OF inj this] tk have "t = k" by simp
        thus False using tk by simp
      qed
      hence "prnt St (s t) = prnt Sl (s t)" using prntSt by simp
      also have "... = Some (s (t - 1))" using revfact[OF tin] by simp
      finally show ?thesis using pval by simp
    qed
  qed
  have followsub: "set (follow P_snl p) \<subseteq> s ` {..k}"
  proof -
    have "p \<in> s ` {..k}" using sk by (metis atMost_iff imageI order_refl)
    hence "insert p (ran P_snl) \<subseteq> s ` {..k}" using ranPsnlS by auto
    thus ?thesis using follow_ran_subset[OF psN] by auto
  qed
  have agr: "\<forall>w \<in> set (follow P_snl p). w \<noteq> i \<longrightarrow> prnt St w = P_snl w"
  proof (intro ballI impI)
    fix w assume w: "w \<in> set (follow P_snl p)" and wi: "w \<noteq> i"
    obtain t where t: "t \<le> k" and wst: "w = s t" using w followsub by auto
    show "prnt St w = P_snl w"
    proof (cases "t = 0")
      case True
      hence "w = i" using wst s0 by simp
      thus ?thesis using wi by simp
    next
      case False
      hence "t \<in> {Suc 0..k}" using t by auto
      thus ?thesis using agrstem wst by simp
    qed
  qed
  have lsucStpV: "lsuc St p \<in> V" using lsucStp lsV by simp
  have snlpre: "(\<forall>w \<in> set (follow P_snl p). w \<noteq> i \<longrightarrow> prnt St w = P_snl w) \<and> p \<in> V \<and> lsuc St p \<in> V \<and> (\<forall>w \<in> set (follow P_snl p). snum St w = snum S0 w)"
    using agr pV lsucStpV snumSt by simp
  have SNL: "<ndtree_assn V St Ti> stem_num_loop_imp Ti p i 0 (lsuc St p) <\<lambda>_. ndtree_assn V Su Ti>"
    using stem_num_loop_imp_wf[OF psN ranPsnl V0, THEN mp, OF snlpre] by (simp add: Su_def)
  have TC: "<ndtree_assn V S0 Ti> (if old_rev = j then Array.nth (thrd_impl Ti) old_last else Array.nth (thrd_impl Ti) j)
      <\<lambda>r. ndtree_assn V S0 Ti * \<up>(r = nat_of_opt (if old_rev = j then thrd S0 old_last else thrd S0 j))>"
    by (cases "old_rev = j") (sep_auto simp: old_lastV jV)+
  have RE: "\<And>St'. <ndtree_drt_assn V St' Ti (length dr) dr>
      (if old_rev \<noteq> j
       then (if nat_of_opt af = 0 then Array.upd old_rev 0 (thrd_impl Ti) \<bind> (\<lambda>_. return ())
             else Array.upd old_rev (nat_of_opt af) (thrd_impl Ti) \<bind> (\<lambda>_. Array.upd (nat_of_opt af) old_rev (rvth_impl Ti) \<bind> (\<lambda>_. return ())))
       else return ())
      <\<lambda>_. ndtree_drt_assn V (if old_rev \<noteq> j then (case af of None \<Rightarrow> St'\<lparr>thrd := (thrd St')(old_rev := None)\<rparr>
                               | Some a \<Rightarrow> St'\<lparr>thrd := (thrd St')(old_rev \<mapsto> a), rvth := (rvth St')(a \<mapsto> old_rev)\<rparr>) else St') Ti (length dr) dr>"
  proof -
    fix St'
    show "?thesis St'"
    proof (cases "old_rev = j")
      case True hence nc: "\<not> (old_rev \<noteq> j)" by simp
      show ?thesis unfolding if_not_P[OF nc] by sep_auto
    next
      case False hence pc: "old_rev \<noteq> j" by simp
      show ?thesis unfolding if_P[OF pc] by (rule aftT_drt[OF V0 old_revV afV[rule_format]])
    qed
  qed
  have funeq: "ut_reversal_fun S0 i j p old_rev old_num old_last = Sv"
    by (simp only: ut_reversal_fun_def Let_def Sinit_def[symmetric] steq prod.case Sv_def Su_def St_def Ss_def Sr_def Sq_def Sp_def)
  show ?thesis
    unfolding ut_reversal_imp_def funeq
    apply (rule ht_bind[OF TC], rule ht_extract_pre_pure, hypsubst)
    apply (rule ht_bind[OF ndtree_nth_lsuc[OF iV]], rule ht_extract_pre_pure, hypsubst)
    apply (rule ht_bind[OF ndtree_nth_thrd[OF lsx0V]], rule ht_extract_pre_pure, hypsubst)
    apply (rule ht_bind[OF ndtree_upd_thrd_Some[OF jV iV]])
    apply (rule ht_bind[OF ndtree_assn_to_drt[OF jV]], fold Sinit_def)
    apply (rule ht_bind[OF SL])
    apply (case_tac xe)
    apply (simp only: prod.case)
    apply (rule ht_extract_pre_pure, elim conjE, hypsubst)
    apply (rule ht_bind[OF ndtree_drt_upd_prnt_Some[OF pV pstV]], fold Sp_def)
    apply (rule ht_bind[OF aftT_drt[OF V0 lsV tcV]], assumption, fold Sq_def)
    apply (rule ht_bind[OF ndtree_drt_upd_lsuc[OF pV lsV]], fold Sr_def)
    apply (rule ht_bind[OF RE], fold Ss_def)
    apply (rule ht_bind[OF dirty_pass_imp_rule[OF V0 drV thrdSsV]], fold St_def)
    apply (rule ht_bind[OF ndtree_nth_lsuc[OF pV]], rule ht_extract_pre_pure, hypsubst)
    apply (rule ht_bind[OF SNL])
    apply (rule ht_bind[OF ndtree_upd_snum[OF iV]], fold Sv_def)
    apply sep_auto
    done
qed

text \<open>Top-level correspondence: @{const update_tree_imp} refines @{const update_tree} on the plain
      @{const ndtree_assn} (the auxiliary array is entirely internal).  Preconditions: @{const arb_invar}
      together with the memberships @{term "i \<in> V"}, @{term "j \<in> V"}, @{term "jn \<in> V"}, the pivot
      @{term "p \<in> set (follow (prnt S) i)"}, and @{term "p \<noteq> r"}.

      The \<^emph>\<open>join geometry\<close> (@{term "jn = join_of (prnt S) i j"}, @{term "jn \<in> set (follow (prnt S) p)"},
      @{term "p \<noteq> jn"}) is \<^emph>\<open>not\<close> needed for the refinement --- it is required only for
      @{thm update_tree_preserves_arb_invar}.  The imperative matches @{const update_tree} for the given
      @{term jn} because each loop refines its functional twin \<^emph>\<open>unconditionally\<close>, by fixpoint induction
      under partial correctness (@{thm fused_vin_loop_imp_uncond}, @{thm fused_vout_loop_imp_uncond}): on an
      invalid move the loop diverges and the triple holds vacuously.  The @{term "i \<noteq> p"} branch is the
      geometry-free @{thm UT_reversal}; the fused tail is @{thm UT_tail}, whose \<open>ran (prnt S1) \<subseteq> V\<close> /
      \<open>lsuc S1 p \<in> V\<close> side conditions are read off the @{const ndtree_assn} precondition
      (@{thm ran_prnt_ndtree_assn_extract}, @{thm lsuc_ndtree_assn_extract}).\<close>
theorem update_tree_imp_rule:
  assumes arb: "arb_invar r V S" and iV: "i \<in> V" and jV: "j \<in> V"
      and pi: "p \<in> set (follow (prnt S) i)"
      and jnV: "jn \<in> V"
      and pnr: "p \<noteq> r"
  shows "<ndtree_assn V S Ti>
     update_tree_imp Ti i j p jn
   <\<lambda>_. ndtree_assn V (update_tree S i j p jn) Ti>"
proof -
  have rinv: "rooted_arborescense_invar r V (prnt S)" using arb by (simp add: arb_invar_def)
  have pV: "p \<in> V" using pi follow_subset_V[OF rinv iV] by auto
  note pner = pnr
  have pdomP: "p \<in> dom (prnt S)" using pV pner rooted_arborescense_invar_dom[OF rinv] by simp
  have pdomR: "p \<in> dom (rvth S)" using pV pner arb unfolding arb_invar_def by simp
  have vouteq: "nat_of_opt (prnt S p) = the (prnt S p)" using pdomP by (cases "prnt S p") auto
  have oldreveq: "nat_of_opt (rvth S p) = the (rvth S p)" using pdomR by (cases "rvth S p") auto
  have ranP: "ran (prnt S) \<subseteq> V"
  proof
    fix z assume "z \<in> ran (prnt S)"
    then obtain y0 where "prnt S y0 = Some z" by (auto simp: ran_def)
    hence "(y0, z) \<in> {(y, x) |x y. Some x = prnt S y}" by auto
    hence "z \<in> dVs {(y, x) |x y. Some x = prnt S y}" by (rule dVsI(2))
    thus "z \<in> V" using rinv rooted_arborescense_invar_dVs by blast
  qed
  have ranT: "ran (thrd S) \<subseteq> V"
  proof
    fix z assume "z \<in> ran (thrd S)"
    then obtain y0 where "thrd S y0 = Some z" by (auto simp: ran_def)
    hence "rvth S z = Some y0" using arb unfolding arb_invar_def by simp
    hence "z \<in> dom (rvth S)" by auto
    thus "z \<in> V" using arb unfolding arb_invar_def by auto
  qed
  have ranR: "ran (rvth S) \<subseteq> V"
  proof
    fix z assume "z \<in> ran (rvth S)"
    then obtain y0 where "rvth S y0 = Some z" by (auto simp: ran_def)
    hence "thrd S z = Some y0" using arb unfolding arb_invar_def by simp
    hence "z \<in> dom (thrd S)" by auto
    thus "z \<in> V" using arb unfolding arb_invar_def by auto
  qed
  have voutV: "the (prnt S p) \<in> V" using pdomP ranP by (auto simp: ran_def)
  have oldrevV: "the (rvth S p) \<in> V" using pdomR ranR by (auto simp: ran_def)
  have oldlastV: "lsuc S p \<in> V" using pV arb unfolding arb_invar_def by auto
  define Sa where "Sa = S\<lparr>prnt := (prnt S)(i \<mapsto> j)\<rparr>"
  define Sbb where "Sbb = (case thrd Sa (lsuc S p) of None \<Rightarrow> Sa\<lparr>thrd := (thrd Sa)(the (rvth S p) := None)\<rparr>
                          | Some a \<Rightarrow> Sa\<lparr>thrd := (thrd Sa)(the (rvth S p) \<mapsto> a), rvth := (rvth Sa)(a \<mapsto> the (rvth S p))\<rparr>)"
  define Scc where "Scc = Sbb\<lparr>thrd := (thrd Sbb)(j \<mapsto> p), rvth := (rvth Sbb)(p \<mapsto> j)\<rparr>"
  define Sdd where "Sdd = (case thrd Sbb j of None \<Rightarrow> Scc\<lparr>thrd := (thrd Scc)(lsuc S p := None)\<rparr>
                          | Some a \<Rightarrow> Scc\<lparr>thrd := (thrd Scc)(lsuc S p \<mapsto> a), rvth := (rvth Scc)(a \<mapsto> lsuc S p)\<rparr>)"
  define S1 where "S1 = (if i = p then (if thrd Sa j = Some p then Sa else Sdd)
                         else ut_reversal_fun S i j p (the (rvth S p)) (snum S p) (lsuc S p))"
  have UTeq: "update_tree S i j p jn =
     (if jn \<noteq> the (rvth S p) \<and> j \<noteq> the (rvth S p)
      then fused_vout_loop (fused_vin_loop S1 j j jn (lsuc S1 p) (snum S p) True True) (the (prnt S p)) (if lsuc S1 jn = j then Some jn else None) (lsuc S p) (the (rvth S p)) jn (snum S p) True True
      else if lsuc S1 p \<noteq> lsuc S p
           then fused_vout_loop (fused_vin_loop S1 j j jn (lsuc S1 p) (snum S p) True True) (the (prnt S p)) (if lsuc S1 jn = j then Some jn else None) (lsuc S p) (lsuc S1 p) jn (snum S p) True True
           else fused_vout_loop (fused_vin_loop S1 j j jn (lsuc S1 p) (snum S p) True True) (the (prnt S p)) (if lsuc S1 jn = j then Some jn else None) (lsuc S p) (lsuc S p) jn (snum S p) False True)"
    unfolding S1_def Sdd_def Scc_def Sbb_def Sa_def ut_reversal_fun_def
    by (simp only: update_tree_def Let_def prod.case)
  have BR: "<ndtree_assn V S Ti>
       (if i = p
        then do {
          _ \<leftarrow> Array.upd i j (prnt_impl Ti);
          tj \<leftarrow> Array.nth (thrd_impl Ti) j;
          (if tj = p then return ()
           else do {
             aft1 \<leftarrow> Array.nth (thrd_impl Ti) (lsuc S p);
             _ \<leftarrow> (if aft1 = 0 then do { _ \<leftarrow> Array.upd (the (rvth S p)) 0 (thrd_impl Ti); return () }
                    else do { _ \<leftarrow> Array.upd (the (rvth S p)) aft1 (thrd_impl Ti);
                              _ \<leftarrow> Array.upd aft1 (the (rvth S p)) (rvth_impl Ti); return () });
             aft2 \<leftarrow> Array.nth (thrd_impl Ti) j;
             _ \<leftarrow> Array.upd j p (thrd_impl Ti);
             _ \<leftarrow> Array.upd p j (rvth_impl Ti);
             (if aft2 = 0 then do { _ \<leftarrow> Array.upd (lsuc S p) 0 (thrd_impl Ti); return () }
              else do { _ \<leftarrow> Array.upd (lsuc S p) aft2 (thrd_impl Ti);
                        _ \<leftarrow> Array.upd aft2 (lsuc S p) (rvth_impl Ti); return () })
           })
        }
        else ut_reversal_imp Ti i j p (the (rvth S p)) (snum S p) (lsuc S p))
       <\<lambda>_. ndtree_assn V S1 Ti>"
  proof (cases "i = p")
    case True
    have res: "(let Sa = S\<lparr>prnt := (prnt S)(i \<mapsto> j)\<rparr>
       in if thrd Sa j = Some p then Sa
          else (let Sb = (case thrd Sa (lsuc S p) of None \<Rightarrow> Sa\<lparr>thrd := (thrd Sa)(the (rvth S p) := None)\<rparr>
                          | Some a \<Rightarrow> Sa\<lparr>thrd := (thrd Sa)(the (rvth S p) \<mapsto> a), rvth := (rvth Sa)(a \<mapsto> the (rvth S p))\<rparr>);
                    Sc = Sb\<lparr>thrd := (thrd Sb)(j \<mapsto> p), rvth := (rvth Sb)(p \<mapsto> j)\<rparr>
                in (case thrd Sb j of None \<Rightarrow> Sc\<lparr>thrd := (thrd Sc)(lsuc S p := None)\<rparr>
                    | Some a \<Rightarrow> Sc\<lparr>thrd := (thrd Sc)(lsuc S p \<mapsto> a), rvth := (rvth Sc)(a \<mapsto> lsuc S p)\<rparr>))) = S1"
      using True 
      by (auto simp add: S1_def Sdd_def Scc_def Sbb_def Sa_def Let_def 
                  split: option.split)
    show ?thesis unfolding if_P[OF True] res[symmetric]
      by (rule UT_simple[OF iV jV pV oldrevV oldlastV ranT])
  next
    case False
    have res: "ut_reversal_fun S i j p (the (rvth S p)) (snum S p) (lsuc S p) = S1"
      using False by (simp add: S1_def)
    show ?thesis unfolding if_not_P[OF False] res[symmetric]
      by (rule UT_reversal[OF arb iV jV pi pner False refl refl refl])
  qed
  show ?thesis
    unfolding update_tree_imp_def UTeq
    apply (rule ht_bind[OF ndtree_nth_prnt[OF pV]], rule ht_extract_pre_pure, hypsubst)
    apply (rule ht_bind[OF ndtree_nth_rvth[OF pV]], rule ht_extract_pre_pure, hypsubst)
    apply (rule ht_bind[OF ndtree_nth_snum[OF pV]], rule ht_extract_pre_pure, hypsubst)
    apply (rule ht_bind[OF ndtree_nth_lsuc[OF pV]], rule ht_extract_pre_pure, hypsubst)
    apply (simp only: vouteq oldreveq)
    apply (fold ut_reversal_imp_def)
    apply (rule ht_bind[OF BR])
    apply (rule UT_tail[OF jV jnV pV voutV oldrevV oldlastV])
    done
qed

subsection \<open>Refinement of the join / path-pair search @{const get_path_pair_impl}\<close>

text \<open>Imperative port of @{const join_paths_loop}: the two branch paths are written directly into the
      caller's arrays @{term a1} / @{term a2} at ascending indices @{term q1} / @{term q2} (the running
      lengths), lifting whichever endpoint currently has the smaller @{const snum} to its parent.  No
      list is built and only a constant amount of extra state is used; the returned pair of fill
      pointers marks how much of each array now holds the corresponding branch path.\<close>
partial_function (heap) join_paths_loop_imp ::
  "ndtree_impl \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) Heap" where
  "join_paths_loop_imp Ti a1 a2 u v q1 q2 =
     (if u = v then return (q1, q2)
      else do {
        snu \<leftarrow> Array.nth (snum_impl Ti) u;
        snv \<leftarrow> Array.nth (snum_impl Ti) v;
        (if snu \<le> snv
         then do {
           pu \<leftarrow> Array.nth (prnt_impl Ti) u;
           _ \<leftarrow> Array.upd q1 u a1;
           join_paths_loop_imp Ti a1 a2 pu v (q1 + 1) q2
         }
         else do {
           pv \<leftarrow> Array.nth (prnt_impl Ti) v;
           _ \<leftarrow> Array.upd q2 v a2;
           join_paths_loop_imp Ti a1 a2 u pv q1 (q2 + 1)
         })
      })"

text \<open>The @{const get_path_pair_impl} operation of the arborescence ADT, imperatively: run the loop from
      empty fill pointers.\<close>
definition get_path_pair_imp :: "ndtree_impl \<Rightarrow> nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) Heap" where
  "get_path_pair_imp Ti a1 a2 u v = join_paths_loop_imp Ti a1 a2 u v 0 0"

lemma finite_V_arb: "arb_invar r V S \<Longrightarrow> finite V"
  by (metis arb_invar_def List.finite_set)

text \<open>The loop refines @{const join_paths_loop} for any common ancestor @{term j}: with @{term W} the
      before-@{term j} prefix of a root-path, the loop leaves the two arrays with @{term "W u"} / @{term "W v"}
      appended at @{term q1} / @{term q2} and returns the advanced fill pointers.  Proved by strong induction
      on the combined length of the two remaining root-paths, mirroring @{thm join_paths_loop_eval}; each
      recursive call is bridged to the target shape by @{thm ht_cons_post_prec}.\<close>
lemma join_paths_loop_imp_rule:
  assumes inv: "arb_invar r V S" and W_def: "W = (\<lambda>x. takeWhile (\<lambda>y. y \<noteq> j) (follow (prnt S) x))"
  shows "u \<in> V \<Longrightarrow> v \<in> V \<Longrightarrow> j \<in> set (follow (prnt S) u) \<Longrightarrow> j \<in> set (follow (prnt S) v) \<Longrightarrow>
    set (W u) \<inter> set (W v) = {} \<Longrightarrow> q1 + length (W u) \<le> length xs1 \<Longrightarrow> q2 + length (W v) \<le> length xs2 \<Longrightarrow>
    <ndtree_assn V S Ti * a1 \<mapsto>\<^sub>a xs1 * a2 \<mapsto>\<^sub>a xs2>
      join_paths_loop_imp Ti a1 a2 u v q1 q2
    <\<lambda>(r1, r2). \<exists>\<^sub>A ys1 ys2. ndtree_assn V S Ti * a1 \<mapsto>\<^sub>a ys1 * a2 \<mapsto>\<^sub>a ys2 *
        \<up>(r1 = q1 + length (W u) \<and> r2 = q2 + length (W v) \<and> length ys1 = length xs1 \<and> length ys2 = length xs2 \<and>
          take r1 ys1 = take q1 xs1 @ W u \<and> take r2 ys2 = take q2 xs2 @ W v)>"
proof -
  have rinv: "rooted_arborescense_invar r V (prnt S)" using inv unfolding arb_invar_def by simp
  have ps: "parent_spec (prnt S)" by (rule rooted_arborescense_invar_parent_spec[OF rinv])
  { fix N cu cv b1 b2 ys1 ys2
    have "length (follow (prnt S) cu) + length (follow (prnt S) cv) = N \<Longrightarrow> cu \<in> V \<Longrightarrow> cv \<in> V \<Longrightarrow>
          j \<in> set (follow (prnt S) cu) \<Longrightarrow> j \<in> set (follow (prnt S) cv) \<Longrightarrow> set (W cu) \<inter> set (W cv) = {} \<Longrightarrow>
          b1 + length (W cu) \<le> length ys1 \<Longrightarrow> b2 + length (W cv) \<le> length ys2 \<Longrightarrow>
          <ndtree_assn V S Ti * a1 \<mapsto>\<^sub>a ys1 * a2 \<mapsto>\<^sub>a ys2> join_paths_loop_imp Ti a1 a2 cu cv b1 b2
          <\<lambda>(r1, r2). \<exists>\<^sub>A zs1 zs2. ndtree_assn V S Ti * a1 \<mapsto>\<^sub>a zs1 * a2 \<mapsto>\<^sub>a zs2 *
              \<up>(r1 = b1 + length (W cu) \<and> r2 = b2 + length (W cv) \<and> length zs1 = length ys1 \<and> length zs2 = length ys2 \<and>
                take r1 zs1 = take b1 ys1 @ W cu \<and> take r2 zs2 = take b2 ys2 @ W cv)>"
    proof (induct N arbitrary: cu cv b1 b2 ys1 ys2 rule: less_induct)
      case (less N cu cv b1 b2 ys1 ys2)
      note eqN = less.prems(1) and cuV = less.prems(2) and cvV = less.prems(3) and jcu = less.prems(4)
        and jcv = less.prems(5) and disj = less.prems(6) and len1 = less.prems(7) and len2 = less.prems(8)
      have jV: "j \<in> V" using follow_subset_V[OF rinv cuV] jcu by auto
      show ?case
      proof (cases "cu = cv")
        case True
        note eqcc = True
        have cuj: "cu = j"
        proof (rule ccontr)
          assume cune: "cu \<noteq> j"
          have "cu \<in> set (W cu)"
          proof -
            have ne: "follow (prnt S) cu \<noteq> []" by (rule follow_ne_ps[OF ps])
            have hd: "hd (follow (prnt S) cu) = cu" by (rule follow_hd_ps[OF ps])
            show ?thesis using ne hd cune by (cases "follow (prnt S) cu") (auto simp: W_def)
          qed
          moreover have "cu \<in> set (W cv)" using eqcc calculation by simp
          ultimately show False using disj by auto
        qed
        have Wcu: "W cu = []" using cuj follow_ne_ps[OF ps, of cu] follow_hd_ps[OF ps, of cu]
          by (simp add: W_def takeWhile_eq_Nil_iff)
        have Wcv: "W cv = []" using Wcu eqcc by simp
        show ?thesis using eqcc Wcu Wcv by (subst join_paths_loop_imp.simps) sep_auto
      next
        case False
        note cune_cv = False
        show ?thesis
        proof (cases "snum S cu \<le> snum S cv")
          case True
          note le = True
          have cune: "cu \<noteq> j"
          proof (rule ccontr)
            assume "\<not> cu \<noteq> j" hence cj: "cu = j" by simp
            have cvne: "cv \<noteq> j" using cune_cv cj by auto
            have "snum S cv < snum S j" using snum_proper_anc_lt[OF inv jV jcv] cvne by simp
            thus False using le cj by simp
          qed
          obtain w where Pw: "prnt S cu = Some w" and fcu: "follow (prnt S) cu = cu # follow (prnt S) w"
            and jcw: "j \<in> set (follow (prnt S) w)" using follow_cons_of_anc[OF ps jcu cune] by auto
          have Wcu: "W cu = cu # W w" using fcu cune by (simp add: W_def)
          have wmem: "w \<in> set (follow (prnt S) cu)" using fcu follow_hd_ps[OF ps, of w] follow_ne_ps[OF ps, of w]
            by (metis hd_in_set list.set_intros(2))
          have wV: "w \<in> V" using follow_subset_V[OF rinv cuV] wmem by auto
          have disj': "set (W w) \<inter> set (W cv) = {}" using disj Wcu by auto
          have lenlt: "length (follow (prnt S) w) + length (follow (prnt S) cv) < N" using eqN fcu by simp
          have b1lt: "b1 < length ys1" using len1 Wcu by simp
          have len1'': "Suc b1 + length (W w) \<le> length (list_update ys1 b1 cu)" using len1 Wcu by simp
          note IH2 = less.hyps[OF lenlt refl wV cvV jcw jcv disj' len1'' len2]
          have takeeq: "take (Suc b1) (ys1[b1 := cu]) @ W w = take b1 ys1 @ W cu"
          proof -
            have A: "take (Suc b1) (ys1[b1 := cu]) = take b1 (ys1[b1 := cu]) @ [(ys1[b1 := cu]) ! b1]"
              using b1lt by (subst take_Suc_conv_app_nth) simp_all
            have B: "take b1 (ys1[b1 := cu]) = take b1 ys1" by (rule take_update_cancel) simp
            have C: "(ys1[b1 := cu]) ! b1 = cu" using b1lt by (rule nth_list_update_eq)
            show ?thesis using A B C Wcu by simp
          qed
          have cnteq2: "Suc (b1 + length (W w)) = b1 + length (W cu)" using Wcu by simp
          have takeeq2: "(take (Suc b1) ys1)[b1 := cu] @ W w = take b1 ys1 @ W cu"
            using takeeq by (simp add: take_update_swap)
          have IHgoal: "<ndtree_assn V S Ti * a1 \<mapsto>\<^sub>a ys1[b1 := cu] * a2 \<mapsto>\<^sub>a ys2>
              join_paths_loop_imp Ti a1 a2 w cv (Suc b1) b2
            <\<lambda>(r1, r2). \<exists>\<^sub>A zs1 zs2. ndtree_assn V S Ti * a1 \<mapsto>\<^sub>a zs1 * a2 \<mapsto>\<^sub>a zs2 *
                \<up>(r1 = b1 + length (W cu) \<and> r2 = b2 + length (W cv) \<and> length zs1 = length ys1 \<and> length zs2 = length ys2 \<and>
                  take r1 zs1 = take b1 ys1 @ W cu \<and> take r2 zs2 = take b2 ys2 @ W cv)>"
            by (rule ht_cons_post_prec[OF IH2]) (sep_auto simp: cnteq2 takeeq2)
          show ?thesis
            apply (subst join_paths_loop_imp.simps)
            apply (sep_auto simp: cune_cv le Pw cuV cvV b1lt heap: IHgoal)
            done
        next
          case False
          note notle = False
          have cvne: "cv \<noteq> j"
          proof (rule ccontr)
            assume "\<not> cv \<noteq> j" hence cj: "cv = j" by simp
            have cune: "cu \<noteq> j" using cune_cv cj by auto
            have "snum S cu < snum S j" using snum_proper_anc_lt[OF inv jV jcu] cune by simp
            thus False using notle cj by simp
          qed
          obtain w where Pw: "prnt S cv = Some w" and fcv: "follow (prnt S) cv = cv # follow (prnt S) w"
            and jcw: "j \<in> set (follow (prnt S) w)" using follow_cons_of_anc[OF ps jcv cvne] by auto
          have Wcv: "W cv = cv # W w" using fcv cvne by (simp add: W_def)
          have wmem: "w \<in> set (follow (prnt S) cv)" using fcv follow_hd_ps[OF ps, of w] follow_ne_ps[OF ps, of w]
            by (metis hd_in_set list.set_intros(2))
          have wV: "w \<in> V" using follow_subset_V[OF rinv cvV] wmem by auto
          have disj': "set (W cu) \<inter> set (W w) = {}" using disj Wcv by auto
          have lenlt: "length (follow (prnt S) cu) + length (follow (prnt S) w) < N" using eqN fcv by simp
          have b2lt: "b2 < length ys2" using len2 Wcv by simp
          have len2'': "b1 + length (W cu) \<le> length ys1" using len1 by simp
          note IH2 = less.hyps[OF lenlt refl cuV wV jcu jcw disj' len2'']
          have len2': "Suc b2 + length (W w) \<le> length (list_update ys2 b2 cv)" using len2 Wcv by simp
          note IH2' = IH2[of "Suc b2" "ys2[b2 := cv]", OF len2']
          have takeeq: "take (Suc b2) (ys2[b2 := cv]) @ W w = take b2 ys2 @ W cv"
          proof -
            have A: "take (Suc b2) (ys2[b2 := cv]) = take b2 (ys2[b2 := cv]) @ [(ys2[b2 := cv]) ! b2]"
              using b2lt by (subst take_Suc_conv_app_nth) simp_all
            have B: "take b2 (ys2[b2 := cv]) = take b2 ys2" by (rule take_update_cancel) simp
            have C: "(ys2[b2 := cv]) ! b2 = cv" using b2lt by (rule nth_list_update_eq)
            show ?thesis using A B C Wcv by simp
          qed
          have cnteq2: "Suc (b2 + length (W w)) = b2 + length (W cv)" using Wcv by simp
          have takeeq2: "(take (Suc b2) ys2)[b2 := cv] @ W w = take b2 ys2 @ W cv"
            using takeeq by (simp add: take_update_swap)
          have IHgoal: "<ndtree_assn V S Ti * a1 \<mapsto>\<^sub>a ys1 * a2 \<mapsto>\<^sub>a ys2[b2 := cv]>
              join_paths_loop_imp Ti a1 a2 cu w b1 (Suc b2)
            <\<lambda>(r1, r2). \<exists>\<^sub>A zs1 zs2. ndtree_assn V S Ti * a1 \<mapsto>\<^sub>a zs1 * a2 \<mapsto>\<^sub>a zs2 *
                \<up>(r1 = b1 + length (W cu) \<and> r2 = b2 + length (W cv) \<and> length zs1 = length ys1 \<and> length zs2 = length ys2 \<and>
                  take r1 zs1 = take b1 ys1 @ W cu \<and> take r2 zs2 = take b2 ys2 @ W cv)>"
            by (rule ht_cons_post_prec[OF IH2']) (sep_auto simp: cnteq2 takeeq2)
          show ?thesis
            apply (subst join_paths_loop_imp.simps)
            apply (sep_auto simp: cune_cv notle Pw cuV cvV b2lt heap: IHgoal)
            done
        qed
      qed
    qed }
  note gen = this
  show "u \<in> V \<Longrightarrow> v \<in> V \<Longrightarrow> j \<in> set (follow (prnt S) u) \<Longrightarrow> j \<in> set (follow (prnt S) v) \<Longrightarrow>
    set (W u) \<inter> set (W v) = {} \<Longrightarrow> q1 + length (W u) \<le> length xs1 \<Longrightarrow> q2 + length (W v) \<le> length xs2 \<Longrightarrow>
    <ndtree_assn V S Ti * a1 \<mapsto>\<^sub>a xs1 * a2 \<mapsto>\<^sub>a xs2> join_paths_loop_imp Ti a1 a2 u v q1 q2
    <\<lambda>(r1, r2). \<exists>\<^sub>A ys1 ys2. ndtree_assn V S Ti * a1 \<mapsto>\<^sub>a ys1 * a2 \<mapsto>\<^sub>a ys2 *
        \<up>(r1 = q1 + length (W u) \<and> r2 = q2 + length (W v) \<and> length ys1 = length xs1 \<and> length ys2 = length xs2 \<and>
          take r1 ys1 = take q1 xs1 @ W u \<and> take r2 ys2 = take q2 xs2 @ W v)>"
    by (rule gen[OF refl])
qed

text \<open>ADT-specification form: for @{term u}, @{term v} in the tree, given two arrays each long enough to
      hold a branch path (length at least @{term "card V - 1"}), @{const get_path_pair_imp} returns the
      two fill pointers @{term "length p1"} / @{term "length p2"} and leaves the arrays with the two
      functional branch paths @{term p1} / @{term p2} (@{term "get_path_pair_impl S u v = (p1, p2)"}) as
      their prefixes.\<close>
lemma get_path_pair_imp_rule:
  assumes inv: "arb_invar r V S" and uV: "u \<in> V" and vV: "v \<in> V"
      and len1: "card V \<le> Suc (length xs1)" and len2: "card V \<le> Suc (length xs2)"
      and pp: "get_path_pair_impl S u v = (p1, p2)"
  shows "<ndtree_assn V S Ti * a1 \<mapsto>\<^sub>a xs1 * a2 \<mapsto>\<^sub>a xs2>
           get_path_pair_imp Ti a1 a2 u v
         <\<lambda>(r1, r2). \<exists>\<^sub>A ys1 ys2. ndtree_assn V S Ti * a1 \<mapsto>\<^sub>a ys1 * a2 \<mapsto>\<^sub>a ys2 *
             \<up>(r1 = length p1 \<and> r2 = length p2 \<and> length ys1 = length xs1 \<and> length ys2 = length xs2 \<and>
               take r1 ys1 = p1 \<and> take r2 ys2 = p2)>"
proof -
  have rinv: "rooted_arborescense_invar r V (prnt S)" using inv unfolding arb_invar_def by simp
  have ps: "parent_spec (prnt S)" by (rule rooted_arborescense_invar_parent_spec[OF rinv])
  define j where "j = join_of (prnt S) u v"
  define W where "W = (\<lambda>x. takeWhile (\<lambda>y. y \<noteq> j) (follow (prnt S) x))"
  have lst: "last (follow (prnt S) u) = last (follow (prnt S) v)"
    using follow_last_root[OF inv uV] follow_last_root[OF inv vV] by simp
  have ju: "j \<in> set (follow (prnt S) u)" using join_of_mem(1)[OF ps lst] by (simp add: j_def)
  have jv: "j \<in> set (follow (prnt S) v)" using join_of_mem(2)[OF ps lst] by (simp add: j_def)
  have jV: "j \<in> V" using follow_subset_V[OF rinv uV] ju by auto
  have disjj: "set (W u) \<inter> set (W v) = {}" using join_takeWhile_disjoint[OF inv uV vV] by (simp add: j_def W_def)
  have p1eq: "p1 = W u" and p2eq: "p2 = W v"
    using pp by (simp_all add: get_path_pair_impl_def
        join_paths_loop_eval[OF inv uV vV ju jv disjj[unfolded W_def], of "[]" "[]"] W_def j_def)
  have finV: "finite V" by (rule finite_V_arb[OF inv])
  have Wsub: "\<And>x. x \<in> V \<Longrightarrow> set (W x) \<subseteq> V - {j}"
  proof -
    fix x assume xV: "x \<in> V"
    have "set (W x) \<subseteq> set (follow (prnt S) x)" by (auto simp: W_def dest: set_takeWhileD)
    hence sub: "set (W x) \<subseteq> V" using follow_subset_V[OF rinv xV] by auto
    have "j \<notin> set (W x)" unfolding W_def using set_takeWhileD by fastforce
    thus "set (W x) \<subseteq> V - {j}" using sub by auto
  qed
  have Wlen: "\<And>x. x \<in> V \<Longrightarrow> length (W x) \<le> card V - 1"
  proof -
    fix x assume xV: "x \<in> V"
    have dW: "distinct (W x)" using follow_distinct_ps[OF ps, of x] by (simp add: W_def)
    have "length (W x) = card (set (W x))" using dW by (simp add: distinct_card)
    also have "\<dots> \<le> card (V - {j})" using Wsub[OF xV] finV by (simp add: card_mono)
    also have "\<dots> = card V - 1" using jV finV by (simp add: card_Diff_singleton)
    finally show "length (W x) \<le> card V - 1" .
  qed
  have b1: "0 + length (W u) \<le> length xs1" using Wlen[OF uV] len1 by simp
  have b2: "0 + length (W v) \<le> length xs2" using Wlen[OF vV] len2 by simp
  note main = join_paths_loop_imp_rule[OF inv W_def uV vV ju jv disjj b1 b2]
  show ?thesis
    unfolding get_path_pair_imp_def
    apply (rule ht_cons_post_prec[OF main])
    apply (sep_auto simp: p1eq p2eq)
    done
qed

subsection \<open>Refinement of the subtree iteration @{const iterate_root_opposed_impl}\<close>

text \<open>Imperative port of @{const subtree_fold} / @{const iterate_root_opposed_impl}.  The accumulator is a
      heap object identified by a handle @{term ai} (e.g. the potential array): the fold visits every node of
      the subtree in thread order and applies the heap-monadic step @{term "fi :: nat \<Rightarrow> 'ai \<Rightarrow> unit Heap"},
      which mutates that object in place.  The structure mirrors the functional @{const subtree_fold} exactly:
      apply @{term "fi u ai"}, stop at the marker @{term stop}, otherwise follow the thread.  The recursion is
      tail-recursive and uses no extra heap of its own.\<close>
partial_function (heap) subtree_fold_imp :: "ndtree_impl \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'ai \<Rightarrow> unit Heap) \<Rightarrow> 'ai \<Rightarrow> unit Heap" where
  "subtree_fold_imp Ti stop u fi ai =
     do {
       _ \<leftarrow> fi u ai;
       (if u = stop then return ()
        else do {
          w \<leftarrow> Array.nth (thrd_impl Ti) u;
          subtree_fold_imp Ti stop w fi ai
        })
     }"

text \<open>The @{const iterate_root_opposed_impl} operation of the arborescence ADT, imperatively: fold from
      @{term v} up to its last successor @{term "lsuc S v"} (read from the array).\<close>
definition iterate_root_opposed_imp :: "ndtree_impl \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'ai \<Rightarrow> unit Heap) \<Rightarrow> 'ai \<Rightarrow> unit Heap" where
  "iterate_root_opposed_imp Ti v fi ai =
     do { ls \<leftarrow> Array.nth (lsuc_impl Ti) v; subtree_fold_imp Ti ls v fi ai }"

text \<open>Every node reachable along the thread from a vertex of the tree is again a vertex: the thread walk
      from @{term x} is a suffix of the global thread @{term "follow (thrd S) r"}, whose node set is @{term V}.\<close>
lemma follow_thrd_subset_V:
  assumes inv: "arb_invar r V S" and xV: "x \<in> V"
  shows "set (follow (thrd S) x) \<subseteq> V"
proof -
  have pst: "parent_spec (thrd S)" using inv unfolding arb_invar_def by simp
  have setV: "set (follow (thrd S) r) = V" using inv unfolding arb_invar_def by simp
  have "x \<in> set (follow (thrd S) r)" using xV setV by simp
  then obtain A B where AB: "follow (thrd S) r = A @ x # B" by (meson split_list)
  have fx: "follow (thrd S) x = x # B" using follow_append_ps[OF pst AB] by auto
  show ?thesis using fx AB setV by auto
qed

text \<open>Refinement of the subtree fold, mirroring the functional @{thm subtree_fold_follow}.  Here
      @{term "R ai a"} is the \<^emph>\<open>accumulator refinement relation\<close>: it asserts that the imperative accumulator
      @{term ai} (a heap object --- e.g. the potential array) currently represents the functional accumulator
      value @{term a}.  The single-step premise @{term fi_rule} says @{term fi} refines @{term f} on one node:
      running @{term "fi x ai"} turns \<open>ai\<close> from a representation of @{term a} into a representation of
      @{term "f x a"}.  The tree @{const ndtree_assn} is framed around the fold (it is read but never modified),
      and the conclusion states that after the fold \<open>ai\<close> represents @{term "subtree_fold S stp u f acc"} --- i.e.
      the imperative accumulator ends up refining the functional result.  The remaining premises are exactly
      those of the functional correctness lemma @{thm subtree_fold_follow} (@{term "parent_spec (thrd S)"}, the
      thread decomposition @{term "follow (thrd S) u = bl @ stp # rest"}, @{term "stp \<notin> set bl"}), plus the
      standing membership @{term "set (follow (thrd S) u) \<subseteq> V"} making the array reads in bounds.  Proved by
      induction on @{term bl}, each recursive call discharged by the induction hypothesis.\<close>
lemma subtree_fold_imp_rule:
  assumes ps: "parent_spec (thrd S)"
      and fi_rule: "\<And>x a. x \<in> V \<Longrightarrow> <R ai a> fi x ai <\<lambda>_. R ai (f x a)>"
  shows "follow (thrd S) u = bl @ stp # rest \<Longrightarrow> stp \<notin> set bl \<Longrightarrow> set (follow (thrd S) u) \<subseteq> V \<Longrightarrow>
    <ndtree_assn V S Ti * R ai acc>
      subtree_fold_imp Ti stp u fi ai
    <\<lambda>_. ndtree_assn V S Ti * R ai (subtree_fold S stp u f acc)>"
proof (induct bl arbitrary: u acc)
  case Nil
  have uV: "u \<in> V" using Nil.prems(3) follow_hd_ps[OF ps, of u] follow_ne_ps[OF ps, of u] by (metis hd_in_set subsetD)
  have hd: "u = stp" using follow_hd_ps[OF ps, of u] Nil.prems(1) by simp
  have fval: "subtree_fold S stp u f acc = f u acc" using hd by (subst subtree_fold.simps) (simp add: Let_def)
  show ?case unfolding fval
    apply (subst subtree_fold_imp.simps)
    apply (sep_auto simp: hd heap: fi_rule[OF uV])
    done
next
  case (Cons b bs)
  have hd: "u = b" using follow_hd_ps[OF ps, of u] Cons.prems(1) by simp
  have une: "u \<noteq> stp" using Cons.prems(2) hd by auto
  have uV: "u \<in> V" using Cons.prems(3) follow_hd_ps[OF ps, of u] follow_ne_ps[OF ps, of u] by (metis hd_in_set subsetD)
  have flu: "follow (thrd S) u = u # (bs @ stp # rest)" using Cons.prems(1) hd by simp
  have tw_ne: "thrd S u \<noteq> None"
  proof
    assume "thrd S u = None"
    hence "follow (thrd S) u = [u]" by (subst follow_ps_simps[OF ps]) simp
    thus False using flu by simp
  qed
  then obtain w where tw: "thrd S u = Some w" by auto
  have fxy: "follow (thrd S) u = u # follow (thrd S) w" using tw by (subst follow_ps_simps[OF ps]) simp
  have fw: "follow (thrd S) w = bs @ stp # rest" using flu fxy by simp
  have notin': "stp \<notin> set bs" using Cons.prems(2) by simp
  have wsub: "set (follow (thrd S) w) \<subseteq> V" using Cons.prems(3) fxy by auto
  have fval: "subtree_fold S stp u f acc = subtree_fold S stp w f (f u acc)"
    using une tw by (subst subtree_fold.simps) (simp add: Let_def)
  note IH = Cons.hyps[OF fw notin' wsub]
  show ?case unfolding fval
    apply (subst subtree_fold_imp.simps)
    apply (sep_auto simp: une tw uV heap: fi_rule[OF uV] IH)
    done
qed

text \<open>Hence @{const iterate_root_opposed_imp} refines @{const iterate_root_opposed_impl}: under
      @{term "arb_invar r V S"}, @{term "v \<in> V"} and the single-step refinement of @{term fi} by @{term f},
      folding over the subtree of @{term v} leaves the imperative accumulator @{term ai} representing the
      functional result @{term "iterate_root_opposed_impl S v f acc"}.  The thread decomposition and membership
      premises of @{thm subtree_fold_imp_rule} come from @{thm block_props} (the block is the subtree in thread
      order, ending at @{term "lsuc S v"}) and @{thm follow_thrd_subset_V}.\<close>
lemma iterate_root_opposed_imp_rule:
  assumes inv: "arb_invar r V S" and vV: "v \<in> V"
      and fi_rule: "\<And>x a. x \<in> V \<Longrightarrow> <R ai a> fi x ai <\<lambda>_. R ai (f x a)>"
  shows "<ndtree_assn V S Ti * R ai acc>
           iterate_root_opposed_imp Ti v fi ai
         <\<lambda>_. ndtree_assn V S Ti * R ai (iterate_root_opposed_impl S v f acc)>"
proof -
  have pst: "parent_spec (thrd S)" using inv unfolding arb_invar_def by simp
  have bne: "block S v \<noteq> []" by (rule block_props(2)[OF inv vV])
  have blast': "last (block S v) = lsuc S v" by (rule block_props(3)[OF inv vV])
  have decomp: "follow (thrd S) v = block S v @ (case thrd S (lsuc S v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S) w)"
    by (rule block_props(1)[OF inv vV])
  define bl where "bl = butlast (block S v)"
  have blk: "block S v = bl @ [lsuc S v]" unfolding bl_def using append_butlast_last_id[OF bne] blast' by simp
  define rest where "rest = (case thrd S (lsuc S v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S) w)"
  have L: "follow (thrd S) v = bl @ (lsuc S v) # rest" using decomp blk rest_def by simp
  have distf: "distinct (follow (thrd S) v)" by (rule follow_distinct_ps[OF pst])
  have notin: "lsuc S v \<notin> set bl" using distf L by (auto simp: distinct_append)
  have treeV: "set (follow (thrd S) v) \<subseteq> V" by (rule follow_thrd_subset_V[OF inv vV])
  note SF = subtree_fold_imp_rule[where R=R and f=f and fi=fi and Ti=Ti and ai=ai, OF pst fi_rule L notin treeV]
  show ?thesis
    unfolding iterate_root_opposed_imp_def iterate_root_opposed_impl_def
    apply (sep_auto simp: vV heap: SF)
    done
qed

end
