theory BFS_Refinement_2
  imports BFS_3 BFS_Subprocedures  Directed_Set_Graphs.Pair_Graph_Imperative
"HOL-Imperative_HOL.Imperative_HOL" "HOL-Library.IArray" BFS_Refinement
CSR_Graph
begin

lemma triple_res_ht_ex_pre_and_post_I:"(\<And> x. <P x> c <\<lambda> (r1,r2,r3). Q x r1 r2 r3>) 
           \<Longrightarrow> <\<exists>\<^sub>A x. P x> c <\<lambda> (r1,r2,r3). \<exists>\<^sub>A x. Q x r1 r2 r3>"
  by sep_auto

lemma "<a \<mapsto>\<^sub>a xs * a' \<mapsto>\<^sub>a xs' * \<up> (i < length xs \<and> j < length xs')>
       do {Array.upd i x a; Array.upd j x' a'}
      <\<lambda> r. a \<mapsto>\<^sub>a xs[i:=x] * r \<mapsto>\<^sub>a xs'[j:=x'] * \<up> (i < length xs \<and> j < length xs')>"
  by sep_auto

record ('imp_dist, 'imp_vis, 'imp_cf) BFS_state_imp =
     dists:: "'imp_dist" current:: "'imp_cf" visited:: "'imp_vis" current_dist::nat

locale BFS_Imperative_spec = 
fixes imp_src_to_cf::"'imp_src \<Rightarrow> 'imp_cf Heap"
and set_srcs_visited::" 'imp_vis \<Rightarrow> 'imp_src \<Rightarrow> 'imp_vis Heap"
and next_frontier_and_current_imp::"'imp_cf \<Rightarrow> 'imp_vis \<Rightarrow> ('imp_cf \<times> 'imp_vis) Heap"
and imp_cf_is_empty::"'imp_cf \<Rightarrow> bool Heap"
and in_vis::"'ver \<Rightarrow> 'imp_vis \<Rightarrow> bool Heap"
and set_all_dists_in_front_imp::"'imp_dist \<Rightarrow> 'imp_cf \<Rightarrow> nat \<Rightarrow> 'imp_dist Heap"
begin

partial_function (heap) BFS_dist_imp::
  "('imp_dist, 'imp_vis, 'imp_cf) BFS_state_imp \<Rightarrow> ('imp_dist, 'imp_vis, 'imp_cf) BFS_state_imp Heap"
  where 
 "BFS_dist_imp state = 
   do { b \<leftarrow> imp_cf_is_empty (current state);
       if b then Heap_Monad.return state
       else do{ (current', visited') \<leftarrow>  next_frontier_and_current_imp (current state)  (visited state);
               let d = current_dist state;
               dist' \<leftarrow> set_all_dists_in_front_imp (dists state) current' (Suc d);
               BFS_dist_imp (state \<lparr>dists:= dist', visited := visited', current := current',
                                 current_dist := Suc d\<rparr>)}}"

definition "initial_state_imp empty_vis src_imp imp_some_dist=  
  do {v \<leftarrow> set_srcs_visited empty_vis src_imp;
      cf \<leftarrow> imp_src_to_cf src_imp;
      dists \<leftarrow> set_all_dists_in_front_imp  imp_some_dist cf 0;
      return \<lparr>dists = dists, current = cf, visited = v, current_dist = 0\<rparr>}"

definition "check_reachable empty_vis src_imp imp_some_dist t =
    do {init \<leftarrow> initial_state_imp empty_vis src_imp imp_some_dist;
        final \<leftarrow> BFS_dist_imp init;
        in_vis t (visited final)}"
end

locale BFS_Imperative = 
 BFS_3.BFS_distance  where expand_tree = expand_tree and insert = insert and some_dist = some_dist+
 BFS_Imperative_spec where  imp_src_to_cf = imp_src_to_cf
  and in_vis = in_vis and set_all_dists_in_front_imp = set_all_dists_in_front_imp
 for  imp_src_to_cf :: "'imp_src \<Rightarrow> 'imp_cf Heap"
  and expand_tree::"'adjmap \<Rightarrow> 'vset \<Rightarrow> 'vset \<Rightarrow> 'adjmap"
  and insert :: "'ver \<Rightarrow> 'vset \<Rightarrow> 'vset" 
  and in_vis::"'ver \<Rightarrow> 'imp_vis \<Rightarrow> bool Heap"
  and some_dist::"'dist" and set_all_dists_in_front_imp::"'imp_dist \<Rightarrow> 'imp_cf \<Rightarrow> nat \<Rightarrow> 'imp_dist Heap"+
fixes  G_imp::"'imp_G"
 and graph_assn::"'adjmap \<Rightarrow> 'imp_G \<Rightarrow> assn"
 and imp_src_assn::"'vset \<Rightarrow> 'imp_src \<Rightarrow> assn"
 and imp_dag_assn::"'adjmap \<Rightarrow> 'imp_dag \<Rightarrow> assn"
 and imp_cf_assn::"'vset \<Rightarrow> 'imp_cf \<Rightarrow> assn"
 and imp_vis_assn::"'vset \<Rightarrow> 'imp_vis \<Rightarrow> assn"
 and imp_dist_assn::"'dist \<Rightarrow> 'imp_dist \<Rightarrow> assn"
assumes imp_sf_is_empty: "\<And> S Si. <imp_cf_assn S Si> imp_cf_is_empty Si 
                       <\<lambda> b. imp_cf_assn S Si * \<up>(b \<longleftrightarrow> S = \<emptyset>\<^sub>N)>"
 and imp_src_to_cf: "\<And> S Si. <imp_src_assn S Si> imp_src_to_cf Si 
                      <\<lambda> r. imp_cf_assn S r>"
 and set_srcs_visited: 
  "\<And> S Si. 
    <imp_src_assn S Si * imp_vis_assn vset_empty empty_vis> set_srcs_visited empty_vis Si 
           <\<lambda> r. imp_vis_assn S r * imp_src_assn S Si>"
 and next_frontier_and_current_imp:  "\<And> cf imp_cf vis imp_vis.
    <imp_cf_assn cf imp_cf * imp_vis_assn vis imp_vis * graph_assn G G_imp>
    next_frontier_and_current_imp imp_cf imp_vis
    <\<lambda> (r1, r2). imp_cf_assn (fst (next_frontier_and_current cf vis)) r1 * 
                 imp_vis_assn (snd (next_frontier_and_current cf vis)) r2 * graph_assn G G_imp>"
(*and in_vis_rule: "\<And>vis visi s. <imp_vis_assn vis visi> in_vis s visi 
            <\<lambda> r. imp_vis_assn vis visi * \<up> (r \<longleftrightarrow> isin vis s)>"*)
and set_all_dists_in_front_imp:
    "\<And> d id. <imp_dist_assn d id * imp_cf_assn cf cfi> set_all_dists_in_front_imp id cfi n
            <\<lambda> r. imp_dist_assn (set_all_dists_in_set d cf n) r * imp_cf_assn cf cfi>"
begin

definition "state_assn (s::('dist, 'vset) BFS_dist_state)
    (imp_s::('imp_dist, 'imp_vis, 'imp_cf) BFS_state_imp) = 
  (imp_vis_assn (BFS_dist_state.visited s) (BFS_state_imp.visited imp_s) *
   imp_cf_assn (BFS_dist_state.current s) (BFS_state_imp.current imp_s)*
   imp_dist_assn (BFS_dist_state.dists s) (BFS_state_imp.dists imp_s) *
    \<up> (BFS_dist_state.current_dist s = BFS_state_imp.current_dist imp_s))"

lemma BFS_refine:
  "<graph_assn G G_imp * state_assn s s_imp >
  BFS_dist_imp s_imp 
  <\<lambda> s_imp'. graph_assn G G_imp * state_assn (BFS_dist_impl s) s_imp'>"
proof(induction arbitrary: s s_imp rule: BFS_dist_imp.fixp_induct, goal_cases)
  case 1
  then show ?case 
    by auto
next
  case (2 s s_imp)
  then show ?case 
    by simp
next
  case (3 f s s_imp)

  note IH = 3(1)[of 
     "\<lparr>BFS_dist_state.dists = dists, current = current, visited = visited, BFS_dist_state.current_dist = n\<rparr>"
     "\<lparr>BFS_state_imp.dists = imp_dists, current = imp_current, visited = imp_visited, BFS_state_imp.current_dist = n\<rparr>"
     for imp_dists imp_current imp_visited dists current visited n] 

  note IH[sep_heap_rules] = IH[unfolded state_assn_def, simplified, rule_format]

  show ?case
    apply(cases s, cases s_imp)
    subgoal for dists current visited current_dist imp_dists imp_current imp_visited imp_current_dist
      apply (rewrite in "<_> _ <\<hole>>" BFS_dist_impl.simps)
      using next_frontier_and_current_imp IH  imp_sf_is_empty set_all_dists_in_front_imp
      apply(auto split!: if_split prod.split simp add: state_assn_def Let_def mod_pure_star_dist)
      by sep_auto
    done
qed

lemma initial_refine:
 "<imp_vis_assn vset_empty empty_vis* imp_src_assn srcs srcs_imp * imp_dist_assn some_dist imp_some_dist>
  initial_state_imp empty_vis srcs_imp imp_some_dist
 <\<lambda> si. state_assn initial_dist_state si>"
  apply(auto simp add: initial_dist_state_def state_assn_def initial_state_imp_def)
  using imp_src_to_cf set_all_dists_in_front_imp set_srcs_visited 
  by sep_auto

lemma BFS_program_behaviour:
  "<imp_vis_assn vset_empty empty_vis * imp_src_assn srcs srcs_imp * imp_dist_assn some_dist imp_some_dist * graph_assn G G_imp>
   do { si \<leftarrow> initial_state_imp empty_vis srcs_imp imp_some_dist;
        BFS_dist_imp si }
   < \<lambda> si'. state_assn (BFS_dist_impl initial_dist_state) si' * graph_assn G G_imp>"
  using initial_refine BFS_refine 
  by sep_auto

lemma check_reachable_rule:
 "<imp_vis_assn vset_empty empty_vis * imp_src_assn srcs srcs_imp * imp_dist_assn some_dist imp_some_dist * graph_assn G G_imp> 
   check_reachable empty_vis srcs_imp imp_some_dist t
  <\<lambda> b.  graph_assn G G_imp *
      \<up> (b \<longleftrightarrow> isin (BFS_dist_state.visited (BFS_dist_impl initial_dist_state)) t)>" 
  unfolding check_reachable_def
  using initial_refine BFS_refine in_vis_rule
  by (sep_auto simp: state_assn_def)
end

locale imp_fixed_univ_set =
  fixes is_fixed_univ_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> assn"
  assumes only_in_univ: "is_fixed_univ_set U S Si = (is_fixed_univ_set U S Si * \<up> (S \<subseteq> U))"
(*
locale imp_set_empty = imp_set +
  constrains is_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> assn"
  fixes empty :: "'s Heap"
  and U::"'a set"
  assumes empty_rule[sep_heap_rules]: "<emp> empty <is_set {}>"
*)(*
locale imp_fixed_univ_set_is_empty = imp_fixed_univ_set +
  constrains is_fixed_univ_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> assn"
  fixes is_empty :: "'s \<Rightarrow> bool Heap"
  assumes is_empty_rule[sep_heap_rules]: 
    "<is_fixed_univ_set U s p> is_empty p <\<lambda>r. is_fixed_univ_set U s p * \<up>(r \<longleftrightarrow> s={})>"
*)
locale imp_fixed_univ_set_memb = imp_fixed_univ_set +
  constrains is_fixed_univ_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> assn"
  fixes memb :: "'a \<Rightarrow> 's \<Rightarrow> bool Heap"
  assumes memb_rule[sep_heap_rules]: 
    "<is_fixed_univ_set U s p * \<up> (a \<in> U)> memb a p <\<lambda>r. is_fixed_univ_set U s p * \<up>(r \<longleftrightarrow> a \<in> s)>"

locale imp_fixed_univ_set_ins = imp_fixed_univ_set +
  constrains is_fixed_univ_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> assn"
  fixes ins :: "'a \<Rightarrow> 's \<Rightarrow> 's Heap"
  assumes ins_rule[sep_heap_rules]: 
    "<is_fixed_univ_set U s p * \<up> (a \<in> U)> ins a p <is_fixed_univ_set U (Set.insert a s)>"

locale imp_fixed_univ_set_distinct_ins = imp_fixed_univ_set +
  constrains is_fixed_univ_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> assn"
  fixes distinct_ins :: "'a \<Rightarrow> 's \<Rightarrow> 's Heap"
  assumes distinct_ins_rule[sep_heap_rules]: 
    "<is_fixed_univ_set U s p * \<up> (a \<in> U \<and> a \<notin> s)> distinct_ins a p <is_fixed_univ_set U (Set.insert a s)>"

locale imp_fixed_univ_set_rest = imp_fixed_univ_set +
  constrains is_fixed_univ_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> assn"
  fixes reset :: "'s \<Rightarrow> 's Heap"
  assumes ins_rule[sep_heap_rules]: 
    "<is_fixed_univ_set U s p > reset p <is_fixed_univ_set U {}>"
  

locale BFS_subprocedures_lists =
  imp_fixed_univ_set_memb where is_fixed_univ_set = is_visited_set
  and memb = visited_memb +
  imp_fixed_univ_set_distinct_ins where is_fixed_univ_set = is_visited_set
for is_visited_set and visited_memb::"nat \<Rightarrow> 'imp_vis \<Rightarrow> bool Heap"
begin

definition "Vs (G::nat \<Rightarrow> nat list option) = \<Union> {{u, v} | u v vs. G u = Some vs \<and> v \<in> set vs }"

fun inner_loop where
"inner_loop Gi sindicesi eindicesi u (front, frontpt, vis) =
   iterate_neighbourhood Gi sindicesi eindicesi u 
     (\<lambda> u v (front, frontpt, vis) . 
          do {b \<leftarrow> visited_memb v vis;
              if \<not> b then do { front' \<leftarrow> Array.upd frontpt v front;
                               vis' \<leftarrow> distinct_ins v vis;
                               return (front', Suc frontpt, vis')}
              else return (front, frontpt, vis)})
      (front, frontpt, vis)"

definition "front_assn G vis (front::nat list) fronti frontp = 
  (\<exists>\<^sub>A frontlist. fronti \<mapsto>\<^sub>a frontlist * \<up> (length frontlist > card (Vs G) \<and>
     frontp < length frontlist - card (Vs G) + card vis \<and> frontp \<le> length frontlist \<and>
        rev (take frontp (frontlist)) = front
     \<and> vis \<subseteq> (Vs G) \<and> set front \<subseteq> (Vs G)))"

lemma inner_loop_rule:
  assumes "(front', vis') = 
          foldl (\<lambda>x y. case x of (nf, vis) \<Rightarrow> if y \<notin> set vis then (y # nf, y # vis) else (nf, vis))
            (front, vis) (case G u of None \<Rightarrow> [] | Some ys \<Rightarrow> ys)"
          "finite (Vs G)"
  shows "<CSR_assn_raw G Gi sindicesi eindicesi nha sindices eindices
          * is_visited_set (Vs G) (set vis) visi * front_assn G (set vis) front fronti frontp>
  inner_loop Gi sindicesi eindicesi u (fronti, frontp, visi)
 <\<lambda> (fronti', frontp', visi'). 
   CSR_assn_raw G Gi sindicesi eindicesi nha sindices eindices
       * is_visited_set (Vs G) (set vis') visi' * front_assn G (set vis') front' fronti' frontp'>"
proof-
  define acc_assn where 
    "acc_assn = (\<lambda> (front, vis) (fronti, frontp, visi). 
        is_visited_set (Vs G) (set vis) visi * front_assn G (set vis) front fronti frontp)"
  define fi where "fi = (\<lambda> (u::nat) (v::nat) (front, frontpt, vis) . 
          do {b \<leftarrow> visited_memb v vis;
              if \<not> b then do { front' \<leftarrow> Array.upd frontpt v front;
                               vis' \<leftarrow> distinct_ins v vis;
                               return (front', Suc frontpt, vis')}
              else return (front, frontpt, vis)})"
  define f where "f = (\<lambda>(nf, vis) y. if (y::nat) \<notin> set vis then (y # nf, y # vis) else (nf, vis))"
  have assms_1': "(front', vis') = 
          foldl f (front, vis) (case G u of None \<Rightarrow> [] | Some ys \<Rightarrow> ys)"
    using assms(1) by(auto simp add: f_def case_prod_unfold)
  show ?thesis
    unfolding inner_loop.simps fi_def[symmetric]
    apply(rule ht_cons_prec)
      defer
      defer
      apply(rule iterate_neighbourhood_raw_rule[where F = emp and acc_assn = acc_assn, simplified, of _ _ fi,
          where nhlists = G and nha = nha and sindices = sindices and eindices = eindices
           and acc = "(front, vis)" and f = "\<lambda> x. f"])
    subgoal for acc acci x vs
    proof(cases acc, cases acci, goal_cases)
      case (1 front vis fronti frontp visi)
      have x_in_Vs: "x \<in> (Vs G)" 
        using 1(1,2)
        by(auto simp add: Vs_def)
      show ?case 
        unfolding 1
        unfolding acc_assn_def front_assn_def
        unfolding acc_assn_def f_def fi_def 
        unfolding prod.case front_assn_def ex_assn_move_out(2)
      proof(cases "x \<notin> set vis", goal_cases)
        case 1
        show ?case
          apply(subst (2) if_P)
           using 1 apply force
           unfolding prod.case 
           using x_in_Vs apply sep_auto
           subgoal 
             by (smt (verit, ccfv_SIG) Nat.add_diff_assoc2 assms(2) card_mono card_seteq le_add_diff_inverse2 le_trans
                 nat_add_left_cancel_le nat_less_le x_in_Vs)
           subgoal for h xa ha r hb ra
             using distinct_ins_rule[of "(Vs G)" "set vis" visi x] x_in_Vs apply sep_auto
               apply(rule mod_exI[of _ "xa[frontp := x]"])
               apply (sep_auto simp: mod_pure_star_dist)
               apply(subst take_Suc_conv_app_nth)
                apply simp
             by (metis take_Suc_conv_app_nth take_update_last)
           subgoal for h xa ha r
             apply sep_auto
             apply(rule mod_exI[of _ "xa"])
             apply sep_auto
             using "1" by blast
           done
       next
         case 2
         thus ?case
           by sep_auto
       qed
     qed
     subgoal
       unfolding acc_assn_def prod.case 
       by sep_auto
     subgoal for x
       apply(clarsimp split!: option.split prod.split)
       subgoal for front frontpt vis
         unfolding acc_assn_def front_assn_def prod.case ex_assn_move_out(2)
         apply(rule matr.impl_of_exes_assn)
         using assms(1)
         by sep_auto
       subgoal for vs front frontpt vis
         unfolding acc_assn_def front_assn_def prod.case
         apply(clarsimp split!: option.split prod.split)
         subgoal for front' vis'
           unfolding ex_assn_move_out(2)
           apply(rule matr.impl_of_exes_assn)
           using assms_1' 
           by sep_auto
         done
       done
     done
 qed

fun outer_loop where
  "outer_loop Gi sindicesi eindicesi (old_front, old_frontp) (front, frontpt, vis) = 
    do{iterate_range_strict old_front 0 old_frontp 
             (inner_loop Gi sindicesi eindicesi) (front, frontpt, vis)}"

definition "old_front_assn G (front::nat list) fronti frontp = 
  (\<exists>\<^sub>A frontlist. 
    fronti \<mapsto>\<^sub>a frontlist * \<up> ( frontp < length frontlist \<and> rev (take frontp (frontlist)) = front
    \<and> card (Vs G) < length frontlist))"

lemma outer_loop_rule:
  assumes "(front', vis') = 
   foldl (\<lambda>(nf, vis) u. 
       foldl (\<lambda>x y. case x of (nf, vis) \<Rightarrow> if y \<notin> set vis then (y # nf, y # vis) else (nf, vis))
            (nf, vis) (case G u of None \<Rightarrow> [] | Some ys \<Rightarrow> ys)) 
   (front, vis) (rev old_front)"
          "finite (Vs G)"
  shows "<CSR_assn_raw G Gi sindicesi eindicesi nha sindices eindices
          * is_visited_set (Vs G) (set vis) visi * front_assn G (set vis) front fronti frontp
          * old_front_assn G old_front old_fronti old_frontp>
  outer_loop Gi sindicesi eindicesi (old_fronti, old_frontp) (fronti, frontp, visi)
 <\<lambda> (fronti', frontp', visi'). 
   CSR_assn_raw G Gi sindicesi eindicesi nha sindices eindices
       * is_visited_set (Vs G) (set vis') visi' * front_assn G (set vis') front' fronti' frontp'
       * old_front_assn G old_front old_fronti old_frontp>"
proof-
  define acc_assn where 
    "acc_assn = (\<lambda> (front, vis) (fronti, frontp, visi). 
        is_visited_set (Vs G) (set vis) visi * front_assn G (set vis) front fronti frontp)"
  define f where "f = (\<lambda>  (nf, vis) u. foldl (\<lambda>x y. case x of (nf, vis) \<Rightarrow> if y \<notin> set vis then (y # nf, y # vis) else (nf, vis))
            (nf, vis) (case G u of None \<Rightarrow> [] | Some ys \<Rightarrow> ys))"
  show ?thesis
    unfolding outer_loop.simps 
    unfolding old_front_assn_def ex_assn_move_out(2)
    apply(rule triple_res_ht_ex_pre_and_post_I)
    subgoal for old_front_list
    apply(rule ht_cons_prec)
      defer
    defer
      apply(rule iterate_range_strict_rule[of old_front_list 0 old_frontp acc_assn 
          "CSR_assn_raw G Gi sindicesi eindicesi nha sindices eindices 
           * \<up> (old_frontp < length old_front_list \<and> rev (take old_frontp (old_front_list)) = old_front
                \<and> card (Vs G) < length old_front_list)" 
           "inner_loop Gi sindicesi eindicesi" f old_fronti "(front, vis)" "(fronti, frontp, visi)"
             ])
    subgoal for acc acci x
      apply(clarsimp simp add: acc_assn_def split: prod.split simp del: inner_loop.simps)
      subgoal for front vis front' vis' fronit' frontp visi'
        apply(rule ht_cons_prec)
        defer defer
        apply(rule ht_frame[OF inner_loop_rule[of front' vis' front vis G _ _ _ _  nha sindices eindices],
              where R = "\<up> (old_frontp < length old_front_list \<and> 
                rev (take old_frontp (old_front_list)) = old_front \<and>
                   card (Vs G) < length old_front_list)"])
        by(sep_auto simp: f_def assms(2))
      done
      using assms(1)
      by(sep_auto split: prod.split simp: old_front_assn_def acc_assn_def f_def nths_intervall_strict_as_drop_and_take)
  
      done
qed

fun imp_cf_assn where 
   "imp_cf_assn (G::nat \<Rightarrow> nat list option) front (fronti, frontp, buffer_fronti) =
      (\<exists>\<^sub>A frontlist buffer_frontlist. fronti \<mapsto>\<^sub>a frontlist *  buffer_fronti \<mapsto>\<^sub>a buffer_frontlist *
       \<up> (length frontlist > card (Vs G) \<and> frontp < length frontlist  \<and> 
          rev (take frontp (frontlist)) = front \<and> length buffer_frontlist > card (Vs G)
          \<and> set front \<subseteq> (Vs G)))"

definition "imp_src_to_cf = (\<lambda> x. return x)"
definition "imp_src_assn = imp_cf_assn"

fun imp_cf_is_empty where
 "imp_cf_is_empty (fronti, frontp, buffer_fronti) = 
          return (frontp = 0)"

lemma imp_cf_is_empty_rule:
  "<imp_cf_assn G S Si> imp_cf_is_empty Si <\<lambda>b. imp_cf_assn G S Si * \<up> (b = (S = []))>"
  by(cases Si) sep_auto
term inner_loop

fun set_srcs_visited where
  "set_srcs_visited (imp_vis::'imp_vis) (fronti, frontp, buffer_fronti) =
   do { iterate_range_strict fronti 0 frontp 
             (\<lambda> v vis. do {b \<leftarrow> visited_memb v vis;
                           if \<not> b then distinct_ins v vis
                           else return vis})
             imp_vis}"

lemma foldl_insert:"foldl (\<lambda>S x. if x \<in> S then S else Set.insert x S) A xs = set xs \<union> A"
  by(induction xs arbitrary: A) auto

lemma set_srcs_visited_rule:
      "<imp_src_assn G S Si * is_visited_set (Vs G) {} empty_vis> 
          set_srcs_visited empty_vis Si
        <\<lambda>r. is_visited_set (Vs G) (set S) r * imp_src_assn G S Si>"
  unfolding imp_src_assn_def
  apply(cases Si)
  subgoal for fronti frontp buffer_fronti
    apply simp
    apply(rule ht_ex_pre_and_post_I)+
    subgoal for frontlist buffer_frontlist
  apply(rule ht_cons_prec)
      defer defer
        apply(rule iterate_range_strict_rule[where acc_assn = "is_visited_set (Vs G)"
             and F = "buffer_fronti \<mapsto>\<^sub>a buffer_frontlist *
    \<up> (card (Vs G) < length frontlist \<and>
       frontp < length frontlist \<and> rev (take frontp frontlist) = S \<and> card (Vs G) < length buffer_frontlist \<and> set S \<subseteq> Vs G)"
         and f = "\<lambda> S x. if x \<notin> S then Set.insert x S else S" and list = frontlist and acc = Set.empty])
     by (sep_auto simp: foldl_insert nths_intervall_strict_as_drop_and_take)
   done
  done

abbreviation "imp_dist_assn_raw G dlist d di 
   \<equiv> (di \<mapsto>\<^sub>a dlist * 
          \<up>((\<forall> i \<in> dom G. i < length dlist \<and> d i = dlist ! i)))"

definition "imp_dist_assn G d di 
   = (\<exists>\<^sub>A dlist. di \<mapsto>\<^sub>a dlist * 
          \<up>((\<forall> i \<in> Vs G. i < length dlist \<and> d i = dlist ! i)))"

fun set_all_dists_in_front_imp where
 "set_all_dists_in_front_imp di (fronti, frontp, buffer_fronti) n = 
       iterate_range_strict fronti 0 frontp 
         (\<lambda> v di. Array.upd v n di) di"

lemma foldl_fun_upd_same: "foldl (\<lambda>d x y. if x = y then n else d y) d xs =
       (\<lambda> x. if x \<in> set xs then n else d x)"
  by(induction xs arbitrary: d)  auto

lemma set_all_dists_in_front_imp_rule:
  "<imp_dist_assn G d di * imp_cf_assn G cf cfi> set_all_dists_in_front_imp di cfi n
    <\<lambda>r. imp_dist_assn G (\<lambda>y. if y \<in> set cf then n else d y) r * imp_cf_assn G cf cfi>"
  apply(cases cfi)
  subgoal for fronti frontp buffer_fronti
    apply simp 
    apply(rule ht_ex_pre_and_post_I)+
    subgoal for frontlist buffer_frontlist
    apply(rule ht_cons_prec)
      defer defer
        apply(rule iterate_range_strict_rule[where list = frontlist
               and acc_assn = "imp_dist_assn G" and acc = d
               and F = "buffer_fronti \<mapsto>\<^sub>a buffer_frontlist *
          \<up> (card (Vs G) < length frontlist \<and> frontp < length frontlist \<and>
        rev (take frontp frontlist) = cf \<and> card (Vs G) < length buffer_frontlist \<and> set cf \<subseteq> Vs G)"
               and f = "\<lambda> d. \<lambda> x y. if x = y then n else d y"])
      by (sep_auto simp: imp_dist_assn_def nths_intervall_strict_as_drop_and_take 
         nths_intervall_strict_as_drop_and_take foldl_fun_upd_same)
    done
  done

fun next_frontier_and_current_imp where
  "next_frontier_and_current_imp Gi sindicesi eindicesi (fronti, frontp, buffer_fronti) imp_vis =
   do{
      (front', frontpt', vis') \<leftarrow> 
       outer_loop Gi sindicesi eindicesi (fronti, frontp) (buffer_fronti, 0, imp_vis);
      return ((front', frontpt', fronti), vis')}"

lemma verts_rw:
   "\<Union> {{v1, v2} |v1 v2. (v1, v2) \<in> {(u, v). v \<in> set (case G u of None \<Rightarrow> [] | Some vset \<Rightarrow> vset)}} =
    \<Union> {uu. \<exists>u v vs. uu = {u, v} \<and> G u = Some vs \<and> v \<in> set vs}"
  by auto (metis insert_iff)+

sublocale BFS_subprocedures_3
  where empty = "\<lambda> x. None"
  and delete = "\<lambda> (x::nat) M. \<lambda> y. if y = x then None else M y"
  and insert = Cons
  and isin = "\<lambda> xs x. x \<in> set xs"
  and t_set = set
  and sel = hd
  and  update = "\<lambda> x z M. \<lambda> y. if y = x then Some z else M y"
  and adjmap_inv = "\<lambda> _. True"
  and vset_empty = Nil
  and vset_delete = "\<lambda> x xs. filter (\<lambda> y. x \<noteq> y) xs"
  and vset_inv = "\<lambda> _. True"
  and union = append
  and inter = "\<lambda> xs ys. filter (\<lambda> y. y \<in> set ys) xs"
  and diff = "\<lambda> xs ys. filter (\<lambda> y. y \<notin> set ys) xs"
  and fold_vset = "\<lambda>  f xs a. foldl (\<lambda>x y. f y x) a xs"
  and fold_adjmap = "\<lambda>  f xs a. foldl (\<lambda>x y. f y x) a xs"
  and lookup = "\<lambda> M x. M x"
  and fold2_vset = "\<lambda>  f xs a. foldl (\<lambda>x y. f y x) a xs"
  and fold2_vset' = "\<lambda>  f xs a. foldl (\<lambda>x y. f y x) a (rev xs)"
  and fast_insert = Cons
  and vset_inv2 = distinct
  apply unfold_locales
  apply (auto intro: exI[of _ "rev _"] simp add: foldl_conv_foldr) 
  done


lemma next_frontier_and_current_imp_rule:
  fixes G::"nat \<Rightarrow> nat list option"
  assumes "finite (Vs G)" "G_imp = Gi" 
  shows 
    "<imp_cf_assn G cf imp_cf * is_visited_set (Vs G) (set vis) imp_vis *
     CSR_assn_raw G G_imp sindicesi eindicesi nha sindices eindices>
    next_frontier_and_current_imp Gi sindicesi eindicesi imp_cf imp_vis
    <\<lambda>(r1, r2).
        imp_cf_assn G (fst (next_frontier_and_current cf vis)) r1 *
        is_visited_set (Vs G) (set (snd (next_frontier_and_current cf vis))) r2 *
        CSR_assn_raw G G_imp sindicesi eindicesi nha sindices eindices>"
proof(cases imp_cf, cases "next_frontier_and_current cf vis", goal_cases)
  case (1 fronti frontp buffer_fronti cf' vis')
  show ?case
    unfolding 1 fst_conv snd_conv next_frontier_and_current_imp.simps
    apply(rule ht_bind[where R = "\<lambda> x. (case x of
          (fronti', frontp', visi') \<Rightarrow>
            CSR_assn_raw G Gi sindicesi eindicesi nha sindices eindices * is_visited_set (Vs G) (set vis') visi' *
            front_assn G (set vis') cf' fronti' frontp' *
            old_front_assn G cf fronti frontp)"])
    apply(rule ht_cons_prec)
    defer defer
    apply(rule outer_loop_rule[of cf' vis' G Nil vis cf _ _  _ nha sindices eindices, OF _ assms(1)])
    subgoal
      unfolding 1(2)[symmetric] next_frontier_and_current_def Graph.neighbourhood_def 
      apply(rule fun_cong[of "foldl _ _" "foldl _ _"])
      apply(rule fun_cong[of "foldl _" "foldl _"])
      apply(rule arg_cong[of _ _ foldl])
      by fast
      defer
    subgoal
      apply (sep_auto intro: simp: front_assn_def old_front_assn_def)
      apply(rule matr.impl_of_exes_assn)+
      subgoal for frontlist buffer_frontlist
      apply(subst only_in_univ)
        apply(subst ent_pure_pre_iff)+
        apply rule
        apply(subst ent_pure_post_iff)+
      apply rule+
        subgoal
          unfolding assms(2)
          apply(elim conjE)
          by (metis  ent_refl  assms(2) only_in_univ  star_aci(2) star_aci(3))
        subgoal
          apply rule+
          subgoal 
            by auto
          subgoal
            by (metis mod_false pure_false star_false_left star_false_right)
          done
        subgoal
          by sep_auto
        done
      done
    subgoal
      by sep_auto
    subgoal for x
    proof(cases x, goal_cases)
      case (1 fronti' frontpt' visi' )
      show ?case 
        unfolding 1 prod.case
        apply(rule ht_cons_post_prec)
        apply(rule ht_return_sp)
        apply (sep_auto )
        unfolding front_assn_def ex_assn_move_out old_front_assn_def
        apply(rule ent_ex_preI)+
        subgoal for frontlist buffer_frontlist

          apply(rule ent_ex_postI[of _ _ buffer_frontlist])
          apply(rule ent_ex_postI[of _ _ frontlist])
        proof(goal_cases)
          case 1
          have assn_rw:"CSR_assn_raw G Gi sindicesi eindicesi nha sindices eindices * is_visited_set (Vs G) (set vis') visi' *
    (fronti' \<mapsto>\<^sub>a buffer_frontlist *
     \<up> (card (Vs G)< length buffer_frontlist \<and>
        frontpt' < length buffer_frontlist - card (Vs G) + card (set vis') \<and>
        frontpt' \<le> length buffer_frontlist \<and> rev (take frontpt' buffer_frontlist) = cf' \<and> set vis' \<subseteq> (Vs G)
         \<and> set cf' \<subseteq> (Vs G))) *
    (fronti \<mapsto>\<^sub>a frontlist *
     \<up> (frontp < length frontlist \<and> rev (take frontp frontlist) = cf \<and> card (Vs G) < length frontlist)) = 
       CSR_assn_raw G Gi sindicesi eindicesi nha sindices eindices * is_visited_set (Vs G) (set vis') visi' *
  fronti' \<mapsto>\<^sub>a buffer_frontlist * fronti \<mapsto>\<^sub>a frontlist *
   \<up> (card (Vs G) < length buffer_frontlist \<and>
        frontpt' < length buffer_frontlist - card (Vs G) + card (set vis') \<and>
        frontpt' \<le> length buffer_frontlist \<and> rev (take frontpt' buffer_frontlist) = cf' \<and> set vis' \<subseteq> (Vs G) 
        \<and> set cf' \<subseteq> (Vs G) \<and>
         frontp < length frontlist \<and> rev (take frontp frontlist) = cf \<and> card (Vs G) < length frontlist)"
            by (smt (verit, best) merge_pure_star mult_left_assoc star_aci(3))
        
          show ?case
           apply(insert 1)
            unfolding assn_rw ent_pure_pre_iff ent_pure_post_iff
            apply rule+
            subgoal
              unfolding assms(2)
              by (metis ent_refl star_aci(3) star_aci(2))
            using assms(1) card_mono[of "(Vs G)" "set vis'"] 
            by (auto simp: mod_pure_star_dist)
        qed
        done
    qed
    done
qed

lemma Vs_same:"dVs (Graph.digraph_abs G) =  Vs G"
  unfolding Vs_def Graph.digraph_abs_def Graph.neighbourhood_def dVs_def verts_rw[of G]
  by order

context fixes nha sindices eindices ::"nat list"
and Gi sindicesi eindicesi::"nat array"
assumes finite_Vs:"finite (Vs G)"
begin

interpretation imp_bfs: BFS_Imperative
where empty = "\<lambda> x. None"
  and delete = "\<lambda> x M. \<lambda> y. if y = x then None else M y"
  and insert = Cons
  and isin = "\<lambda> xs x. x \<in> set xs"
  and t_set = set
  and sel = hd
  and  update = "\<lambda> x z M. \<lambda> y. if y = x then Some z else M y"
  and adjmap_inv = "\<lambda> _. True"
  and vset_empty = Nil
  and vset_delete = "\<lambda> x xs. filter (\<lambda> y. x \<noteq> y) xs"
  and vset_inv = "\<lambda> _. True"
  and union = append
  and inter = "\<lambda> xs ys. filter (\<lambda> y. y \<in> set ys) xs"
  and diff = "\<lambda> xs ys. filter (\<lambda> y. y \<notin> set ys) xs"
  and lookup = "\<lambda> M x. M x"
  and vset_inv2 = distinct
  and G = G
  and next_frontier_and_current = next_frontier_and_current
and next_frontier_and_current_imp = "next_frontier_and_current_imp Gi sindicesi eindicesi"
and imp_cf_assn = "imp_cf_assn G"
and expand_tree = expand_tree
and graph_assn = "\<lambda> G Gi. CSR_assn_raw G Gi sindicesi eindicesi nha sindices eindices"
and imp_vis_assn = "\<lambda> xs. is_visited_set (Vs G) (set xs)"
and G_imp = Gi
and imp_cf_is_empty = imp_cf_is_empty
and imp_src_assn = "imp_src_assn G"
and imp_src_to_cf = imp_src_to_cf
and set_srcs_visited = set_srcs_visited
and in_vis = visited_memb
and dist_invar = "\<lambda> d S. S \<subseteq> (Vs G)"
and dist_lookup = "\<lambda> d x. d x"
and set_all_dists_in_set = "\<lambda> d S n. \<lambda> y. if y \<in> set S then n else d y"
and some_dist = id
and imp_dist_assn = "imp_dist_assn G"
and set_all_dists_in_front_imp = set_all_dists_in_front_imp
proof(unfold_locales, goal_cases)
  case (1 BFS_tree frontier vis)
  then show ?case 
    by blast
next
  case (2 BFS_tree frontier vis)
  then show ?case 
    using expand_tree(2) by presburger
next
  case (3 BFS_tree frontier vis)
  then show ?case 
     using expand_tree(3) by presburger   
next
  case (4 frontier vis front' vis')
  then show ?case 
    using next_frontier_and_curent_correct by blast
next
  case (5 frontier vis front' vis')
  then show ?case
    using next_frontier_and_curent_correct(2)[OF _ _ 5(3,4,5,6)] by blast
next
  case (6 frontier vis front' vis')
  then show ?case 
    by force
next
  case (7 frontier vis front' vis')
  then show ?case 
    using next_frontier_and_curent_correct(4)[OF _ _ 7(3,4,5,6)] by blast
next
  case (8 S)
  then show ?case 
    by simp
next
  case (9 dists front S n)
  thus ?case 
    unfolding Vs_same by simp
next
  case (10 dists front S n x)
  thus ?case 
    by presburger
next
  case (11 dists front S n x)
  thus ?case 
    unfolding Vs_same 
    apply(subst if_not_P)
    by force+
next
  case 12
  thus ?case 
    by simp
next
  case (13 S Si)
  then show ?case 
    using imp_cf_is_empty_rule by fast
next
  case (14 S Si)
  then show ?case 
    by(sep_auto simp: imp_src_assn_def imp_src_to_cf_def)
next
  case (15 empty_vis S Si)
  then show ?case 
    using set_srcs_visited_rule[of G S Si empty_vis] by simp
next
  case (16 cf imp_cf vis imp_vis)
  then show ?case 
    using next_frontier_and_current_imp_rule[OF finite_Vs refl, of G cf imp_cf vis imp_vis]
    by fast
next 
  case (17 vis visi s)
  then show ?case 
    using memb_rule[of "Vs G" "set vis" visi s] by force
next
  case (18 cf cfi n d id)
  then show ?case 
    using set_all_dists_in_front_imp_rule[of G d id cf cfi n] by force
qed

end
end

definition "barr_fixed_univ_set_assn U S Si
       = (\<exists>\<^sub>A blist. Si \<mapsto>\<^sub>a blist * 
             \<up> ((\<forall> u \<in> U. u < length blist \<and> blist ! u \<longleftrightarrow> (u\<in> S)) \<and> S \<subseteq> U))"

interpretation imp_fixed_univ_set barr_fixed_univ_set_assn
  apply unfold_locales 
  apply(rule ent_iffI)
  by(sep_auto simp: barr_fixed_univ_set_assn_def)

definition "barr_fixed_univ_set_memb x S =
     Array.nth S x"

interpretation imp_fixed_univ_set_memb barr_fixed_univ_set_assn barr_fixed_univ_set_memb
  apply unfold_locales
  apply(sep_auto simp: barr_fixed_univ_set_assn_def barr_fixed_univ_set_memb_def)
  subgoal for U s p a blist aa b
    apply(rule mod_exI[of _ blist])
    apply (sep_auto simp: mod_pure_star_dist)
    sledgehammer
  
  find_theorems "_ \<Turnstile> _ * _ = _"

end