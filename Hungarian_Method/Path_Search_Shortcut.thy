theory Path_Search_Shortcut
  imports Neighbourhood_Best_Scan Hungarian_Method_Top_Loop Directed_Set_Graphs.More_Arith
begin

section \<open>A Shortcut for Augmenting Paths of Length One\<close>

text \<open>Before a full path search, we try to augment along a single edge: for a free left vertex
      @{term l}, the neighbour @{term j} of minimum reduced cost is computed. If @{term j} is free,
      then raising the potential of @{term l} to this minimum makes the edge @{term "{l, j}"} tight
      and keeps the potential feasible, and @{term "[l, j]"} is an augmenting path. The free left
      vertices are tried in the order @{term left_order} until one succeeds. If none does, the full
      path search @{term path_search} is run.

      The combination @{term path_search_sc} tries the shortcut only if its first argument holds.
      Every branch satisfies the contract of the path search of @{locale hungarian_loop}, hence so
      does the combination, whatever its first argument is.\<close>

locale path_search_shortcut_spec =
  hungarian_loop_spec potential_abstract init_potential potential_invar empty_matching
    matching_invar augment matching_abstract edge_costs card_L card_R path_search G +
  nb_best_scan_spec rnb_current rnb_has rnb_move rnb_reset
  for potential_abstract :: "'potential \<Rightarrow> 'v \<Rightarrow> real"
    and init_potential potential_invar empty_matching matching_invar augment
    and matching_abstract :: "'matching \<Rightarrow> 'v set set"
    and edge_costs card_L card_R path_search G
    and rnb_current :: "'g \<Rightarrow> 'v \<Rightarrow> 'v" and rnb_has rnb_move rnb_reset +
  fixes buddy_lookup :: "'matching \<Rightarrow> 'v \<Rightarrow> 'v option"
    and potential_lookup :: "'potential \<Rightarrow> 'v \<Rightarrow> real option"
    and potential_upd :: "'v \<Rightarrow> real \<Rightarrow> 'potential \<Rightarrow> 'potential"
    and rnb_init :: 'g
    and edge_costs_code :: "'v \<Rightarrow> 'v \<Rightarrow> real"
    and left_order :: "'v list"
begin

definition "free M v = (buddy_lookup M v = None)"

definition "red \<pi> l r = edge_costs_code l r - abstract_real_map (potential_lookup \<pi>) r"

text \<open>One row: the cursors are threaded through the scans.\<close>

definition "row_try M \<pi> C l =
  (if free M l then
     (case best_of (red \<pi>) (free M) l C of
        (C', Some (x, j)) \<Rightarrow> (C', if free M j then Some (j, x) else None)
      | (C', None) \<Rightarrow> (C', None))
   else (C, None))"

definition "fs_step M \<pi> Cr l =
  (case Cr of (C, None) \<Rightarrow> (case row_try M \<pi> C l of (C', r) \<Rightarrow> (C', map_option (Pair l) r))
   | (C, Some _) \<Rightarrow> Cr)"

definition "first_success M \<pi> = foldl (fs_step M \<pi>) (rnb_init, None) left_order"

definition "shortcut M \<pi> =
  (case snd (first_success M \<pi>) of None \<Rightarrow> None
   | Some (l, j, x) \<Rightarrow> Some (l, j, potential_upd l x \<pi>))"

definition "path_search_sc b M \<pi> =
  (if b then
     (case shortcut M \<pi> of
        Some (l, j, \<pi>') \<Rightarrow> Next_Iteration [l, j] \<pi>'
      | None \<Rightarrow> path_search M \<pi>)
   else path_search M \<pi>)"

lemma path_search_sc_cases:
  "path_search_sc b M \<pi> = path_search M \<pi> \<or>
   (\<exists>l j \<pi>'. shortcut M \<pi> = Some (l, j, \<pi>') \<and> path_search_sc b M \<pi> = Next_Iteration [l, j] \<pi>')"
  by (auto simp: path_search_sc_def split: option.splits)

end

locale path_search_shortcut =
  path_search_shortcut_spec +
  nb_best_scan rnb_current rnb_has rnb_move rnb_reset rnb_invar rnb_abstract rnb_iterated
    rnb_remaining K
  for rnb_invar rnb_abstract rnb_iterated rnb_remaining K +
  fixes L R
  assumes G: "bipartite G L R" "set left_order = L" "L \<subseteq> K"
    and rnb_init: "rnb_invar rnb_init"
      "\<And>l. l \<in> L \<Longrightarrow> rnb_abstract rnb_init l = {r. {l, r} \<in> G}"
      "\<And>l. l \<in> L \<Longrightarrow> finite (rnb_abstract rnb_init l)"
    and edge_costs_code: "\<And>l r. \<lbrakk>{l, r} \<in> G; l \<in> L\<rbrakk> \<Longrightarrow> edge_costs_code l r = edge_costs {l, r}"
    and buddy: "\<And>M v. matching_invar M \<Longrightarrow>
                  buddy_lookup M v = None \<longleftrightarrow> v \<notin> Vs (matching_abstract M)"
    and potential: "\<And>\<pi>. potential_abstract \<pi> = abstract_real_map (potential_lookup \<pi>)"
      "\<And>\<pi> l x. \<lbrakk>potential_invar \<pi>; l \<in> L\<rbrakk> \<Longrightarrow> potential_invar (potential_upd l x \<pi>)"
      "\<And>\<pi> l x. potential_invar \<pi> \<Longrightarrow>
                potential_lookup (potential_upd l x \<pi>) = (potential_lookup \<pi>)(l \<mapsto> x)"
    and fallback:
      "\<And>M \<pi> B. \<lbrakk>path_search_precond M \<pi>; path_search M \<pi> = Dual_Unbounded\<rbrakk>
         \<Longrightarrow> \<exists>\<pi>'. feasible_min_perfect_dual G edge_costs \<pi>' \<and> sum \<pi>' (L \<union> R) > B"
      "\<And>M \<pi>. \<lbrakk>path_search_precond M \<pi>; path_search M \<pi> = Lefts_Matched\<rbrakk>
         \<Longrightarrow> L \<subseteq> Vs (matching_abstract M)"
      "\<And>M \<pi> \<pi>' p. \<lbrakk>path_search_precond M \<pi>; path_search M \<pi> = Next_Iteration p \<pi>'\<rbrakk>
         \<Longrightarrow> good_search_result M \<pi>' p"
begin

text \<open>A successful row.\<close>

definition "row_ok M \<pi> l j x =
  (l \<in> L \<and> free M l \<and> free M j \<and> {l, j} \<in> G \<and> x = red \<pi> l j \<and>
   (\<forall>r. {l, r} \<in> G \<longrightarrow> x \<le> red \<pi> l r))"

lemma row_try_invar:
  assumes "rnb_invar C" "rnb_abstract C = rnb_abstract rnb_init" "l \<in> L"
  shows "rnb_invar (fst (row_try M \<pi> C l)) \<and>
         rnb_abstract (fst (row_try M \<pi> C l)) = rnb_abstract rnb_init"
proof-
  have fin: "finite (rnb_abstract C l)" using rnb_init(3)[OF assms(3)] assms(2) by simp
  note B = best_of_props[OF assms(1) subsetD[OF G(3) assms(3)] fin, of "red \<pi>" "free M"]
  show ?thesis
    using B(1,2) assms(1,2) by (auto simp: row_try_def split: prod.splits option.splits)
qed

lemma fs_fold_props:
  assumes "set xs \<subseteq> L" "rnb_invar C" "rnb_abstract C = rnb_abstract rnb_init"
          "case res of None \<Rightarrow> True | Some (l, j, x) \<Rightarrow> row_ok M \<pi> l j x"
  shows "rnb_invar (fst (foldl (fs_step M \<pi>) (C, res) xs)) \<and>
         rnb_abstract (fst (foldl (fs_step M \<pi>) (C, res) xs)) = rnb_abstract rnb_init \<and>
         (case snd (foldl (fs_step M \<pi>) (C, res) xs) of None \<Rightarrow> True
          | Some (l, j, x) \<Rightarrow> row_ok M \<pi> l j x)"
  using assms
proof(induction xs arbitrary: C res)
  case (Cons l xs)
  have l: "l \<in> L" using Cons.prems(1) by simp
  define st where "st = fs_step M \<pi> (C, res) l"
  have st: "rnb_invar (fst st) \<and> rnb_abstract (fst st) = rnb_abstract rnb_init \<and>
            (case snd st of None \<Rightarrow> True | Some (l, j, x) \<Rightarrow> row_ok M \<pi> l j x)"
  proof(cases res)
    case (Some a)
    thus ?thesis using Cons.prems(2-4) by (simp add: st_def fs_step_def)
  next
    case None
    show ?thesis
    proof(cases "free M l")
      case False
      thus ?thesis using Cons.prems(2,3) None by (simp add: st_def fs_step_def row_try_def)
    next
      case True
      have N: "rnb_abstract C l = {r. {l, r} \<in> G}" using Cons.prems(3) rnb_init(2)[OF l] by simp
      have fin: "finite (rnb_abstract C l)" using rnb_init(3)[OF l] Cons.prems(3) by simp
      have lK: "l \<in> K" using l G(3) by auto
      note B = best_of_props[OF Cons.prems(2) lK fin, of "red \<pi>" "free M"]
      obtain C' b where Cb: "best_of (red \<pi>) (free M) l C = (C', b)" by fastforce
      show ?thesis
      proof(cases b)
        case None
        thus ?thesis
          using B(1,2) Cb \<open>res = None\<close> True Cons.prems(3)
          by (simp add: st_def fs_step_def row_try_def)
      next
        case (Some p)
        obtain x j where p: "p = (x, j)" by fastforce
        have bj: "j \<in> rnb_abstract C l" "x = red \<pi> l j" "\<forall>r\<in>rnb_abstract C l. x \<le> red \<pi> l r"
          using B(4)[of x j] Cb Some p by auto
        show ?thesis
          using B(1,2) bj Cb Some p \<open>res = None\<close> True l N Cons.prems(3)
          by (auto simp: st_def fs_step_def row_try_def row_ok_def)
      qed
    qed
  qed
  obtain C1 r1 where C1: "st = (C1, r1)" by fastforce
  have "foldl (fs_step M \<pi>) (C, res) (l # xs) = foldl (fs_step M \<pi>) (C1, r1) xs"
    by (simp add: st_def[symmetric] C1)
  thus ?case using Cons.IH[of C1 r1] st Cons.prems(1) by (simp add: C1)
qed simp

lemma first_success_props:
  "rnb_invar (fst (first_success M \<pi>))"
  "rnb_abstract (fst (first_success M \<pi>)) = rnb_abstract rnb_init"
  "snd (first_success M \<pi>) = Some (l, j, x) \<Longrightarrow> row_ok M \<pi> l j x"
  using fs_fold_props[where xs = left_order and C = rnb_init and res = None and M = M and \<pi> = \<pi>,
                      OF equalityD1[OF G(2)] rnb_init(1) refl]
  by (auto simp: first_success_def)

lemma shortcut_good:
  assumes "path_search_precond M \<pi>" "shortcut M \<pi> = Some (l, j, \<pi>')"
  shows "good_search_result M \<pi>' [l, j]"
proof-
  obtain x where x: "snd (first_success M \<pi>) = Some (l, j, x)" "\<pi>' = potential_upd l x \<pi>"
    using assms(2) by (auto simp: shortcut_def split: option.splits)
  have ok: "row_ok M \<pi> l j x" by (rule first_success_props(3)[OF x(1)])
  note pre = path_search_precondD[OF assms(1)]
  have l: "l \<in> L" "l \<notin> Vs (matching_abstract M)" and j: "j \<notin> Vs (matching_abstract M)"
    and lj: "{l, j} \<in> G" and xr: "x = red \<pi> l j" and xmin: "\<And>r. {l, r} \<in> G \<Longrightarrow> x \<le> red \<pi> l r"
    using ok buddy[OF pre(1)] by (auto simp: row_ok_def free_def)
  have other: "\<And>r. {l, r} \<in> G \<Longrightarrow> r \<noteq> l"
    using bipartite_edgeD(1)[OF _ G(1) l(1)] l(1) by (metis DiffD2)
  let ?p = "potential_abstract \<pi>" and ?p' = "potential_abstract \<pi>'"
  have pa: "?p' = ?p(l := x)"
    using potential(3)[OF pre(2)] x(2) by (auto simp: potential(1) abstract_real_map_def fun_eq_iff)
  have cost: "\<And>r. {l, r} \<in> G \<Longrightarrow> red \<pi> l r = edge_costs {l, r} - ?p r"
    using edge_costs_code l(1) by (simp add: red_def potential(1))
  show ?thesis
  proof(rule good_search_resultI)
    show "potential_invar \<pi>'" using potential(2)[OF pre(2) l(1)] x(2) by simp
    show "matching_abstract M \<subseteq> tight_subgraph G edge_costs ?p'"
    proof
      fix e assume e: "e \<in> matching_abstract M"
      then obtain u v where uv: "e = {u, v}" "{u, v} \<in> G" "edge_costs {u, v} = ?p u + ?p v"
        using pre(4) by (auto elim!: in_tight_subgraphE)
      have "u \<noteq> l" "v \<noteq> l" using l(2) e uv(1) by (auto simp: Vs_def)
      thus "e \<in> tight_subgraph G edge_costs ?p'"
        using uv by (intro in_tight_subgraphI) (auto simp: pa)
    qed
    show "feasible_min_perfect_dual G edge_costs ?p'"
    proof(rule feasible_min_perfect_dualI)
      fix e u v assume e: "e \<in> G" "e = {u, v}"
      have old: "?p u + ?p v \<le> edge_costs e" by (rule feasible_min_perfect_dualD[OF pre(5) e])
      show "?p' u + ?p' v \<le> edge_costs e"
      proof(cases "u = l")
        case True
        hence G': "{l, v} \<in> G" using e by simp
        thus ?thesis using xmin[OF G'] cost[OF G'] other[OF G'] e True by (simp add: pa)
      next
        case False
        show ?thesis
        proof(cases "v = l")
          case True
          hence G': "{l, u} \<in> G" using e by (simp add: insert_commute)
          thus ?thesis
            using xmin[OF G'] cost[OF G'] other[OF G'] e True by (simp add: pa insert_commute)
        next
          case False
          thus ?thesis using old \<open>u \<noteq> l\<close> by (simp add: pa)
        qed
      qed
    qed
    show "set (edges_of_path [l, j]) \<subseteq> tight_subgraph G edge_costs ?p'"
      using lj other[OF lj] xr cost[OF lj]
      by (auto simp: pa insert_commute intro!: in_tight_subgraphI)
    have nM: "{l, j} \<notin> matching_abstract M" using l(2) by (auto simp: Vs_def)
    have jV: "j \<in> Vs G" using lj by (auto simp: Vs_def)
    have pth: "path G [l, j]" using lj jV by (auto intro: path.intros)
    have aug: "matching_augmenting_path (matching_abstract M) [l, j]"
      using nM l(2) j by (auto intro!: matching_augmenting_pathI alt_list.intros)
    show "graph_augmenting_path G (matching_abstract M) [l, j]"
      using pth aug other[OF lj] by auto
  qed
qed

lemma path_search_sc_correct:
  "\<And>M \<pi> B. \<lbrakk>path_search_precond M \<pi>; path_search_sc b M \<pi> = Dual_Unbounded\<rbrakk>
     \<Longrightarrow> \<exists>\<pi>'. feasible_min_perfect_dual G edge_costs \<pi>' \<and> sum \<pi>' (L \<union> R) > B"
  "\<And>M \<pi>. \<lbrakk>path_search_precond M \<pi>; path_search_sc b M \<pi> = Lefts_Matched\<rbrakk>
     \<Longrightarrow> L \<subseteq> Vs (matching_abstract M)"
  "\<And>M \<pi> \<pi>' p. \<lbrakk>path_search_precond M \<pi>; path_search_sc b M \<pi> = Next_Iteration p \<pi>'\<rbrakk>
     \<Longrightarrow> good_search_result M \<pi>' p"
proof-
  fix M \<pi> B assume "path_search_precond M \<pi>" "path_search_sc b M \<pi> = Dual_Unbounded"
  thus "\<exists>\<pi>'. feasible_min_perfect_dual G edge_costs \<pi>' \<and> sum \<pi>' (L \<union> R) > B"
    using path_search_sc_cases[of b M \<pi>] fallback(1) by auto
next
  fix M \<pi> assume "path_search_precond M \<pi>" "path_search_sc b M \<pi> = Lefts_Matched"
  thus "L \<subseteq> Vs (matching_abstract M)"
    using path_search_sc_cases[of b M \<pi>] fallback(2) by auto
next
  fix M \<pi> \<pi>' p assume a: "path_search_precond M \<pi>" "path_search_sc b M \<pi> = Next_Iteration p \<pi>'"
  show "good_search_result M \<pi>' p"
    using path_search_sc_cases[of b M \<pi>]
  proof
    assume "path_search_sc b M \<pi> = path_search M \<pi>"
    thus ?thesis using a fallback(3) by simp
  next
    assume "\<exists>l j \<pi>''. shortcut M \<pi> = Some (l, j, \<pi>'') \<and>
                      path_search_sc b M \<pi> = Next_Iteration [l, j] \<pi>''"
    thus ?thesis using a shortcut_good by auto
  qed
qed

end

end