theory Edmonds_Gallai_Computation
  imports Edmonds_Gallai_Blossoms
begin 

lemma Union_of_singletons_in_set:
  "\<Union> {{x} | x. x \<in> X} = X"
  by auto

context compute_alt_path
begin

lemma termination_conditions_edg:
  assumes "\<not> if1_cond F" "\<not> if2_cond F" "forest_invar M F" "Vs G - Vs M \<subseteq> aevens F" 
          "aevens F \<subseteq> Vs G" "\<lbrace> F \<rbrace> \<subseteq> G"
    shows "edmonds_gallai G M {{v} |v. v \<in> aevens F} (aodds F)" (is ?thesis1)
          "Neighbourhood G (\<Union> {{v} |v. v \<in> aevens F}) = aodds F" (is ?thesis2)
proof-               
  have goal1: "disjoint {{v} |v. v \<in> aevens F}"
    by(auto simp add: disjoint_def)
  have goal2: "\<Union> {{v} |v. v \<in> aevens F} \<subseteq> Vs G" 
    using assms(5) by blast
  have goal3: "X \<in> {{v} |v. v \<in> aevens F} \<Longrightarrow> X \<noteq> {}" for X by auto
  have goal5: "\<lbrakk>X \<in> {{v} |v. v \<in> aevens F}; Y \<in> {{v} |v. v \<in> aevens F}; X \<noteq> Y\<rbrakk>
                \<Longrightarrow> X \<leftarrow>|\<rightarrow>\<^bsub>G\<^esub> Y" for X Y
    using assms(2)
    by(auto simp add: connected_set_of_vertices_def if2_cond_def)
  have goal6: "aodds F = Neighbourhood G (\<Union> {{v} |v. v \<in> aevens F})"
    using assms
    unfolding  Union_of_singletons_in_set
    by(subst finial_forest_evens'_Neighbourhood[of F]) auto
  have goal7: "\<lbrakk>X \<in> {{v} |v. v \<in> aevens F}; x \<in> X\<rbrakk>
        \<Longrightarrow> \<exists>M. graph_matching ( G \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x}" for x X
    by(auto intro!: exI[of _ "{}"])
  have goal8: "\<lbrakk>v \<in> Vs G\<rbrakk> \<Longrightarrow> even_vert G M v \<longleftrightarrow> v \<in> \<Union> {{v} |v. v \<in> aevens F}" for v
  proof(rule, goal_cases)
    case 1
    then obtain p where "odd (length p)"
     "alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p)"
     "hd p \<notin> Vs M" "last p = v" "distinct p" "(path G p \<or> length p = 1)"
     by(elim even_vertE) auto
   hence p_props: "odd (length p)"
     "alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p)"
     "hd p \<notin> Vs M" "last p = v" "distinct p" "path G p" "1 \<le> length p"
     using 1(1) by(all \<open>cases p rule: list_cases3\<close>) auto
   hence p_in_G:"set p \<subseteq> Vs G"
     by (simp add: subset_path_Vs)
   have edges_p_in_G: "set (edges_of_path p) \<subseteq> G"
     by (simp add: p_props(6) path_edges_subset)
   have alt_list_p:"alt_list (\<lambda>x. x \<in> aevens F) (\<lambda>x. x \<in> aodds F) p"
    using termination_conditions_alt_paths_alternating_labels[OF
               assms(1,2,3,4) p_props(2,7,3) refl p_in_G edges_p_in_G]
    by simp
  hence "last p \<in> aevens F"
    using last_odd_P2 p_props(1) by auto
  thus ?case
    using p_props(4) by blast
next
  case 2
  hence even_v: "v \<in> aevens F" by auto
   thm get_path
   have "even_alt_path G M (last (get_path F v)) (rev (get_path F v)) v"
  proof-
    note get_path = get_path[OF assms(3) even_v refl]
    moreover have "path G (rev (get_path F v))"
      using "2"(1) assms(6) get_path
        path_subset[of "\<lbrace> F \<rbrace>" "get_path F v" G] path1[of v G]
      by(auto simp add:  walk_betw_def rev_path_is_path_iff)
    moreover have "alt_path M (rev (get_path F v))" 
      using get_path
      by(auto intro: rev_of_rev_alt_path_is_alt_path)
    moreover have "hd (rev (get_path F v)) = last (get_path F v)"
      by (simp add: hd_rev)
    moreover have "last (rev (get_path F v)) = v"
      using get_path last_rev[of "get_path F v"] by(auto simp add: walk_betw_def)
    moreover have "last (get_path F v) \<notin> Vs M" 
      using assms(3) get_path roots(3)[of M F] by auto
    ultimately show ?thesis
      by(auto intro!: even_alt_pathI)
  qed  
  thus ?case
    by(auto simp add: even_vert_even_alt_path)
qed

  have goal9: "X \<in> {{v} |v. v \<in> aevens F} \<Longrightarrow> \<exists>x. x \<in> X \<and> Vs ( M \<lbrakk>X\<rbrakk>) = X - {x}" for X
    using matching(2) 
    by (auto elim!: in_graph_inter_VsE simp add: vs_member)+
  have goal10: "Delta M (\<Union> {{v} |v. v \<in> aevens F} \<union> aodds F) = {}"
  proof(rule ccontr, goal_cases)
    case 1
    then obtain e where "e \<in> Delta M (aevens F \<union> aodds F)"
      by (auto simp add: Union_of_singletons_in_set)
    thus ?case
    proof(elim in_DeltaE, goal_cases)
      case (1 u v)
      then show ?case 
      proof(elim UnE, goal_cases)
        case 1
        then show ?case 
          using assms(1,2,3,4,6) matching(2)
            finial_forest_evens'_Neighbourhood[of F] subsetD[of M G e]
            in_NeighbourhoodI[of u v G "aevens F"]
          by auto
      next
        case 2
        moreover hence "v \<in> aevens F" 
          using "1"(3) assms(3) evens_and_odds(3)[of M F] higher_forest_properties(2,3)[of M F u v]
          by auto
        ultimately show ?case 
          by auto
      qed
    qed
  qed

  have goal11: "D \<in> {{v} |v. v \<in> aevens F} \<Longrightarrow> card (Delta M D) \<le> 1" for D
  proof(goal_cases)
    case 1
    then obtain v where v: "v \<in> aevens F" "D = {v}"
      by auto
    show ?case
    proof(rule ccontr, goal_cases)
      case 1
      then obtain e1 e2 where "e1 \<in> Delta M {v}"  "e2 \<in> Delta M {v}" "e1 \<noteq> e2"
        using card_ge_1_obtain_two_distinc_elems[of "Delta M {v}"] v(2)
        by auto
      then show ?case 
        using matching(1)
       by(auto dest: matching_edges_not_eqD(1) elim!: in_DeltaE)
   qed
 qed

  have goal12: "Vs G - \<Union> {{v} |v. v \<in> aevens F} \<subseteq> Vs M"
    using assms(4)
    unfolding Union_of_singletons_in_set
    by auto

  have goal13: "M \<inter> (G \<lbrakk>aodds F\<rbrakk>) = {}"
  proof(rule equals0I, unfold Int_iff, elim conjE in_graph_inter_VsE, goal_cases)
    case (1 e)
    then obtain x y where xy: "e = {x, y}" "x \<noteq> y"
      by auto
    have "y \<in> aevens F" 
      using "1"(1,3)  evens_and_odds(3)[OF assms(3)]
          higher_forest_properties(2,3)[OF assms(3), of y x]  xy(1)
      by(auto simp add: insert_commute)
    hence "y \<notin> aodds F"
      using assms(3) evens_and_odds(4) by fastforce
    then show ?case 
      using 1 xy by auto
  qed

  show ?thesis1
   by(rule edmonds_gallaiI  goal1 goal2 goal3 goal5 goal6 goal7 goal8 goal9 goal10
           goal11 goal12 goal13 | 
      assumption)+
  show ?thesis2
    by (simp add: goal6)
qed

lemma compute_alt_path_or_edg_from_tree_2:
  assumes invars: "forest_invar M F" 
  and ret: "compute_alt_path_or_pedg F = PEDG \<D>"
  and init: "finite \<lbrace>F\<rbrace>" "\<lbrace>F\<rbrace> \<subseteq> G" "aevens F \<subseteq> Vs G"
  and unmatcheds_even: "Vs G - Vs M \<subseteq> aroots F"
shows "\<nexists>p. matching_augmenting_path M p \<and> path G p \<and> distinct p" (is ?thesis1)
      "edmonds_gallai G M \<D> (Neighbourhood G (\<Union> \<D>))" (is ?thesis2)
proof-
  have fun_dom: "compute_alt_path_dom F" 
    using compute_alt_path_dom init(1,2) invars by blast
  hence None:"compute_alt_path F = None"
    using ret by(auto simp add: compute_alt_path_or_pedg_same'[of F, symmetric])
  show ?thesis1
    by(intro compute_alt_path_from_tree_2 [OF assms(1) _ assms(3,4,6)] None)
  obtain F' where F': "\<not> if1_cond F'" "\<not> if2_cond F'" "forest_invar M F'" 
            "aroots F' = aroots F" "\<D> = {{v} |v. v \<in> aevens F'}" "aevens F' \<subseteq> Vs G" "\<lbrace> F' \<rbrace> \<subseteq> G"
    using what_if_search_fails_pedg[OF assms(2,3,4,1,5)] by auto
  have Vs_with_M_in_aevens:"Vs G - Vs M \<subseteq> aevens F'"
    by (metis F'(3,4) roots(2) subset_trans unmatcheds_even)
  show ?thesis2           
    using termination_conditions_edg[OF  F'(1,2,3) Vs_with_M_in_aevens F'(6,7)] F'(5)
    by simp
qed

definition "compute_edg =
  (case compute_alt_path_or_pedg (empty_forest unmatcheds) of 
    PEDG \<D> \<Rightarrow> (\<D>, Neighbourhood G (\<Union> \<D>)))"

lemma compute_edg_correct:
  "\<lbrakk>compute_alt_path (empty_forest unmatcheds) = None\<rbrakk> \<Longrightarrow>
    edmonds_gallai G M (fst compute_edg) (snd compute_edg)"
 using compute_alt_path_or_edg_from_tree_2(2)[OF 
            init_props(1) _ init_props(2,3)  init_evens_in_G init_props(4)]
  by(auto simp add: compute_edg_def compute_alt_path_or_pedg_same initial_dom 
             split: alt_search_res.split)
end

locale find_aug_path_edg =
find_aug_path where sel = sel
for sel::"'a set \<Rightarrow> 'a"+
fixes edg_search::"'a set set \<Rightarrow> 'a set set \<Rightarrow> ('a set set \<times> 'a set)"
and sel_from_sets::"('a set \<Rightarrow> bool) \<Rightarrow> 'a set set \<Rightarrow> 'a set"
assumes edg_search_sound: 
 "\<lbrakk>graph_invar G; matching M; M \<subseteq> G; blos_search G M = None\<rbrakk>
     \<Longrightarrow> edmonds_gallai G M (fst (edg_search G M)) (snd (edg_search G M))" 
assumes sel_from_sets:
  "\<And> \<D> P. \<lbrakk>finite \<D>; \<exists> D \<in> \<D>. P D\<rbrakk> \<Longrightarrow> sel_from_sets P \<D> \<in> \<D>"
  "\<And> \<D> P. \<lbrakk>finite \<D>; \<exists> D \<in> \<D>. P D\<rbrakk> \<Longrightarrow> P (sel_from_sets P \<D>)"
begin

function (domintros) find_edg where
  "find_edg G M = 
     (case blos_search G M of Some match_blossom_res \<Rightarrow>
        (case match_blossom_res of Blossom stem cyc \<Rightarrow>
            (let u = create_vert (Vs G);
                 s = Vs G - (set cyc);
                 quotG = quot.quotG s u;
                 (\<D>, A) = find_edg (quotG G) (quotG M)
                 in if Delta G (set cyc) = {}
                    then (insert (set cyc) \<D>, A)
                    else let D = sel_from_sets (\<lambda> D. u \<in> D) \<D>;
                             \<D>' = \<D> - {D} \<union> {D - {u} \<union>  (set cyc)}
                         in (\<D>', A)))
      | _ \<Rightarrow> edg_search G M)"
  by pat_completeness auto

thm find_aug_path_dom
lemma find_edg_dom:
  assumes  "matching M" "M \<subseteq> E" "graph_invar E" 
  shows "find_edg_dom (E,M)"
  using assms
proof(induction "find_aug_path_meas E" arbitrary: E M rule: less_induct)
  case less
  have step: "find_edg_dom
        (quot_graph (\<lambda>v. if v \<in> Vs E \<and> v \<notin> set cyc then v else create_vert (Vs E)) E -
         {{create_vert (Vs E)}},
         quot_graph (\<lambda>v. if v \<in> Vs E \<and> v \<notin> set cyc then v else create_vert (Vs E)) M -
         {{create_vert (Vs E)}})" 
    if "blos_search E M = Some (Blossom stem cyc)" for stem cyc
  proof- 
    note 1 = that
      let ?s = "(Vs E - (set cyc))"
      let ?u = "(create_vert (Vs E))"
      have "match_blossom M stem cyc"
        "path E (stem @ cyc)"
        using bloss_algo_sound(2) 1 less.prems(1,2,3) by auto
      then have "set cyc \<subseteq> Vs E"
        using path_suff subset_path_Vs
        by metis
      then have "Vs E - ?s = set cyc"
        by auto
      moreover have "?s \<subseteq> Vs E"
        by auto
      moreover have "card (set cyc) \<ge> 2"
        using blossom_cycle_longer_2[OF \<open>match_blossom M stem cyc\<close>] .
      moreover have "finite (Vs E)"
        by (simp add: less.prems(3))
      ultimately have measure_less:"find_aug_path_meas (quot.quotG ?s ?u E) < find_aug_path_meas E"
        using 1 less.prems(3)           
        by(intro card_Vs_lt[of ?s E]) auto
      moreover have finite_quot:"finite (quot.quotG ?s ?u E)"
        by (simp add: \<open>finite (Vs E)\<close> quot_graph_finite')
      moreover have "((Vs E) - set cyc) \<subset> (Vs E)"
        using blossom_diff[OF \<open>graph_invar E\<close> \<open>match_blossom M stem cyc\<close> \<open>path E (stem@cyc)\<close>].  
      hence dblton_new: "dblton_graph (quot.quotG ?s ?u E)"
        apply(intro doublton_quot[where E = E])
        using \<open>graph_invar E\<close> create_vert_works
        by auto
      moreover have "matching (quot.quotG ?s ?u M)"
        apply (intro matching_quotM[where s = ?s and stem = stem and C=cyc and E=E])
        subgoal using \<open>((Vs E) - set cyc) \<subset> (Vs E)\<close> .
        subgoal using \<open>graph_invar E\<close> .
        subgoal using \<open>match_blossom M stem cyc\<close> .
        subgoal using less(2) .
        subgoal using less.prems(2) by auto
        subgoal ..
        done
      moreover have "(quot.quotG ?s ?u M) \<subseteq> quot.quotG ?s ?u E"
        by (simp add: less.prems(2) Diff_mono graph_subset_quot_subset)
      moreover have "graph_invar (quot.quotG ?s ?u E)"
        using dblton_new finite_quot finite_dbl_finite_verts by auto
      ultimately show ?thesis
        using measure_less
        by(intro less(1)) auto
    qed
    thus ?case
      by(rule find_edg.domintros) 
  qed

context 
  fixes s::"'a set" and E::"'a set set"
  assumes quot_assms: "s\<subset>Vs E" "graph_invar E"
begin
interpretation quot: quot sel E s "(create_vert (Vs E))"
  apply(unfold_locales)
  using quot_assms create_vert_works 
  by auto

lemma card_Vs_lt:
  assumes "1 < card (Vs E - s)"
  shows "find_aug_path_meas (quot.quotG E) < find_aug_path_meas E"
  unfolding find_aug_path_meas_def
  apply (rule quot.card_Vs_quotG)
  using quot_assms assms
  by auto

lemmas matching_quotM=quot.matching_quotM

lemmas doublton_quot = quot.doubleton_quot

lemmas aug_path_works_in_contraction = quot.aug_path_works_in_contraction

lemmas finite_quot = quot.finite_quot

lemmas doubleton_quot = quot.doubleton_quot

lemmas refine = quot.refine

lemmas pre_emonds_gallai_lonely_blossom =quot.pre_emonds_gallai_lonely_blossom

lemmas graph_invar_quotG = quot.graph_invar_quotG

lemmas max_card_matching_equiv_blossom_contraction = 
     quot.max_card_matching_equiv_blossom_contraction

lemmas emonds_gallai_connected_blossom=
  quot.emonds_gallai_connected_blossom

lemmas emonds_gallai_connected_blossom_obtain_D = 
  quot.emonds_gallai_connected_blossom_obtain_D

lemmas emonds_gallai_lonely_blossom =
  quot.emonds_gallai_lonely_blossom
end

lemma find_edg_correct:
  assumes  "graph_invar E" "max_card_matching E M"
  shows "edmonds_gallai E M (fst (find_edg E M)) (snd (find_edg E M))"
  using assms
proof(induction rule:  find_edg.pinduct[OF find_edg_dom, of M E], goal_cases)
  case 1
  then show ?case 
    using assms(2) max_card_matching_def by blast
next
  case 2
  then show ?case 
    by (simp add: assms(2) max_card_matchingDs(1))
next
  case 3
  then show ?case 
    by (simp add: assms(1))
next
  case (4 G M)
  note IH = this
  show ?case
    unfolding find_edg.psimps[OF IH(1)]
  proof(cases "blos_search G M", goal_cases)
    case 1
    then show ?case
      using  max_card_matchingDs[OF IH(4)]
      by(auto intro!: edg_search_sound simp add: IH(3) max_card_matching_subgraphD)
  next
    case (2 res)
    note two = this
    have matching_M: "matching M" and graph_matching_M: "graph_matching G M"
      using IH(4) max_card_matchingDs by auto
    have M_in_G: "M \<subseteq> G"
      by (simp add: IH(4) max_card_matchingDs(1))
    have no_p:"\<nexists> p. graph_augmenting_path G M p" 
      using IH(3) max_card_matchingD[OF IH(4)]  Berge[of M G] finite_Vs_then_finite[of G] 
            finite_subset[of M G]
      by auto
    obtain stem cyc where res_def: "res = Blossom stem cyc"
      using no_p bloss_algo_sound[OF IH(3) matching_M M_in_G] 2
      by(cases res) auto
    have a_blossom: "blossom G M stem cyc"
      by(intro bloss_algo_sound(2)[OF IH(3) matching_M M_in_G, of stem cyc])
        (simp add: "2" res_def)
    define u where "u = create_vert (Vs G)"
    define s where "s = Vs G - set cyc"
    define quotG where "quotG = (\<lambda>G. quot_graph (\<lambda>v. if v \<in> s then v else u) G - {{u}})"
    have "set cyc \<subseteq> Vs G"
        using a_blossom path_suff[of G stem cyc] subset_path_Vs[of G cyc]
        by simp
    then have Vs_G_cyc:"Vs G - s = set cyc"
        by (auto simp add: s_def)
     moreover have "s \<subseteq> Vs G"
        by (auto simp add: s_def)
     moreover have "card (set cyc) \<ge> 2"
       using a_blossom blossom_cycle_longer_2 by blast
     ultimately have s_string_in_G:"s \<subset> Vs G" 
       by auto
     have quot_fold:
        "quot_graph (\<lambda>v. if v \<in> s then v else create_vert (Vs G)) GG - {{create_vert (Vs G)}} =
          quotG GG" for GG
       unfolding quotG_def u_def by simp
     
     define \<D> where  "\<D> = fst (find_edg (quotG G) (quotG M))"
     define A where "A = snd (find_edg (quotG G) (quotG M))"

    define u' where "u' = create_vert (insert u (Vs G))"
    have u'_props: "create_vert (Vs G) \<notin> Vs G" "u' \<notin> Vs G" "u' \<noteq> create_vert (Vs G)"
      using IH(3) create_vert_works 
      by(auto simp add: u'_def u_def)
    have max_card_matching_quot: "max_card_matching (quotG G) (quotG M)"
      using max_card_matching_equiv_blossom_contraction[OF s_string_in_G IH(3) a_blossom
                graph_matching_M s_def u'_props(1), simplified quot_fold] IH(4)
      by simp
    hence Vs_quot_M_in_quot_Vs: "Vs (quotG G) \<supseteq> Vs (quotG M)"
      by (simp add: Vs_subset max_card_matchingDs(1))
     have IH_applied: "edmonds_gallai (quotG G) (quotG M) \<D> A"
       unfolding \<D>_def A_def
     proof(rule IH(2)[OF two res_def u_def s_def], goal_cases)
       case 1
       then show ?case 
         using graph_invar_quotG IH(3) quotG_def s_string_in_G u_def 
         by presburger
     next
       case 3
       then show ?case 
         using IH(4)
         using max_card_matching_equiv_blossom_contraction[OF s_string_in_G IH(3) a_blossom
                 graph_matching_M s_def, simplified quot_fold]
         by (simp add: u'_props(1))
     next
       case 2
       thus ?case
         using IH(3) graph_invar_quotG quotG_def s_string_in_G u_def by presburger
     qed 
     have grapn_invar_quot: "graph_invar (quotG G)"
       using IH(3) graph_invar_quotG quotG_def s_string_in_G u_def by presburger
    show ?case
     unfolding 2 res_def option.case  match_blossom_res.case
    proof(cases "Delta G (set cyc) = {}", goal_cases)
      case 1
      have "edmonds_gallai G M (insert (set cyc) \<D>) A"
        using IH_applied IH(4) u'_props 
        by (intro emonds_gallai_lonely_blossom[OF s_string_in_G IH(3) _ 1 _ a_blossom],
            unfold  quot_fold)
            (auto simp add: s_def)
      thus ?case
        unfolding Let_def quot_fold[simplified s_def]
        by(cases "find_edg (quotG G) (quotG M)")(simp add: "1" \<D>_def A_def)
    next
      case 2
      define D where "D = sel_from_sets ((\<in>) u) \<D>" 

      note obtainD1 =
           emonds_gallai_connected_blossom_obtain_D[OF s_string_in_G IH(3) _ 2 _ a_blossom,
              simplified quot_fold[simplified s_def]]
      note obtainD2 =obtainD1[OF IH_applied s_def IH(4) u'_props]
      moreover have finite_\<D>: "finite \<D>" 
        using IH_applied
        by(auto dest!: edmonds_gallaiD(2)
             simp add: finite_UnionD finite_subset grapn_invar_quot)
      ultimately have D_props: "D \<in> \<D>" "create_vert (Vs G) \<in> D"
        using sel_from_sets[of \<D> "(\<in>) u"]
        by(auto simp add: D_def u_def)
      note new_pedg1 =
           emonds_gallai_connected_blossom[OF s_string_in_G IH(3) _ 2 _ a_blossom,
              simplified quot_fold[simplified s_def]]
      note new_pedg2 = new_pedg1[OF IH_applied s_def IH(4) u'_props D_props, folded u_def]
      thus ?case
        unfolding Let_def quot_fold[simplified s_def]
        by(cases "find_edg (quotG G) (quotG M)")
          (simp add: "2" D_def \<D>_def u_def A_def)
    qed
  qed
qed

end

locale find_aug_path_pedg_use = find_aug_path_use where sel = sel and E = E + 
   find_aug_path_edg where sel = sel 
   for sel::"'a set \<Rightarrow> 'a" and E::"'a set set"
begin

interpretation find_max_match_intrp: find_max_match E find_aug_path
  apply unfold_locales
  subgoal using find_aug_path_complete[OF _ _ _ graph] by force
  subgoal using find_aug_path_sound[OF _ _ _ graph] by force
  done
(*
definition "find_decomposition M=
  (let M = find_max_matching {}
   in (find_edg E M))"

lemma find_matching_has_max_card:
  "max_card_matching E (find_max_matching {})"
  using find_max_matching_works(1,2,4) finite_subset finite_E
  by(auto intro!: max_card_matchingI')
*)
lemmas compute_pedg_spec = edg_search_sound

lemma find_decomposition_correct_with_matching:
  "max_card_matching E M \<Longrightarrow> edmonds_gallai E M (fst (find_edg E M)) (snd (find_edg E M))"
  by (auto intro!: find_edg_correct simp add: dblton_E finite_Vs)
(*
lemma find_decomposition_correct:
  "\<exists> M. max_card_matching E M \<and>
        edmonds_gallai E M (fst find_decomposition) (snd find_decomposition)"
  using find_decomposition_correct_with_matching find_matching_has_max_card by blast
*)
end

locale compute_match_blossom'_edg_use =
compute_match_blossom'_use where E = E
for E::"'a set set"+
fixes compute_edg::"'a set set \<Rightarrow>'a set set \<Rightarrow> ('a set set \<times> 'a set)" 
and sel_from_sets::"('a set \<Rightarrow> bool) \<Rightarrow> 'a set set \<Rightarrow> 'a set"
assumes compute_edg: 
  "\<And> E M.  \<lbrakk>graph_invar E; matching M; M \<subseteq> E; compute_alt_path E M = None\<rbrakk>
            \<Longrightarrow> edmonds_gallai E M (fst (compute_edg E M)) (snd (compute_edg E M))"
assumes sel_from_sets:
  "\<And> \<D> P. \<lbrakk>finite \<D>; \<exists> D \<in> \<D>. P D\<rbrakk> \<Longrightarrow> sel_from_sets P \<D> \<in> \<D>"
  "\<And> \<D> P. \<lbrakk>finite \<D>; \<exists> D \<in> \<D>. P D\<rbrakk> \<Longrightarrow> P (sel_from_sets P \<D>)"
begin

interpretation find_aug_path_edg_use_intrp: find_aug_path_pedg_use create_vert
               "\<lambda>G M. compute_match_blossom'.compute_match_blossom sel G M (compute_alt_path G M)"
               compute_edg sel_from_sets sel E
proof(rule find_aug_path_pedg_use.intro, goal_cases)
  case 2
  then show ?case
  proof(rule find_aug_path_edg.intro, goal_cases)
    case 1
    then show ?case 
      using find_aug_path_use.axioms(1) find_aug_path_use_satisfied by blast
  next
    case 2
    then show ?case
    proof(rule find_aug_path_edg_axioms.intro, goal_cases)
      case (1 G M)
       then interpret compute_match_blossom' sel G M "compute_alt_path G M"
        using compute_alt_path_spec compute_alt_path_complete
        apply unfold_locales
        by (auto simp: compute_alt_path_spec_def)
      from 1 show ?case
        by(auto intro!:  compute_edg compute_edg blossom_None_alt_path_None)
    qed (auto simp add: sel_from_sets)
  qed
qed (simp add: find_aug_path_use_satisfied)

abbreviation "find_decomposition \<equiv>
  find_aug_path_edg_use_intrp.find_edg"

lemmas find_decomposition_correct =
 find_aug_path_edg_use_intrp.find_decomposition_correct_with_matching
end

locale compute_alt_path_and_edg_use = 
compute_alt_path_use +
fixes sel_from_sets::"('a set \<Rightarrow> bool) \<Rightarrow> 'a set set \<Rightarrow> 'a set"
assumes sel_from_sets:
  "\<And> \<D> P. \<lbrakk>finite \<D>; \<exists> D \<in> \<D>. P D\<rbrakk> \<Longrightarrow> sel_from_sets P \<D> \<in> \<D>"
  "\<And> \<D> P. \<lbrakk>finite \<D>; \<exists> D \<in> \<D>. P D\<rbrakk> \<Longrightarrow> P (sel_from_sets P \<D>)"
begin

definition "compute_edg G M = 
  compute_alt_path.compute_edg id 
     get_path extend_forest_even_unclassified
     empty_forest abstract_forest evens G M sel (Vs G - Vs M)"

context 
  fixes G M::"'a set set"
  assumes "graph_invar G" "matching M" "M \<subseteq> G"
begin

interpretation path_compute: compute_alt_path
  where vset_invar = "\<lambda> V. finite V"
    and vset_to_set = id
    and odds = odds
    and get_path = get_path
    and forest_invar = forest_invar
    and roots = roots
    and vset_empty = "{}"
    and extend_forest_even_unclassified = extend_forest_even_unclassified
    and empty_forest = empty_forest
    and abstract_forest = abstract_forest
    and evens = evens
    and G = G
    and M = M
    and sel = sel
    and unmatcheds = "Vs G - Vs M"
     using forest_satisfied[OF \<open>graph_invar G\<close>  \<open>matching M\<close> \<open>M \<subseteq> G\<close>]
   by(auto intro!: compute_alt_path.intro choose_axioms compute_alt_path_axioms.intro
         simp add: graph_abs.intro match_axioms.intro match_def g.graph_abs_axioms 
                   \<open>M \<subseteq> G\<close> \<open>matching M\<close> match_axioms_def  \<open>graph_invar G\<close> graph_abs_def)

lemmas compute_alt_path_props = 
  path_compute.compute_alt_path_from_tree_sound'
  path_compute.compute_alt_path_from_tree_complete
  path_compute.compute_edg_correct

end


interpretation usage:
 compute_match_blossom'_edg_use sel create_vert compute_paths E compute_edg sel_from_sets
proof(unfold_locales,goal_cases)  
  case (2 G M)
  thus  ?case
    using compute_alt_path_props(2)[OF 2(1,2,3)]
    by(auto simp add: compute_paths_def)
next
  case (1 G M)
  thus  ?case
    using compute_alt_path_props(1)[OF 1(1,2,3)]
    by(auto simp add: compute_paths_def)
next
  case (3 G M)
  thus ?case
    unfolding compute_edg_def compute_paths_def 
    by(intro compute_alt_path_props(3)[of G M]) auto
qed (auto simp add: sel_from_sets)

abbreviation "find_decomposition \<equiv> usage.find_decomposition"

lemmas find_decomposition_correct =
 usage.find_decomposition_correct
 
end

end