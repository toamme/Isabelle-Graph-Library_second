theory Perfect_Quotient
  imports Graph_Quotient_working_2 Tutte_Theorem.Tutte_Theorem
          Directed_Set_Graphs.More_Lists
(*Blossom_Algo_working*)
begin
(*TODO MOVE*)
lemma path_mono:
"\<lbrakk>path E p; length p \<ge> 2; set (edges_of_path p) \<subseteq> E'\<rbrakk> \<Longrightarrow> path E' p"
proof(induction  rule: path.induct)
  case (path2 v v' vs)
  then show ?case 
    by(cases vs) auto
qed auto

lemma walk_betw_swap_carrier:
"\<lbrakk>walk_betw E' x p y; set (edges_of_path p ) \<subseteq> E; x \<in> Vs E\<rbrakk> \<Longrightarrow> walk_betw E x p y"
  by(cases p rule: list_cases3)
    (force intro!: walk_reflexive_cong 
            intro: walk_betw_strengthen
             dest: walk_betw_split_off_first walk_betw_split_off_last walk_nonempty)+

definition "tutte_violator G X = (X \<subseteq> Vs G \<and> card (odd_comps_in_diff G X) > card X)"

lemma tutte_violator_no_tutte:
  "tutte_violator G X \<Longrightarrow> \<not> tutte_condition G"
  by(auto simp add: tutte_condition_def tutte_violator_def)

lemma tutte_no_tutte_violator:
  "tutte_condition G \<Longrightarrow> \<nexists> X. tutte_violator G X"
  by(auto simp add: tutte_condition_def tutte_violator_def)

lemma tutte_violator_no_perfect_matching:
 "tutte_violator G X \<Longrightarrow> \<nexists> M. perfect_matching G M"
  using tutte1 tutte_no_tutte_violator by auto

lemma perfect_matching_no_tutte_violator:
 "perfect_matching G M \<Longrightarrow> \<nexists> X. tutte_violator G X"
  using tutte1 tutte_no_tutte_violator by blast
  
(*TODO MOVE*)
lemma two_in_path_means_path:
  assumes  "walk_betw E bse1 C bse2" "x \<in> set C" "y \<in> set C"
  shows "\<exists> p. walk_betw E x p y"
proof(cases "x = y")
  case True
  then show ?thesis 
     using assms(3)  walk_in_Vs[OF assms(1)]
    by(auto intro!: exI[of _ "[y]"] walk_reflexive)
next
  case False
  obtain C1 C2 where "C = C1@[x]@C2"
    using split_list_first[OF assms(2)] 
    by auto
  moreover hence "y \<in> set C1 \<or> y \<in> set C2"
    using False assms(3) by auto
  ultimately obtain C1 C2 C3 where "C = C1@[x]@C2@[y]@C3 \<or> C = C1@[y]@C2@[x]@C3" 
    using split_list_first[of y C1] split_list_first[of y C2] 
    by force
  hence "walk_betw E x ([x]@C2@[y]@C3) bse2 \<or> walk_betw E y ([y]@C2@[x]@C3) bse2"
    using assms(1)  walk_suff by force
  hence "walk_betw E x ([x]@C2@[y]) y \<or> walk_betw E y ([y]@C2@[x]) x"
    using  walk_pref[of E x "x#C2" y C3]  walk_pref[of E y "y#C2" x C3]
    by auto
  thus ?thesis
    by (auto intro: walk_symmetric)
qed

lemma walk_touching_comp_in_comp:
"\<lbrakk>walk_betw E x p y; set p \<inter> connected_component E z \<noteq> {}\<rbrakk>
 \<Longrightarrow> set p \<subseteq> connected_component E z"
proof(goal_cases)
  case 1
  then obtain v where v: "v \<in> connected_component E z" "v \<in> set p" by auto
  show ?case
  using  1(1) v in_own_connected_component[of ]
        unequal_components_disjoint[of E v x]
        unequal_components_disjoint[of E v z]
       vertices_path_in_component[of E x p y] 
  by(intro path_in_connected_component)
    (fastforce simp add: disjoint_iff walk_betw_def)+
qed

context quot
begin

lemma edge_in_quotG:
 "\<lbrakk>{v, v'} \<in> E'; E' \<subseteq> E\<rbrakk> \<Longrightarrow> {P v, P v'} \<in> (quotG E') \<or> (P v = P v' \<and> P v = u)" 
  using image_edge_sing_u 
  by(fastforce simp add:  quot_graph_def)

lemma walk_in_graph_walk_in_quotient:
  assumes "walk_betw E' x p y \<or> x = y" "E' \<subseteq> E"
    shows "\<exists> q. walk_betw (quotG E') (P x) q (P y) \<or> P x = P y"    
  proof(cases "x = y")
    case False
    hence "walk_betw E' x p y" 
      using assms by simp
    then show ?thesis 
    proof(induction rule: induct_walk_betw)
      case (path1 v)
      then show ?case by simp
    next
      case (path2 v v' vs b)
      then obtain q where 
          "walk_betw (quot_graph P E' - {{u}}) (P v') q (P b) \<or> P v' = P b" by auto
      moreover have "{P v, P v'} \<in> quot_graph P E' - {{u}} \<or> P v = P v' \<and> P v = u"
        using edge_in_quotG[OF path2(1) assms(2)]  by simp
      moreover hence "walk_betw (quot_graph P E' - {{u}}) (P v) [P v, P v'] (P v') 
                      \<or> P v = P v'" 
        by (auto intro!: edges_are_walks_cong equalityD1)
       moreover have "walk_betw (quot_graph P E' - {{u}}) u [u, u] u \<Longrightarrow> False"
         by (simp add: walk_betw_def)
       ultimately show ?case 
         by (force intro: walk_betw_Cons_first)
     qed
   qed simp
(*TODO MOVE*)
lemma quotG_mono:
  "A \<subseteq> B \<Longrightarrow> quotG A \<subseteq> quotG B"
  by(auto simp add: quot_graph_def)

lemma path_is_quot_path_strong:
  assumes path: "path (quotG E') p" "set p \<subseteq> s" "E' \<subseteq> E"
  shows "path E' p"
proof-
  have "path (quotG E) p"
    using path(1,3) path_subset quotG_mono by blast
  hence "path E p"
    using path(2) qug_path_iff_case_1_ii by presburger
  moreover have "\<And> x. p = [x] \<Longrightarrow> x \<in> Vs E'"
    using path(1,2,3) vert_in_graph_iff_in_quot_diff_u by auto
  moreover have "set (edges_of_path p) \<subseteq> E'"
    using edge_of_path_in_graph_iff_in_quot[of p _ E'] path(1,2,3) path_edges_subset
    by fastforce
  ultimately show ?thesis
  proof(cases p rule: list_cases3, goal_cases)
    case (3 x y xs)
    then show ?thesis 
      using path_mono[of E "x#y#xs" E'] by simp
  qed simp+
qed
 

lemma walk_in_quotient_walk_in_graph:
  assumes  "walk_betw E' bs1 C bs2"  "s = Vs E - set C"
           "walk_betw (quotG E') (P x) q (P y) \<or> P x = P y"
           "x \<in> Vs E" "y \<in> Vs E" "E' \<subseteq> E"
    shows  "\<exists> p. walk_betw E' x p y \<or> x = y"   
proof(cases "x = y")
  case False
  note false = this
  show ?thesis
  proof(cases " P x = P y")
    case True
    hence "x \<in> set C"  "y \<in> set C" 
      using assms(4) false
      apply(all \<open>cases "x \<in> Vs E "\<close>)
      apply(all \<open> cases "y \<in> Vs E "\<close>)
      apply(all \<open> cases "x \<notin> set C"\<close>)
      apply(all \<open> cases "y \<notin> set C"\<close>)
      using good_quot_map(1) assms(2,4,5,6) by auto
    then show ?thesis 
      using two_in_path_means_path[OF assms(1)] by simp
  next
    case False
    hence quotwalk:"walk_betw (quotG E') (P x) q (P y)" 
      using assms(3) by simp
    then obtain q' where q':
        "walk_betw (quotG E') (P x) q' (P y)" "distinct q'" "set q' \<subseteq> set q"
      using walk_betw_different_verts_to_ditinct[OF _ False refl] by force
    hence q'_in_quotG:"set q' \<subseteq> Vs (quotG E')"
      by (simp add: walk_in_Vs)
    show ?thesis
    proof(cases "u \<in> set q'")
      case False
      hence q'_in_s:"set q' \<subseteq> s" 
        using good_quot_map(1) q'_in_quotG  in_quotG_neq_u by blast
      hence "walk_betw E' (P x) q' (P y)"
        using  assms(6) path_is_quot_path_strong[of E' q'] q'(1)
        by(simp add: walk_betw_def)
      moreover have "P x = x" "P y = y"
        using False calculation walk_betw_split_off_first walk_betw_split_off_last
        by fastforce+
      ultimately show ?thesis by auto
    next
      case True
      then obtain q1 q2 where p1p2:"q' = q1@[u]@q2"
        using split_list_last[of u q']
        by auto
      hence u_not_inq1q2: "u \<notin> set q1" "u \<notin> set q2"
        using q'(2) by auto
      have q1_C: "q1 \<noteq> [] \<Longrightarrow> \<exists> p1 u1. walk_betw E' x p1 u1 \<and> u1 \<in> set C"
      proof(goal_cases)
        case 1
        then obtain v1 q11 where q1_split: "q1 = q11@[v1]"
          by (cases q1 rule: rev_exhaust) auto
        have  "walk_betw (quotG E') (P x) q1 v1"
          using q'(1) q1_split p1p2 
          by (simp add: walk_pref)
        moreover have "P x = x"
          using calculation u_not_inq1q2(1) walk_betw_split_off_first by fastforce
        ultimately have walk_up_to_v1:"walk_betw E' x q1 v1" 
          using mem_path_Vs neq_u_notin_quotG u_not_inq1q2(1)
                path_is_quot_path_strong[of E' q1, OF _ _ assms(6)]
                in_quotG_neq_u[of _ E'] subset_code(1)
          unfolding walk_betw_def (* remove metis*)
          by (metis (lifting) )
        have "{v1, u} \<in> (quotG E')" 
          using q'(1) q1_split p1p2 path_2 single_in_append walk_suff
          by(fastforce simp add: walk_betw_def)  
        moreover have "v1 \<noteq> u"
          using q1_split u_not_inq1q2(1) by force
       ultimately obtain u' where "{v1, u'} \<in> E'" "u' \<notin> s"
          using  assms(4)  edge_in_quotG_2'_doubleton[of v1 E']
              edges_are_Vs_2[of v1 u "quotG E'"] in_quot_graph_neq_u[of v1 E'] assms(6)
          by(auto simp add: insert_commute)
        hence u': "u' \<in> set C" "{v1, u'} \<in> E'"
          using assms(2,6) 
          by auto
        hence walk_v1_u': "walk_betw E' v1 [v1, u'] u'"
          by (simp add: edges_are_walks)
        hence "walk_betw E' x (q1@[ u']) u'"
          using  walk_up_to_v1 walk_transitive_2 by fastforce
        thus ?thesis
          using u'(1) by auto
      qed
      have q2_C: "q2 \<noteq> [] \<Longrightarrow> \<exists> p2 u2. walk_betw E' u2 p2 y \<and> u2 \<in> set C"
      proof(goal_cases)
        case 1
        then obtain v2 q21 where q2_split: "q2 = v2#q21"
          by (cases q2 rule: list.exhaust) auto
        have  "walk_betw (quotG E') v2 q2 (P y)"
          using q'(1) q2_split p1p2 path_suff[of "quotG E'" "q1@[u]" q2]
          by(simp add: walk_betw_def)
        moreover have "P y = y"
          using calculation u_not_inq1q2(2) walk_betw_split_off_last by fastforce
        ultimately have walk_up_to_v1:"walk_betw E' v2 q2 y" 
          using mem_path_Vs neq_u_notin_quotG u_not_inq1q2(2)
                path_is_quot_path_strong[of E' q2, OF _ _ assms(6)]
          unfolding  walk_betw_def (*nasty metis*)
          by (metis (lifting) in_quotG_neq_u subset_code(1))
        have "{v2, u} \<in> (quotG E')" 
          using q'(1) q2_split p1p2 path_2 single_in_append  walk_suff
          by(fastforce simp add: insert_commute walk_betw_def)
        moreover have "v2 \<noteq> u"
          using q2_split u_not_inq1q2(2) by force
       ultimately obtain u' where "{v2, u'} \<in> E'" "u' \<notin> s"
          using  assms(4)  edge_in_quotG_2'_doubleton[of v2 E'] assms(6)
              edges_are_Vs_2[of v2 u "quotG E'"] in_quot_graph_neq_u[of v2 E']  
          by(auto simp add: insert_commute)
        hence u': "u' \<in> set C" "{v2, u'} \<in> E'"
          using assms(2,6) 
          by auto
        hence walk_v1_u': "walk_betw E' u' [u', v2] v2"
          by (simp add: edges_are_walks insert_commute)
        hence "walk_betw E' u' (u'#q2) y"
          using q2_split walk_betw_cons walk_up_to_v1 by fastforce
        thus ?thesis
          using u'(1) by auto
      qed
      have q1_q2_cases: "q2 = [] \<Longrightarrow> q1 = [] \<Longrightarrow> False" 
        using False p1p2 q'(1)
        by(simp add: walk_betw_def )
      show ?thesis
      proof(cases q1)
        case Nil
        hence "P x = u"
          using p1p2 q'(1) walk_betw_split_off_first by fastforce
        hence x_in_C:"x \<in> set C"
          using assms(2,4,6) good_quot_map(1) by fastforce
        moreover obtain u2 p2 where "walk_betw E' u2 p2 y" "u2 \<in> set C"
           using q2_C q'(1) Nil  q1_q2_cases by(auto simp add: p1p2)
         moreover then obtain p' where "walk_betw E' x p' u2"
           using assms(1) two_in_path_means_path x_in_C by fast
        then show ?thesis
          by (auto intro: calculation(2) walk_transitive_2)
      next
        case (Cons a list)
        note cons = this
        show ?thesis 
        proof(cases q2)
          case Nil
        hence "P y = u"
          using p1p2 q'(1) walk_betw_split_off_last by fastforce
        hence y_in_C:"y \<in> set C"
          using assms(2,5) good_quot_map(1) by fastforce
        moreover obtain u1 p1 where "walk_betw E' x p1 u1" "u1 \<in> set C"
           using q1_C q'(1) Nil q1_q2_cases by(auto simp add: p1p2)
         moreover then obtain p' where "walk_betw E' u1 p' y"
           using assms(1) two_in_path_means_path y_in_C by fast
        then show ?thesis 
          by (auto intro!: calculation(2) walk_transitive_2)
        next
          case (Cons a list)
          obtain u1 p1 where x_u1: "walk_betw E' x p1 u1" "u1 \<in> set C"
           using q1_C q'(1) cons  by(auto simp add: p1p2)
         moreover obtain u2 p2 where u2_y: "walk_betw E' u2 p2 y" "u2 \<in> set C"
           using q2_C q'(1) Cons by(auto simp add: p1p2)
         moreover obtain pm where "walk_betw E' u1 pm u2" 
           using assms(1) two_in_path_means_path[OF _  x_u1(2) u2_y(2)] by force
         ultimately have " \<exists> p. walk_betw E' x p y" 
           using walk_transitive_2 by meson
         thus ?thesis by simp
       qed
      qed
     qed
   qed
 qed simp

lemma component_in_path_quotient:
  assumes  "walk_betw E' bs1 C bs2"  "s = Vs E - set C"
           "x \<in> Vs E" "E' \<subseteq> E"
     shows "connected_component (quotG E') (P x) = P ` (connected_component E' x)"
proof(rule,  all \<open>rule\<close>, goal_cases)
  case (1 yy)
  then obtain p where  p: "walk_betw (quotG E') (P x) p yy \<or> P x = yy "
    by(auto simp add: connected_component_def Undirected_Set_Graphs.reachable_def)
  hence "yy \<in> Vs (quotG E') \<or> P x = yy" 
    by force
  then obtain y where y: "y \<in> Vs E" "P y = yy"
    using Vs_quotG_subset_Vs_quot_graph[of E'] assms(2)
        in_quot_graph_neq_u[of yy E'] sel' assms(3) by force+
  obtain p where "walk_betw E' x p y \<or> x = y"
    using walk_in_quotient_walk_in_graph[OF assms(1,2) _ assms(3) y(1) assms(4)] p y(2) by auto
  then show ?case 
    using has_path_in_connected_component[of E' x p y]
          in_own_connected_component[of x E'] y(2) 
    by auto
next
  case (2 yy)
  then obtain y where y: "y \<in> connected_component E' x" "P y = yy" by auto
  then obtain p where p: "walk_betw E' x p y \<or> x = y" 
    using in_con_comp_has_walk[of y E' x] by auto
  then obtain q where "walk_betw (quotG E') (P x) q (P y) \<or> P x = P y"
    using walk_in_graph_walk_in_quotient[OF p assms(4)] by auto
  thus ?case 
    using has_path_in_connected_component2[of "quotG E'" "P x" "P y"] 
          in_connected_componentI2[of "P x" "P y" "quotG E'"] y(2) 
    by fast
qed

lemma components_of_path_quotient:
  assumes  "walk_betw E' bs1 p bs2"  "s = Vs E - set p" "E' \<subseteq> E"
  shows "comps (P ` Vs E') (quotG E') = (image P) ` (connected_components E')"
proof(rule, all \<open>rule\<close>, goal_cases)
  case (1 C)
  then obtain xx where xx: "C = connected_component (quot_graph P E' - {{u}}) xx" 
                       "xx \<in> (P ` Vs E')" 
    by(auto simp add: comps_def)
  then obtain x where x': "x \<in> Vs E'" "xx = P x" by blast
  hence x: "x \<in> Vs E" "xx = P x" 
    using Vs_subset assms(3) by auto
  show ?case 
    using component_in_path_quotient[OF assms(1,2) x(1) assms(3)] x(2) xx(1) 
    by (simp add: connected_component_in_components x(1) x')
next
  case (2 C)
  then obtain C' where C':"C' \<in> connected_components E'" "C = P ` C'" by blast
  then obtain x where x: "x \<in>Vs E'" "C' = connected_component E' x" 
    using connected_comp_has_vert by blast
  have x': "x \<in> Vs E" 
    using Vs_subset assms(3) x(1) by auto
  show ?case 
    using component_in_path_quotient[OF assms(1,2) x' assms(3)] x(1)
    by(force simp add: x(2) comps_def C'(2))
qed

lemma component_in_quotient_is_if:
  assumes  "walk_betw E' bs1 p bs2"  "s = Vs E - set p" "x \<in> Vs E" "E' \<subseteq> E"
  shows "connected_component (quotG E') (P x) = 
   (if set p \<inter> connected_component E' x \<noteq> {} 
    then insert u ((connected_component E' x) - set p)
    else (connected_component E' x))"
  unfolding component_in_path_quotient[OF assms]
proof(cases "set p \<inter> connected_component E' x \<noteq> {}", goal_cases)
  case 1
  have helper:"\<lbrakk>xa \<notin> (\<lambda>x. u) ` (connected_component E' x \<inter> { v | v. v \<notin> s});
          xa \<in> connected_component E' x; xa \<notin> set p\<rbrakk> \<Longrightarrow> xa \<in> s" for xa 
    using  Vs_subset[OF assms(4)] assms(2,3)
    by(auto dest!:  in_connected_component_in_edges[of xa E' x])
  have helper2: "u \<in> connected_component E' x" "u \<in> s"
    if "u \<notin> (\<lambda>x. u) ` (connected_component E' x \<inter> { v | v. v \<notin> s})"
    using that 1 assms(2) by force+
  have helper3: 
    "\<lbrakk>xa \<noteq> u; xa \<in> set p; xa \<in> connected_component E' x; xa \<in> s\<rbrakk> \<Longrightarrow> False" for xa
     using assms(2) by fastforce
  show ?case 
    by(auto intro: helper helper2 helper3)
next
  case 2
  have helper1: "\<lbrakk>xa \<in> connected_component E' x; xa \<notin> s\<rbrakk>
               \<Longrightarrow> u \<in> connected_component E' x" for xa
    using "2" Vs_subset[OF assms(4)] assms(2,3) 
        in_connected_component_in_edges[of xa E' x]
    by fast
  have helper2: "\<lbrakk>xa \<in> connected_component E' x;
          xa \<notin> (\<lambda>x. u) ` (connected_component E' x \<inter> { v| v. v \<notin> s})\<rbrakk> \<Longrightarrow> xa \<in> s" for xa
    using "2"  Vs_subset[OF assms(4)] assms(2,3)
        in_connected_component_in_edges[of xa E' x]
    by auto
  show ?case
    using 2
    by (auto intro:  helper1 helper2)
qed

lemma P_of_component_is_if:
  assumes  "walk_betw E' bs1 p bs2"  "s = Vs E - set p" "x \<in> Vs E" "E' \<subseteq> E"
  shows "P ` (connected_component E' x) = 
   (if set p \<inter> connected_component E' x \<noteq> {} 
    then insert u ((connected_component E' x) - set p)
    else (connected_component E' x))"
  using assms(1,2,3,4) component_in_path_quotient component_in_quotient_is_if
  by auto

lemma removed_unchanged_graph_diff_quot_swap:
  assumes  "X \<subseteq> s"
  shows  "graph_diff (quotG E') (P ` X) = quotG (graph_diff E' X)"
proof(rule, goal_cases)
  case 1
  have helper: "xa = u" "u \<notin> (\<lambda>x. u) ` (e \<inter> {v | v. v \<notin> s}) \<Longrightarrow> u \<in> e"if
        "e \<in> E'"
       "(e \<inter> s \<union> (\<lambda>x. u) ` (e \<inter> {v | v. v \<notin> s})) \<inter>
       (X \<inter> s \<union> (\<lambda>x. u) ` (X \<inter> {v | v. v \<notin> s})) = {}"
       "\<And> ea. \<lbrakk>ea \<inter> X = {}; ea \<in> E'\<rbrakk> \<Longrightarrow>
            e \<inter> s \<union> (\<lambda>x. u) ` (e \<inter> {v | v. v \<notin> s}) \<noteq>
            ea \<inter> s \<union> (\<lambda>x. u) ` (ea \<inter> {v | v. v \<notin> s})" for e xa
    using that(1,2) that(3)[of e]
    by auto
  show ?case 
    by(auto simp add: graph_diff_def quot_graph_def intro: helper | rule helper)+
next
  case 2
  then show ?case 
  using good_quot_map(1) assms
  by(auto simp add: graph_diff_def quot_graph_def)
qed

(*TODO MOVE*)
lemma almost_distinct_even_length_list_odd_card:
      "\<lbrakk>even (length xs); xs \<noteq> []; distinct (tl xs); hd xs = last xs\<rbrakk> \<Longrightarrow>
       odd (card (set xs))"
proof(cases xs rule: list_cases3, goal_cases)
  case (3 x y ys)
  hence set_xs:"set xs = set (y#ys)" by auto
  show ?thesis 
    using 3(1,3,5)
    by (subst set_xs, subst distinct_card) auto
qed simp+

lemma tutte_violator_in_quot_is_tutte_violator:
  assumes "walk_betw E bs Cycl bs" "even (length Cycl)" "distinct (tl Cycl)"  
          "s = Vs E - set Cycl" "X \<subseteq> s" "tutte_violator (quotG E) X" 
  shows   "tutte_violator E X"
proof-
  have X_props: "X \<subseteq> Vs (quotG E)"
    "card X < card (odd_comps_in_diff (quotG E) X)"
    using assms(6) by(auto simp add: tutte_violator_def)
  have X_in_Vs: "X \<subseteq> insert u (Vs E)" 
    using X_props(1) assms(4) neq_u_notin_quotG
    by blast
  have "set (edges_of_path Cycl) \<subseteq> E" 
    by (auto intro!: assms(1) path_edges_subset walk_between_nonempty_pathD(1))
  hence C_edges_in_diff:"set (edges_of_path Cycl) \<subseteq> graph_diff E X"
    using assms(4,5) v_in_edge_in_path_gen'[of _ Cycl]
    by(auto simp add: graph_diff_def)
  have bs_Vs:"bs \<in> Vs (graph_diff E X)"
  proof-
    obtain e where e:"e \<in> set (edges_of_path Cycl)" "bs \<in> e"
      using assms(1,2) unfolding walk_betw_def
      by(cases Cycl rule: list_cases3) auto         
    hence "e \<in> graph_diff E X"
      using e(1)
      using \<open>set (edges_of_path Cycl) \<subseteq> graph_diff E X\<close> by blast
    thus ?thesis 
      using e(2) by blast
  qed
  have C_in_diff: "walk_betw (graph_diff E X) bs Cycl bs"
    using assms(1)
  proof(cases Cycl rule: list_cases3, goal_cases)
    case (2 x)
    then show ?thesis 
      using bs_Vs path1
      by(auto simp add: walk_betw_def)
  next
    case (3 x y xs)
    then show ?thesis 
      using C_edges_in_diff 
      by(intro walk_betw_strengthen[OF assms(1)]) auto
  qed (auto simp add: walk_betw_def)
  have odd_verts_cycl: "odd ( card (set Cycl))" 
    using assms(1,2,3)
    by(intro almost_distinct_even_length_list_odd_card)
      (auto simp add: walk_betw_def)
  have P_X_is_X:"P ` X = X"
    using assms(5) by auto
  define f where "f = (\<lambda> C. P ` C)"
  have card_comparison: "card (odd_comps_in_diff E X) \<ge> card (odd_comps_in_diff (quotG E) X)"
  proof(rule surj_card_le[of _ _ f], goal_cases)
    case 1
    then show ?case 
      by (simp add: diff_components_finite graph)
  next
    case 2
    show ?case 
    proof(rule, goal_cases)
      case (1 C')
      then obtain x' where x': "x' \<in> (Vs (quotG E)) - X"
        "C' = connected_component (graph_diff (quotG E) X) x'"
        "odd (card C')" 
        using odd_comps_in_diff_are_componentsOb[OF 1(1)] by auto
      have "x' \<in> s\<or> x' = u"
        using neq_u_notin_quotG[of x'] x'(1)
        by auto
      then obtain x where x: "x' = P x " "x \<notin> X" "x \<in> Vs E"
        using  x'(1) assms(4) in_mono[OF assms(5), of "sel (Vs E - s)"] sel' 
        by force+
      define C where "C = connected_component (graph_diff E X) x"
      have comp_x_finite:"finite (connected_component (graph_diff E X) x)"
        by (simp add: component_is_finite dblton_E finite_Vs graph_invar_diff)
      have u_not_in_x_comp_without_cycle: 
        "u \<notin> connected_component (graph_diff E X) x -  set Cycl"
        using assms(4) diff_connected_component_subset good_quot_map(1) x(3) by fastforce
      have "odd (card C)"
        unfolding 1(1) f_def C_def
      proof(cases "set Cycl \<inter> connected_component (graph_diff E X) x \<noteq> {}", goal_cases)
        case 1
        have cycl_in_x_comp: "set Cycl \<subseteq> connected_component (graph_diff E X) x" 
          using 1 by(rule walk_touching_comp_in_comp[OF C_in_diff])
        have "card ({u} \<union> (connected_component (graph_diff E X) x - set Cycl)) = 
               1 + card (connected_component (graph_diff E X) x - set Cycl)"
          using comp_x_finite  u_not_in_x_comp_without_cycle 
          by (subst card_Un_disjoint) auto
        moreover have "card (connected_component (graph_diff E X) x - set Cycl) = 
                        card (connected_component (graph_diff E X) x)  - card (set Cycl)"
          by(auto simp add: card_Diff_subset[OF _ cycl_in_x_comp])
        ultimately show ?case
          using odd_verts_cycl x'(3) comp_x_finite cycl_in_x_comp
          unfolding C_def x'(2) x(1)
          unfolding removed_unchanged_graph_diff_quot_swap[OF assms(5),
              simplified P_X_is_X]
          unfolding component_in_quotient_is_if[OF C_in_diff assms(4) x(3) graph_diff_subset] if_P[OF 1]
          by auto
      next
        case 2
        then show ?case
          using  x'(3)
          unfolding C_def x'(2) x(1)
          unfolding removed_unchanged_graph_diff_quot_swap[OF assms(5),
              simplified P_X_is_X]
          unfolding component_in_quotient_is_if[OF C_in_diff assms(4) x(3) graph_diff_subset] if_P[OF 1]
          by auto
      qed
      hence "C \<in> odd_comps_in_diff E X"
        using  x(2,3) connected_components_notE_singletons
        by(fastforce simp add: odd_comps_in_diff_def odd_components_def 
            odd_component_def C_def singl_in_diff_def intro!: bexI[of _ x])
      moreover have "P ` C = C'"
        unfolding C_def x'(2) x(1)
        unfolding removed_unchanged_graph_diff_quot_swap[OF assms(5),
            simplified P_X_is_X]
        unfolding component_in_path_quotient[OF C_in_diff assms(4) x(3) graph_diff_subset] if_P[OF 1]
        by auto
      ultimately show ?case
        by(auto simp add: f_def)
    qed
  qed
  hence "card (odd_comps_in_diff E X) > card X"
    using X_props(2) by simp
  thus ?thesis
    using assms(4,5)
    by(auto simp add: tutte_violator_def)
qed

lemma tutte_violator_in_quot_no_perfect_matching:
  assumes "walk_betw E bs Cycl bs" "even (length Cycl)" "distinct (tl Cycl)"  
          "s = Vs E - set Cycl" "X \<subseteq> s" "tutte_violator (quotG E) X" 
  shows   "\<nexists> M. perfect_matching E M"
  using tutte_violator_in_quot_is_tutte_violator[OF assms] 
        tutte_violator_no_perfect_matching 
  by auto

end
(*TODO MOVE*)
lemma matchingI:
  "(\<And>e1 e2. \<lbrakk>e1 \<in> M; e2 \<in> M; e1 \<noteq> e2\<rbrakk> \<Longrightarrow> e1 \<inter> e2 = {}) \<Longrightarrow> matching M"
and matchingD:
  "\<lbrakk>matching M ; e1 \<in> M; e2 \<in> M; e1 \<noteq> e2\<rbrakk> \<Longrightarrow> e1 \<inter> e2 = {}"
  by (auto simp: matching_def)

lemma graph_matchingE:
"graph_matching G M \<Longrightarrow> ( \<lbrakk>matching M; M \<subseteq> G\<rbrakk> \<Longrightarrow> P ) \<Longrightarrow> P"
and graph_matchingI:
"\<lbrakk>matching M; M \<subseteq> G\<rbrakk> \<Longrightarrow> graph_matching G M"
and graph_matchingD:
"graph_matching G M \<Longrightarrow> matching M"
"graph_matching G M \<Longrightarrow> M \<subseteq> G"
  by auto

lemma matching_union:
     assumes "matching M"  "matching M'"
              "M \<inter> M' = {}" "Vs M \<inter> Vs M' = {}"
        shows "matching (M \<union> M')"
  apply(rule matchingE[OF  assms(1)])
  apply(rule matchingE[OF assms(2)])
  apply(rule matchingI)
  using assms(3,4) 
  by blast

lemma graph_matching_union:
     assumes "graph_matching G M"  "graph_matching G M'"
             "M \<inter> M' = {}" "Vs M \<inter> Vs M' = {}"
       shows "graph_matching G (M \<union> M')"
  using matching_union assms by auto

lemma graph_matching_smaller_graph:
  "graph_matching G M \<Longrightarrow> M \<inter> Del = {} \<Longrightarrow> graph_matching (G - Del) M" 
  by blast

lemma graph_matching_bigger_graph:
  "graph_matching G M \<Longrightarrow> G \<subseteq> G'\<Longrightarrow> graph_matching G' M" 
  by auto

lemma graph_matching_edge_change:
  "graph_matching G M \<Longrightarrow> M \<inter> Del = {} \<Longrightarrow> graph_matching ((G - Del) \<union> Ins) M"
  by auto

definition "even_alt_path G M s p t =
         ((path G p \<or> length p = 1) \<and> alt_path M p \<and> 
          hd p = s \<and> last p = t \<and>
          odd (length p) \<and> s \<notin> Vs M \<and> distinct p)"

lemma even_alt_pathE:
"even_alt_path G M s p t  \<Longrightarrow>
  (\<lbrakk>path G p \<or> length p = 1; alt_path M p; p \<noteq> []; hd p = s; last p = t;
    odd (length p); s \<notin> Vs M; distinct p \<rbrakk> \<Longrightarrow> P ) 
\<Longrightarrow> P"
and even_alt_pathI:
"(\<lbrakk>path G p \<or> length p = 1; alt_path M p;  hd p = s; last p = t;
    odd (length p); s \<notin> Vs M; distinct p \<rbrakk> \<Longrightarrow> even_alt_path G M s p t) "
  by(cases p)(auto simp add: even_alt_path_def)

lemma matching_augmenting_pathE:
"matching_augmenting_path M p \<Longrightarrow>
 ( \<lbrakk>length p \<ge> 2; alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p);
     hd p \<notin> Vs M; last p \<notin> Vs M \<rbrakk> \<Longrightarrow> P )
\<Longrightarrow> P"
and matching_augmenting_pathI:
" \<lbrakk>length p \<ge> 2; alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p);
     hd p \<notin> Vs M; last p \<notin> Vs M \<rbrakk> \<Longrightarrow> matching_augmenting_path M p"
  by(auto simp add: matching_augmenting_path_def)

lemma alt_list_single:
"P x \<Longrightarrow> alt_list P Q [x]" 
  by(auto intro: alt_list.intros)

context quot
begin

lemma max_card_matchingE:
  assumes "max_card_matching G M"
  assumes "\<lbrakk> M \<subseteq> G; matching M; (\<And>M'. \<lbrakk>M' \<subseteq> G; matching M'\<rbrakk> \<Longrightarrow> card M' \<le> card M)\<rbrakk> \<Longrightarrow> Q"
  shows Q
  using assms
  unfolding max_card_matching_def
  by blast

lemma not_in_Vs_no_edge: "(x \<notin> Vs G) = (\<nexists>e. e \<in> G \<and> x \<in> e)"
  by(auto simp add: Vs_def)

lemma not_in_VsE: 
"x \<notin> Vs G \<Longrightarrow> ( (\<And> e. \<lbrakk>e \<in> G; x \<in> e\<rbrakk> \<Longrightarrow> False) \<Longrightarrow> P) \<Longrightarrow> P" for P
  by(auto simp add: Vs_def)

lemma quot_graph_cong:
  "(\<And> e. e \<in> G \<Longrightarrow> P `e = P' ` e) \<Longrightarrow> quot_graph P G = quot_graph P' G" for P
  by(auto simp add: quot_graph_def)

lemma list_cases2_both_sides:
"length xs \<ge> 2 \<Longrightarrow> (\<And> x y zs. xs = x#zs@[y] \<Longrightarrow> P) \<Longrightarrow> P" for P
  apply(cases xs)
   apply simp
  subgoal for a list
    apply(cases list rule: rev_cases)
    by auto
  done

lemma list_split_off_last_two:
  assumes "length xs \<ge> 2"
  obtains ys x y where "xs = ys@[x,y]"
  by (metis One_nat_def Suc_1 Suc_le_eq add.right_neutral add_Suc_right assms
      list.size(3,4) not_less_eq_eq rev_cases3 zero_less_Suc)

lemma alt_list_split_last_off:
"alt_list P Q (xs@[x]) \<Longrightarrow> alt_list P Q xs"for P Q 
  using alt_list_append_1 by auto


theorem reachbale_by_even_alt_path_contraction:
  assumes match_blossom: "blossom E M stem C" and
    alt_path:  "even_alt_path E M start p target" and 
    matching:  "max_card_matching E M" and
    quot: "s = (Vs E) - set C" "u \<notin>  Vs E"  "u' \<notin> Vs E" "u' \<noteq> u" 
          "target' = (if target \<notin> Vs E then target else 
              if target \<notin> s then u else target)" "target \<noteq> u"
 shows "\<exists>p' start'. even_alt_path (quotG E) (quotG M) start' p' target'"
proof-
  have p_props:
   "path E p \<or> length p = 1" "alt_path M p"
   "hd p = start" "last p = target" "odd (length p)" "start \<notin> Vs M" "distinct p"
   "p\<noteq>[]"
    using alt_path by(auto elim!: even_alt_pathE)
  show ?thesis
  proof(cases "target \<in> Vs E")
    case False
    hence "length p = 1" 
      using mem_path_Vs p_props(1,4,8) by fastforce
    moreover have "target' = target" 
      using quot(5) False by auto

    ultimately show ?thesis 
      using alt_path alt_path False in_quotG_neq_u[of target] quot(1,6)
      by(cases p)
        (auto intro!: exI[of _ p] exI[of _ target] 
             even_alt_pathI alt_list.intros(1) elim: even_alt_pathE) 
  next
    case True
  have p_props:
   "path E p" "alt_path M p"
   "hd p = start" "last p = target" "odd (length p)" "start \<notin> Vs M" "distinct p"
   "p\<noteq>[]"
    using p_props True
    by(auto intro: list.exhaust[of p])
  have M_props: "M \<subseteq> E" "matching M" "\<And> M'. \<lbrakk>M' \<subseteq> E;matching M'\<rbrakk>\<Longrightarrow> card M' \<le> card M"
                "finite M"
    using matching[simplified max_card_matching_def] finite_E finite_subset apply auto
    done
  note target_in_E = True
  have target'_def: "target' = (if target \<notin> s then u else target)" 
    using quot(5) True by auto
  hence target_not_u': " target \<noteq> u'"
    using target'_def  quot(3) target_in_E by blast
  have u'_not_in_M: "u' \<notin> Vs M" 
    using M_props(1) Vs_subset quot(3) by blast
  have P_target: "P target = target'" 
    unfolding target'_def by auto
  have interpret_helpers: "dblton_graph ({{target, u'}} \<union> E)" 
             "finite (Vs ({{target, u'}} \<union> E))"
    using  graph_invar_insert[OF target_not_u' graph]
    by auto
  have quot'_axioms: "quot_axioms ({{target, u'}} \<union> E) (insert u' s) u"
    apply(intro quot_axioms.intro)
    using quot(4)
    apply (simp add: good_quot_map(1) )
    using good_quot_map(2)
    by (smt (verit, ccfv_threshold) UnCI insert_iff psubsetE psubsetI quot(3) subsetD subsetI
        vs_insert vs_union)
  interpret quot': quot sel "insert {target, u'} E" "insert u' s" u
    using quot'_axioms interpret_helpers 
    by(intro quot.intro pre_quot.intro graph_abs.intro
             interpret_helpers  choose_axioms| simp )+
  have new_blossom: "blossom ({{target, u'}} \<union> E) M stem C"
    using match_blossom path_subset[of E "stem@C" "{{target, u'}} \<union> E"] 
    by auto
  have longer_path: "path ({{target, u'}} \<union> E) (p @ [u'])" 
    using p_props(4) 
    by(auto intro!: path_append path_subset[OF p_props(1)] edges_are_Vs_2)
  have new_edge_not_in_E: "{last p, u'} \<notin> E" "{last p, u'} \<notin> M"
    using quot(3) M_props(1) by (auto simp add:  vs_member')
  have longer_match_path: "matching_augmenting_path M (p @ [u'])"
    using p_props(2,3,5,6,8) new_edge_not_in_E(2) u'_not_in_M
    by (auto intro!: matching_augmenting_pathI alt_list_append_3 alt_list_single
              simp add: Suc_le_eq edges_of_path_append_3 edges_of_path_length)
  have new_aug_path: "graph_augmenting_path ({{target, u'}} \<union> E) M (p @ [u'])"
    using longer_path mem_path_Vs'[OF p_props(1), of u'] quot(3)
    by (auto  simp add: p_props(7) longer_match_path)
  have new_untouched_are: "{u'} \<union> s = Vs ({{target, u'}} \<union> E) - set C"
      using match_blossom mem_path_Vs' path_suff quot(3) target_in_E quot(1) 
      by (auto simp add: vs_insert)
    have u_not_in_new_Vs: "u \<notin> Vs ({{target, u'}} \<union> E)"
      using  in_Vs_insertE[of u] quot(2,4) target_in_E 
      by auto
    have quot'_Es_are:"(quot'.quotG ({{target, u'}} \<union> E)) = insert ({target', u'}) (quotG E)"
    proof(rule, all \<open>rule\<close>, goal_cases)
      case (1 e)
      then obtain e' where e': "e' \<in> insert {target, u'} E" "quot'.P ` e' = e" "e' \<noteq> {u}"
        by(auto simp add: quot_graph_def)
      show ?case
      proof(cases "e' = {target, u'}")
        case True
        hence "e = {target', u'}" 
          using e'(2) target'_def target_not_u' by force
        then show ?thesis by simp
      next
        case False
        hence e'_in_E:"e' \<in> E" 
          using e'(1) by auto
        moreover have "u' \<notin> e'" 
          using calculation quot(3) by auto
        ultimately have same_P:"quot'.P ` e' = P ` e'"
          using False e'(2) by auto
        have "e \<in> quotG E"
          unfolding quot_graph_def
          apply(rule DiffI)
           apply(rule CollectI)
           apply(rule bexI[of _ e'])
          using e'_in_E e'(2,3) 1
          unfolding same_P[symmetric] by simp+
        thus ?thesis by simp
      qed
    next
      case (2 e)
      show ?case
      proof(cases "e = {target', u'}")
        case True
        hence e_not_u:"e \<noteq> {u}"
          by (simp add: quot(4))
        moreover have "quot'.P ` {target, u'} = e" 
          using True   P_target target_not_u' by auto
        ultimately show ?thesis 
          by(auto simp add: quot_graph_def)
      next
        case False
        then obtain e' where "e' \<in> E" "P ` e' = e" "e \<noteq> {u}"
          using 2 by(auto simp add: quot_graph_def)
        moreover have "quot'.P ` e' = e" 
          using calculation(1,2)  
          by (auto intro: not_in_VsE[OF quot(3)])
        ultimately have "e \<in> quot_graph quot'.P ({{target, u'}} \<union> E)"
          unfolding quot_graph_def by blast
        thus ?thesis
          using \<open>e \<noteq> {u}\<close> by blast
      qed
    qed
    have M_edges_P_same:"e \<in> M \<Longrightarrow> quot'.P ` e = P ` e" for e
      using u'_not_in_M by auto
    have quot'_M_are:"quot'.quotG M = quotG M"
      apply(rule arg_cong[of _ _ "\<lambda> x. x - {{u}}"])
      apply(rule quot_graph_cong)
      apply(rule M_edges_P_same)
      .
    have new_Vs_superset: "Vs (quot'.quotG ({{target, u'}} \<union> E)) 
          \<supseteq> insert u' (Vs (quotG E))" 
      unfolding quot'_Es_are
      by (simp add: subset_insertI vs_insert)
    have "\<exists>p'. graph_augmenting_path (quot'.quotG ({{target, u'}} \<union> E))
          (quot'.quotG M ) p'"
      using quot'.aug_path_works_in_contraction[of stem C M "p@[u']"]
           new_blossom new_aug_path new_untouched_are u_not_in_new_Vs
       M_props(1,2) finite_E insert_is_Un rev_finite_subset
          subset_insertI2 
      by (metis (no_types, lifting))
    then obtain p' where p': "graph_augmenting_path (quot'.quotG ({{target, u'}} \<union> E))
          (quot'.quotG M ) p'" by auto
    have u'_in_p':"u' \<in> set p'"
    proof(rule ccontr, goal_cases)
      case 1
      have "set (edges_of_path p') \<subseteq> quot'.quotG ({{target, u'}} \<union> E)"
        using p' path_edges_subset by blast
      hence e_o_p:"set (edges_of_path p') \<subseteq> (quot_graph P E - {{u}})"
        using 1 unfolding quot'_Es_are 
        by (simp add: edge_not_in_edges_in_path subset_insert)
      have path_old:"path (quot_graph P E - {{u}}) p'"
        apply(rule path_mono[of "quot'.quotG ({{target, u'}} \<union> E)"])
        using p'  matching_augmenting_path_def p'  e_o_p 
        by auto
      have aupath_old:"graph_augmenting_path (quotG E) (quotG M ) p'"
        using p' quot'_M_are
        by (auto simp add:  path_old p')
      have distinct_tl:"distinct (tl C)"
        using match_blossom 
        by(auto simp add: match_blossom_def odd_cycle_def intro: list_cases2_both_sides[of C])
      have big_aug_path: "graph_augmenting_path E M (refine C M p')"
        apply(rule refine)
        using match_blossom match_blossom_feats(3) match_blossom_feats' 
              distinct_tl  match_blossom path_suff  aupath_old  M_props(1,2) quot(1) 
        by auto
      then obtain M' where "M'\<subseteq>E" "matching M'" "card M < card M'"
         using Berge[OF M_props(4,2,1) dblton_E finite_Vs] by auto
      thus False
        using M_props(3)[of M'] by simp 
    qed
    have "u' = hd p' \<or> u' = last p'"
    proof(rule ccontr, goal_cases)
      case 1
      then obtain p1 p2 where "p' = p1@[u']@p2" "p1\<noteq> []" "p2 \<noteq> []"
        using  split_list_last[OF u'_in_p'] 
        by force
      hence "u' \<in> Vs (quot'.quotG M)"
        using p'  by(auto intro!: in_aug_path_in_Vs[of _ p' u'])
      hence "u' \<in> Vs M" 
        by (simp add: M_props(1) quot'.vert_in_graph_iff_in_quot_diff_u subset_insertI2)
      thus False
        by (simp add: u'_not_in_M)
    qed
    hence "\<exists> p'. graph_augmenting_path (quot'.quotG ({{target, u'}} \<union> E))
          (quot'.quotG M ) p' \<and> last p' = u'"
      using p'
      by(auto intro: exI[of _ "rev p'"] rev_path_is_path
                     matching_augmenting_path_rev simp add: last_rev)
    then obtain p' where p':" graph_augmenting_path (quot'.quotG ({{target, u'}} \<union> E))
          (quot'.quotG M ) p'" "last p' = u'" by auto
    then obtain x p'' where xp'':"p' = p''@[x, u']" 
      by (auto elim!: matching_augmenting_pathE intro: list_split_off_last_two)
    hence xu'_in_p':"{x, u'} \<in> set (edges_of_path p')"
      by (simp add: edges_of_path_snoc_2)
    have "{x, u'} \<in> quot'.quotG ({{target, u'}} \<union> E)"
      apply(rule set_mp[OF path_edges_subset, of _ p'])
      using p'(1)  xu'_in_p' by auto
    hence xu'_in_where:"{x, u'} \<in> insert ({target', u'}) (quotG E)"
      using quot'_Es_are by argo
    moreover have "u' \<notin> Vs (quotG E)" "\<nexists> e. e \<in> quotG E \<and> u' \<in> e"
      using in_quotG_neq_u quot(1,3,4) by blast+
    moreover have "x \<noteq> u'" 
      using p' xp'' by auto
    ultimately have x_is_target': "x = target'" by auto
    have butlast_p': "p' = butlast (butlast p') @[x, u']" 
      by (simp add: butlast_append xp'')
    have "even_alt_path (quotG E) (quotG M) (hd p') (butlast p') target'"
    proof(cases "target' \<in> Vs (quotG E)")
      case False
      have path_is_target'_only:"butlast p' = [target']" 
      proof(rule ccontr, goal_cases)
        case 1
        obtain p''' y where "butlast p' = p'''@[y, target']"
          apply(rule list_split_off_last_two[of "butlast p'"])
          apply(cases "butlast p'" rule: list_cases3)
          using x_is_target' xp'' 1 
          by (auto simp add: butlast_append)
        hence y_target'_in_p':"{y, target'} \<in> set (edges_of_path (p''@[target']))" 
          unfolding xp''  butlast_append 
          by (simp add: edges_of_path_snoc_2)
        have "{y, target'} \<in> quot'.quotG ({{target, u'}} \<union> E)"
            apply(rule set_mp[OF path_edges_subset, of _ p'])
            using p'(1)  y_target'_in_p' 
            by (auto simp add: edges_of_path_snoc_2 x_is_target' xp'' y_target'_in_p')
        hence yt'_in_big_quot:"{y, target'} \<in> insert ({target', u'}) (quotG E)"
          using quot'_Es_are by argo
        moreover have "y \<noteq> u'"
          using p'(1) v_in_edge_in_path x_is_target' xp'' y_target'_in_p' by fastforce
        ultimately have "{y, target'} \<noteq> {target', u'}"
          by (force simp add: doubleton_eq_iff)
        hence "{y, target'} \<in> quotG E"
          using yt'_in_big_quot by force
        thus False
          using False 
          by blast
      qed
      hence "hd p' = target'" by(cases p' rule: list_cases3) auto
      moreover hence "target' \<notin> Vs (quot_graph P M - {{u}})"
        using False  M_props(1) Vs_subset in_mono quotG_mono[of M E]
        by blast
      ultimately show ?thesis 
         by(auto intro!: even_alt_pathI alt_list.intros(1) 
                  simp add: path_is_target'_only)
    next
      case True
      have path_to_target': "path (quot_graph P E - {{u}}) (butlast p')"
      proof(cases p' rule: list_cases4, goal_cases)
        case (4 x y z xs)
        have butlast_p':"butlast p' @ [last p'] = p'"
          using 4 by simp
        hence "set (edges_of_path (butlast p')) \<subseteq> insert ({target', u'}) (quotG E)"
          using edges_of_path_append_subset_2[of "butlast p'" "[last p']"]
               edges_of_path_append_subset_2 p'(1)
               path_edges_subset [of "insert ({target', u'}) (quotG E)" p']
          unfolding quot'_Es_are 
          by simp
        moreover have "{target', u'} \<notin> set (edges_of_path (butlast p'))" 
          apply(rule edge_not_in_edges_in_path[of target' "butlast p'" u'])
          using butlast_p' distinct_append[of "butlast p'" "[last p']"] p'(1,2) 
          by simp
        ultimately have edges_in_old_quot: 
             "set (edges_of_path (butlast p')) \<subseteq> quot_graph P E - {{u}}"
          by auto
        show ?case
          apply(rule path_mono[of "quot'.quotG ({{target, u'}} \<union> E)"])
          apply(rule path_pref[of _ _ "[last p']"])
          using 4  p'(1)  edges_in_old_quot  
          by auto
      next
        case (3 x y )
        thus ?case 
          using True x_is_target' xp'' by force
      qed auto
      moreover have "alt_path (quot_graph P M - {{u}}) (butlast p')"
      proof-
        have "alt_path (quot_graph P M - {{u}}) p'"
          using p'(1)by(unfold matching_augmenting_path_def quot'_M_are) simp
        thus ?thesis
          apply(subst (asm) butlast_p')
          unfolding edges_of_path_snoc_2
          apply(rule alt_list_split_last_off[of _ _ _ "{x, u'}"]) 
          by (simp add: butlast_append xp'')
      qed
      moreover have "hd (butlast p') = hd p'" 
        unfolding xp'' by(cases p'') auto
      moreover have "last (butlast p') = target'"
        by (simp add: butlast_append x_is_target' xp'')
      moreover have "odd (length (butlast p'))"
        using aug_paths_are_even p'(1) xp'' by fastforce
      moreover have "hd p' \<notin> Vs (quot_graph P M - {{u}})"
        using matching_augmenting_path_def p'(1) quot'_M_are by auto
      moreover have "distinct (butlast p')"
        by (simp add: distinct_butlast p'(1))
      ultimately show ?thesis
        by(auto intro!: even_alt_pathI)
    qed
    thus ?thesis by auto
  qed
qed
 

end
end