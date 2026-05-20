theory Edmonds_Gallai
  imports Edmonds_Gallai_Computation Berge_Formula.Berge_Formula
begin

hide_const evens
hide_const reachable
hide_const reachable
hide_fact reachableE
hide_fact reachableE
hide_fact reachableE

lemma inj_image_dblton_graph:
  "\<lbrakk>inj f; dblton_graph G\<rbrakk> \<Longrightarrow> dblton_graph ((image f) ` G)"
  using inj_eq[of f]
  by (intro dblton_graphI)(auto elim!: dblton_graphE)

lemma inj_image_graph_invar:
  "\<lbrakk>inj f; graph_invar G\<rbrakk> \<Longrightarrow> graph_invar ((image f) ` G)"
  by (auto intro: inj_image_dblton_graph finite_UnionD  finite_Union finite_imageI 
      simp add: Vs_def)

lemma graph_matching_image:
  assumes "graph_matching G M" "inj_on f (Vs M)"
  shows   "graph_matching ((image f) ` G) ((image f) ` M)"
  using assms
  by(auto intro!: graph_matchingI simp add: matching_image)

lemma inj_on_image_subset_iff: "\<lbrakk>inj_on f (A \<union> B)\<rbrakk> \<Longrightarrow> f ` A \<subseteq> f ` B \<longleftrightarrow> A \<subseteq> B"
  by (metis image_Un inj_on_Un_image_eq_iff sup.absorb_iff2 sup.right_idem)

lemma inj_on_lifted_graph_subset:
  "\<lbrakk>inj_on f (Vs (G \<union> G'))\<rbrakk> \<Longrightarrow> (`) f ` G' \<subseteq> (`) f ` G \<longleftrightarrow> G' \<subseteq> G"
  by (simp add: Vs_def inj_on_image inj_on_image_subset_iff sup.commute)

lemma inj_on_lifted_graph_same:
  "\<lbrakk>inj_on f (Vs (G \<union> G'))\<rbrakk> \<Longrightarrow> (`) f ` G' = (`) f ` G \<longleftrightarrow> G' = G"
  by (metis Vs_def inj_on_Un_image_eq_iff inj_on_image)

lemma graph_matching_image_rev:
  assumes  "graph_matching ((image f) ` G) ((image f) ` M)"  "inj_on f (Vs (G \<union> M))"
  shows  "graph_matching G M"
proof-
  have  "inj_on f (Vs G)"  "inj_on f (Vs M)"
    using assms(2) by(auto simp add: inj_on_Un vs_union)
  thus ?thesis
    using assms
    by(auto intro!: graph_matchingI matching_image_rev[of f M] simp add: inj_on_lifted_graph_subset)
qed

lemma graph_matching_image_iff:
  assumes  "inj_on f (Vs (G \<union> M))"
  shows  "graph_matching ((image f) ` G) ((image f) ` M) \<longleftrightarrow> graph_matching G M"
  by (meson Vs_subset assms inj_on_lifted_graph_subset le_supI1 matching_image_iff subset_inj_on)

lemma inj_on_card_of_image_leq_iff:
  "inj_on f (X \<union> Y) \<Longrightarrow> card (f ` X) \<le> card (f ` Y) \<longleftrightarrow> card X \<le> card Y"
  by (simp add: card_image inj_on_Un)

lemma inj_on_card_of_image_leqI:
  "\<lbrakk>inj_on f (X \<union> Y); card X \<le> card Y\<rbrakk> \<Longrightarrow> card (f ` X) \<le> card (f ` Y)"
  by (simp add: card_image inj_on_Un)

lemma max_card_matching_image_iff:
  assumes "inj_on f (Vs (G \<union> M))"
  shows   "max_card_matching ((image f) ` G) ((image f) ` M) \<longleftrightarrow> max_card_matching G M"
proof-
  have  inj_M: "inj_on f (Vs M)" and inj_G: "inj_on f (Vs G)"
    using assms by(auto simp add: inj_on_Un vs_union)
  have inj_on_G: "G' \<subseteq> G \<Longrightarrow> inj_on ((`) f) G'" for G'
    by (metis Vs_def inj_G inj_on_image subset_inj_on)
  have in_G_matching:"C \<subseteq> G \<Longrightarrow> matching ((`) f ` C) \<longleftrightarrow> matching C" for C 
    by (metis Vs_subset inj_G inj_on_subset matching_image_iff)
  show ?thesis
  proof(rule, goal_cases)
    case 2
    then show ?case 
      using inj_M
      by(auto intro!: max_card_matchingI inj_on_card_of_image_leqI inj_on_G
          elim!: max_card_matchingE subset_imageE
          simp add: max_card_matching_subgraphD matching_image max_card_matchingDs(2)
          bij_betw_imp_inj_on in_G_matching)
  next
    case 1
    then show ?case
      using assms max_card_matchingDs(1)[OF 1] graph_matching_image_rev[of f M G]
      by(auto intro!: max_card_matchingI inj_on_card_of_image_leqI inj_on_G
          elim!: max_card_matchingE subset_imageE
          simp add: max_card_matching_subgraphD matching_image max_card_matchingDs(2)
          bij_betw_imp_inj_on inj_on_lifted_graph_same inj_on_G 
          image_mono[of _ G "(`) f"] card_image_subst[of "(`) f" _ "(`) f ` _"] 
          in_G_matching)
  qed
qed

lemma Vs_of_imaged_graph: "Vs ((`) f ` G) = f` (Vs G)"
  by(auto simp add: Vs_def)

lemma Union_of_imaged: "\<Union> ((`) f ` \<D>) = f ` \<Union> \<D>"
  by auto

lemma Neighbourhood_image:
  assumes "inj_on f (Vs G \<union> X)" "dblton_graph G"
  shows "Neighbourhood ((image f) ` G) (f ` X) = f ` Neighbourhood G X"
proof(rule, all \<open>rule, (elim imageE in_NeighbourhoodE)\<close>, goal_cases)
  case (1 x y e yy)
  then obtain u v where "e = {u, v}" "u \<noteq> v" "x = f u" "y = f v"
    by (metis (no_types, lifting) assms(2) dblton_graphE doubleton_eq_iff image_empty image_insert)
  moreover then have "yy = v"
    using 1 assms(1) edges_are_Vs_2[of u v G] 
    by (auto simp add:  doubleton_eq_iff inj_on_def)
  ultimately show ?case
    using 1 
    by (auto intro!: rev_image_eqI[of u "Neighbourhood G X" _ f] in_NeighbourhoodI[of v u G X]
        simp add: doubleton_eq_iff insert_commute)
next
  case (2 x xx yy)
  then show ?case
    using assms(1) inj_on_contraD[of f "Vs G \<union> X" _ xx] edges_are_Vs[of xx yy G]
    by (force intro!: in_NeighbourhoodI[of "f yy" "f xx" "(image f) ` G" "f ` X"]
        rev_image_eqI[of "{xx, yy}" G "{f yy, f xx}" "image f"]
        simp add: insert_commute)
qed

lemma connected_sets_of_vertices_image:
  assumes "inj_on f (Vs G \<union> X \<union> Y)" "dblton_graph G"
  shows "f ` X \<longleftrightarrow>\<^bsub>(`) f ` G\<^esub> f ` Y \<longleftrightarrow> X \<longleftrightarrow>\<^bsub>G\<^esub> Y"
proof(rule, goal_cases)
  case 1
  then obtain e x y where "{f x, f y} = f ` e" "e \<in> G" "x \<in> X" "y \<in> Y"
    by(auto simp add: connected_set_of_vertices_def)
  moreover hence "e = {x, y}" 
    using assms inj_on_eq_iff[of f "Vs G \<union> X \<union> Y" ] edges_are_Vs[of _ _ G]
    by(auto elim!: dblton_graphE simp add: doubleton_eq_iff insert_commute)
  ultimately show ?case 
    by(auto simp add: connected_set_of_vertices_def)
next
  case 2
  then obtain u v where "{u, v} \<in> G" "u \<in> X" "v \<in> Y"
    by(auto simp add: connected_set_of_vertices_def)
  then show ?case 
    using not_in_imageD
    by(fastforce intro!: exI[of _ "f u", OF exI[of _ "f v"]] 
        simp add: connected_set_of_vertices_def)
qed

lemma graph_inter_Vs_image:
  assumes "inj_on f (Vs G \<union> X)"
  shows "((`) f ` G) \<lbrakk>f ` X\<rbrakk> = (image f) ` (G \<lbrakk>X\<rbrakk>)"
proof(rule, all \<open>rule\<close>, goal_cases)
  case (1 e)
  then obtain ee where "f ` ee \<subseteq> f ` X" "ee \<in> G" "e = f ` ee"
    by(auto simp add: graph_inter_Vs_def)
  moreover hence "ee \<subseteq> X" 
    using assms(1) not_in_VsE[of _ G] inj_on_subset[of f "Vs G \<union> X" "ee \<union> X"] 
      inj_on_image_subset_iff[of f ee X]
    by auto
  ultimately show ?case 
    by(auto intro!: in_graph_inter_VsI rev_image_eqI[of ee "G\<lbrakk>X\<rbrakk>" "f ` ee" "image f"])
qed (auto simp add: graph_inter_Vs_def)

lemma edges_of_path_image:
  "edges_of_path (map f p) = map (image f) (edges_of_path p)"
  by(induction p rule: edges_of_path.induct) auto

lemma alt_list_image:
  assumes "\<And> x. x \<in> set xs \<Longrightarrow> P' (f x) \<longleftrightarrow> P x"
    "\<And> x. x \<in> set xs \<Longrightarrow> Q' (f x) \<longleftrightarrow> Q x"
  shows "alt_list P' Q' (map f xs) \<longleftrightarrow> alt_list P Q xs"
  using assms
proof(induction xs arbitrary: P Q P' Q')
  case Nil
  then show ?case
    by (simp add: alt_list.intros(1))
next
  case (Cons a xs)
  show ?case 
    using Cons(2,3)
    unfolding alt_list_step list.map(2)
    by(subst Cons(1)[of Q' Q P' P]) auto
qed

lemma alt_path_image:
  assumes "inj_on f (Vs M \<union> set p)"
  shows "alt_path ((`) f ` M) (map f p) \<longleftrightarrow> alt_path M p"
  unfolding edges_of_path_image
proof(goal_cases)
  case 1
  have "e \<in> set (edges_of_path p) \<Longrightarrow> (f ` e \<notin> (`) f ` M) = (e \<notin> M)" for e
  proof(goal_cases)
    case 1
    hence e_in_p:"e \<subseteq> set p"
      by (simp add: edges_of_path_subset_path)
    moreover have "\<lbrakk>f ` e = f ` e'; e' \<in> M\<rbrakk> \<Longrightarrow> e \<in> M" for e'
    proof(goal_cases)
      case 1
      hence "e = e'"
        using e_in_p assms Vs_def[of M] inj_on_image_eq_iff[of f "Vs M \<union> set p" e e']
        by auto
      thus ?thesis
        using 1 by auto
    qed
    ultimately show ?thesis
      by auto
  qed
  thus ?case
    by(intro alt_list_image) auto
qed

lemma path_image:
  assumes "inj_on f (Vs G \<union> set p)"
  shows "path ((`) f ` G) (map f p) \<longleftrightarrow> path G p"
  using assms
proof(induction p rule: edges_of_path.induct, goal_cases)
  case 1
  then show ?case 
    by auto
next
  case (2 v)
  then show ?case 
    by (auto simp add: Vs_of_imaged_graph)
next
  case (3 v v' l)
  hence path_iff:"path ((`) f ` G) (f v' # map f l) = path G (v' # l)"
    by auto
  have edge_iff: "{f v, f v'} \<in> (`) f ` G \<longleftrightarrow> {v, v'} \<in> G"
  proof(rule, elim imageE, goal_cases)
    case (1 e)
    hence "f  ` {v, v'} = f ` e"
      by auto
    hence "{v,v'} = e" 
      apply(intro inj_onD[of "image f" "G"])
         apply auto
        apply (metis "3"(2) Vs_def inj_on_Un inj_on_image)
      subgoal
        using "1"(2) "3"(2) Sup_upper Un_empty_right Vs_def \<open>f ` {v, v'} = f ` e\<close> inf_sup_ord(4)
          inj_on_image_eq_iff insert_subset le_supI2 le_sup_iff list.simps(15) sup.commute sup_ge1
        by (smt (verit, del_insts))
      subgoal
        by (simp add: "1"(2))
      done
    then show ?case
      using "1"(2) by fastforce
  next
    case 2
    thus ?case
      using not_in_imageD by fastforce
  qed

  then show ?case 
    unfolding list.map(2) path_2 path_iff
    by auto
qed

lemma path_in_image_to_original_path:
  assumes "dblton_graph G" "inj_on f (Vs G)"
  shows "path ((`) f ` G) p \<Longrightarrow> \<exists> q. path G q \<and> map f q = p"
proof(induction p rule: path.induct)
  case path0
  then show ?case 
    by auto
next
  case (path1 v)
  then show ?case 
    by(auto simp add: Vs_of_imaged_graph intro: path.path1)
next
  case (path2 v v' vs)
  then obtain q where "path G q" "map f q = v' # vs"
    by auto
  then obtain q vv'' where "path G (vv''# q)" "map f (vv''#q) = v' # vs"
    by(cases q) auto
  moreover obtain vv vv' where "f vv = v" "f vv' = v'" "{vv, vv'} \<in> G"
    using path2(1) assms
    by (auto elim!: dblton_graphE simp add: doubleton_eq_iff insert_commute)
  moreover have "vv'' = vv'" 
    using assms(2) calculation(1,2,4,5) mem_path_Vs[of G "vv'' # q" vv'']  edges_are_Vs_2[of vv vv' G]
    by (auto simp add: inj_on_def)
  ultimately show ?case 
    by(intro exI[of _ "vv #vv'#q"]) auto
qed


lemma even_vert_image:
  assumes "inj_on f (Vs G \<union> Vs M \<union> {v})" "dblton_graph G"
  shows "even_vert ((`) f ` G) ((`) f ` M) (f v) \<longleftrightarrow> even_vert G M v"
proof-
  have assms:  "inj_on f (Vs G \<union> Vs M)" "dblton_graph G"
    using assms  by (auto simp add: inj_on_Un)
  note big_inj = assms(1)
  show ?thesis
  proof(rule, goal_cases)
    case 1
    then obtain p where p: "odd (length p)" "alt_path ((`) f ` M) p"
      "hd p \<notin> Vs ((`) f ` M)" "last p = (f v)" "distinct p"
      "((path ((`) f ` G) p \<and> length p \<noteq> 1) \<or> length p = 1)"
      by(auto simp add:  even_vert_def)
    thus ?case 
    proof(cases "v \<in> Vs (G \<union> M)", goal_cases)
      case 1
      thus ?case
      proof(elim disjE, goal_cases)
        case 1
        then obtain q where q: "path G q" "p = map f q "
          using path_in_image_to_original_path[of G f p]
            assms(1,2) inj_on_subset[of f "Vs G \<union> Vs M" "Vs G"] 
          by blast
        moreover have "inj_on f (Vs M \<union> set q)" 
          by (meson Un_upper2 assms(1) inj_on_subset le_supI1 le_sup_iff q(1) subset_path_Vs)
        moreover have "hd (map f q) = f (hd q)" 
          using 1 q by(cases q rule: list_cases3) auto
        moreover have "last (map f q) = f (last q)"
          using 1 q by(cases q rule: rev_cases) auto
        moreover have "f (last q) = f v \<Longrightarrow> last q = v"
          using 1 q assms(1) sup_ge1[of G M] vs_union[of G M] inj_on_contraD[of f "Vs (G \<union> M)" _ v]
            path_subset[of G "_ @ [_]" "G \<union> M"] v_in_apath_in_Vs_append[of "G \<union> M" _ _ "[]"]
          by(cases q rule: rev_cases) fastforce+
        moreover have "distinct q" 
          using 1(5) by(auto simp add: distinct_map q)
        ultimately show ?case
          using 1 
          by(auto intro!: exI[of _ q] simp add: even_vert_def alt_path_image Vs_of_imaged_graph)
      next
        case 2
        then show ?case 
          by(auto intro!: exI[of _ "[v]"] simp add: even_vert_def alt_list.intros(1) Vs_of_imaged_graph hd_last_same)
      qed
    next
      case 2
      show ?case
        using 2(7)
        by(auto intro!: exI[of _ "[v]"] simp add: even_vert_def alt_list.intros(1) vs_union)
    qed
  next
    case 2
    then obtain p where "odd (length p)" "alt_path M p" "hd p \<notin> Vs M" "last p = v" "distinct p" 
      "path G p \<or> length p = 1"
      by(auto simp add:  even_vert_def)
    then show ?case
    proof(cases "f v \<in> Vs ((`) f ` M)",goal_cases)
      case 1
      thus ?case
      proof(elim disjE, goal_cases)
        case 1
        moreover have "inj_on f (Vs M \<union> set p)" 
          by (metis Un_mono Un_upper2 assms(1) calculation(7) inj_on_subset subset_path_Vs sup.commute
              sup.idem)
        moreover have "hd (map f p) = f (hd p)"
          using 1 by(cases p) auto
        moreover have "\<lbrakk>f x = f (hd p); x \<in> Vs M\<rbrakk> \<Longrightarrow> x = hd p" for x 
          by (metis "1"(1) UnCI calculation(8) even_zero inj_on_eq_iff list.set_sel(1) list.size(3))
        moreover have "last (map f p) = f (last p)"
          using 1 by(cases p rule: rev_cases) auto
        moreover have "distinct (map f p)"
          using 1 calculation(8) inj_on_Un
          by(auto simp add: distinct_map)
        moreover have "path ((`) f ` G) (map f p)"
          using 1
          apply(subst path_image)
           apply auto 
          by (metis assms(1) inj_on_Un subset_path_Vs sup.orderE)
        ultimately show ?case 
          by(auto intro!: exI[of _ "map f p"] 
              simp add: even_vert_def alt_path_image Vs_of_imaged_graph) auto
      next
        case 2
        thus ?case 
          by (metis UnI2 Union_of_imaged Vs_def \<open>inj_on f (Vs G \<union> Vs M \<union> {v})\<close> hd_last_same inj_on_image_mem_iff
              insertI1 sup.coboundedI1 sup_ge2)
      qed
    next
      case 2
      thus ?case
        using assms(1) Vs_of_imaged_graph[of f M] Un_iff[of v "Vs G" "Vs M"]
          inj_on_image_mem_iff[of f "Vs G \<union> Vs M" v "Vs M"]
        by(cases p)(auto intro!: exI[of _ "[f v]"] simp add: even_vert_def alt_list.intros(1))
    qed
  qed
qed

lemma Delta_image:
  assumes "dblton_graph G" "inj_on f (Vs G \<union> X)"
  shows  "Delta ((`) f ` G) (f ` X) = (image f) ` (Delta G X)"
proof(rule, all \<open>rule, (elim in_DeltaE | elim imageE in_DeltaE)\<close>, goal_cases)
  case (1 e u v)
  then obtain uu vv where "{uu, vv} \<in> G"  "e= f ` {uu, vv}"
    using assms(1) by auto
  then obtain uu vv where "{uu, vv} \<in> G"  "u = f uu" "v = f vv" "e = f ` {uu, vv}"
    by (metis "1"(1) doubleton_eq_iff image_empty image_insert)
  moreover have "uu \<in> X"
    by (metis "1"(3) UnI1 assms(2) calculation(1,2) edges_are_Vs inj_on_image_mem_iff sup.cobounded2)
  moreover have "vv \<notin> X" 
    using "1"(4) calculation(3) by blast
  ultimately show ?case
    by (auto intro!: rev_image_eqI[of "{uu, vv}" _ _ "image f"] in_DeltaI[of "{uu, vv}" uu vv G X])
next
  case (2 e ee u v)
  moreover hence "f ` {u, v} \<in> ((`) f ` G)" 
    by(intro imageI) auto
  ultimately show ?case
    apply (auto intro!: in_DeltaI[of "{f u, f v}" "f u" "f v" ])
    using assms(2) Un_iff[of v "Vs G" X] Un_iff[of _ "Vs G" X] inj_on_contraD[of f "Vs G \<union> X" _ v]
      edges_are_Vs_2[of u v G]
    by force
qed

lemma inj_on_inter:"inj_on f (X \<union> Y) \<Longrightarrow> f ` X \<inter> f ` Y = f ` (X \<inter> Y)"
  by (simp add: inj_on_image_Int)

lemma edmonds_gallai_inj_carry_over:
  assumes "inj_on f (Vs (G \<union> M))"  "edmonds_gallai G M \<D> A" "graph_invar G" "dblton_graph M"
  shows "edmonds_gallai ((image f) ` G) ((image f) ` M) ((image f) ` \<D>) (f ` A)"
proof-
  note edmonds_gallaiD = edmonds_gallaiD[OF assms(2)]
  have goal1:"disjoint ((`) f ` \<D>)" 
    using edmonds_gallaiD(1,2) assms(1) vs_union[of G M]
      inj_on_subset[of f "Vs (G \<union> M)" "\<Union> \<D>"] disjoint_image[of f \<D>]
    by auto
  have goal2: "\<Union> ((`) f ` \<D>) \<subseteq> Vs ((`) f ` G)"
    unfolding Vs_of_imaged_graph Union_of_imaged 
    by (simp add: image_mono local.edmonds_gallaiD(2))
  have goal3: "X \<in> (`) f ` \<D> \<Longrightarrow> X \<noteq> {}" for X
    using local.edmonds_gallaiD(3) by fastforce
  have inj_on2:"inj_on f (Vs G \<union> \<Union> \<D>)"
    using assms(1) edmonds_gallaiD(2) vs_union[of G M] inj_on_Un[of f "Vs G" "Vs M"]
      Un_absorb2[of "\<Union> \<D>" "Vs G"]
    by auto
  have goal4: "f ` A = Neighbourhood ((`) f ` G) (\<Union> ((`) f ` \<D>))"
    using inj_on2 assms(3)
    unfolding Union_of_imaged 
    by(subst Neighbourhood_image)
      (simp_all add: local.edmonds_gallaiD(4))
  have goal5: "\<lbrakk>X \<in> (`) f ` \<D>; Y \<in> (`) f ` \<D>; X \<noteq> Y\<rbrakk> \<Longrightarrow> X \<leftarrow>|\<rightarrow>\<^bsub>(`) f ` G\<^esub> Y" for X Y
  proof(goal_cases)
    case 1
    then obtain XX YY where XX_YY:"XX \<in> \<D>" "X = f ` XX" "YY \<in> \<D>" "Y = f ` YY"
      by blast
    moreover hence "XX \<noteq> YY"
      using "1"(3) by fastforce
    moreover have "inj_on f (Vs G \<union> XX \<union> YY)"
      using calculation(1,3) inj_on2 edmonds_gallaiD(2) Union_upper[of XX \<D>]
        Union_upper[of YY \<D>] Un_absorb2[of XX "Vs G"] Un_absorb2[of YY "Vs G"]
        Un_absorb2[of "\<Union> \<D>" "Vs G"]
      by auto
    ultimately show ?case
      using assms(3) edmonds_gallaiD(5)
      by(simp add: connected_sets_of_vertices_image)
  qed
  have goal6: "\<lbrakk>X \<in> (`) f ` \<D>; x \<in> X\<rbrakk> \<Longrightarrow> \<exists>M. graph_matching ( (`) f ` G \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x}"
    for X x
  proof(goal_cases)
    case 1
    then obtain XX xx where XX_xx: "XX \<in> \<D>" "X = f ` XX" "x = f xx" "xx \<in> XX"
      by auto
    obtain M where M: "matching M" "M \<subseteq> G \<lbrakk>XX\<rbrakk>" "Vs M = XX - {xx}"
      using XX_xx(1,4) local.edmonds_gallaiD(6) by force
    have inj_on3: "inj_on f (Vs M)" 
      using XX_xx(1) inj_on2 M(3) inj_on_Un[of f "Vs G" "\<Union> \<D>"]
        inj_on_subset[of f "\<Union> \<D>" XX] inj_on_subset[of f XX "Vs M"]
      by auto
    have inj_on4: "inj_on f (Vs G \<union> XX)"
      using edmonds_gallaiD(2) XX_xx(1)
      by(auto intro!: inj_on_subset[OF inj_on2])
    have " graph_matching ( ((`) f ` G) \<lbrakk>f ` XX\<rbrakk>) ((`) f ` M)"
      using inj_on3 unfolding graph_inter_Vs_image[OF inj_on4]
      by(intro graph_matching_image)(auto simp add: M(1,2)) 
    moreover have "Vs ((`) f ` M) = f ` XX - {f xx}" 
      unfolding Vs_of_imaged_graph M(3)
      using inj_on4 XX_xx edmonds_gallaiD(2) 
      by (subst inj_on_image_set_diff[of _ "Vs G"])(auto simp add: inj_on_Un)
    ultimately show ?case 
      unfolding XX_xx
      by(intro exI[of _ "(image f) ` M"]) auto
  qed
  have goal7: "X \<in> (`) f ` \<D> \<Longrightarrow> \<exists>x. x \<in> X \<and> Vs ( (`) f ` M \<lbrakk>X\<rbrakk>) = X - {x}" for X
  proof(goal_cases)
    case 1
    then obtain XX where XX_xx: "XX \<in> \<D>" "X = f ` XX" 
      by auto
    obtain x where x: "x \<in> XX" "Vs (M \<lbrakk>XX\<rbrakk>) = XX - {x}" 
      using XX_xx(1) edmonds_gallaiD(7) by force
    have inj_on5: "inj_on f (Vs M \<union> XX)" 
      using edmonds_gallaiD(2) XX_xx(1)
      by(auto intro!: inj_on_subset[OF assms(1)] simp add: vs_union)
    have "Vs ( (`) f ` M \<lbrakk>X\<rbrakk>) = X - {f x}"
      using inj_on2 XX_xx(1) edmonds_gallaiD(2) x(1)
      unfolding  XX_xx graph_inter_Vs_image[OF inj_on5] Vs_of_imaged_graph x(2)
      by(subst inj_on_image_set_diff[of _ "Vs G"])(auto simp add:  inj_on_Un)
    then show ?case 
      by(intro exI[of _ "f x"])(simp add: XX_xx(2) x(1))
  qed
  have goal8: 
    "v \<in> Vs ((`) f ` G) \<Longrightarrow> even_vert ((`) f ` G) ((`) f ` M) v = (v \<in> \<Union> ((`) f ` \<D>))" for v
  proof(goal_cases)
    case 1
    then obtain vv where vv: "vv \<in>Vs G" "v = f vv"
      by (metis Vs_of_imaged_graph image_iff)
    moreover hence "inj_on f (Vs G \<union> Vs M \<union> {vv})"
      using assms(1) vs_union[of G M] sup.absorb_iff1[of "{vv}" "Vs (G \<union> M)"] 
      by auto
    moreover have "f vv \<in> f ` \<Union> \<D> \<longleftrightarrow> vv \<in> \<Union> \<D>"
      by (metis inj_on2 inj_on_image_mem_iff local.edmonds_gallaiD(2) sup.absorb1 vv(1))
    ultimately show ?case
      using 1 assms(3)
      by(simp add: vv even_vert_image[of f G M ]  edmonds_gallaiD(8)[of vv] image_Union)
  qed

  have f_union:"f ` X \<union> f ` Y = f ` (X \<union> Y)" for X Y
    by auto
  have "inj_on f (Vs M \<union> (\<Union> \<D> \<union> A))"
    by (smt (verit, best) Neighbourhood_in_G Un_iff Union_Un_distrib Vs_def assms(1) inj_on_def
        local.edmonds_gallaiD(2,4) sup.orderE)
  hence goal9: "Delta ((`) f ` M) (\<Union> ((`) f ` \<D>) \<union> f ` A) = {}"
    using assms(4) edmonds_gallaiD(9)
    unfolding Union_of_imaged f_union
    by(simp add: Delta_image)
  have goal10: "D \<in> (`) f ` \<D> \<Longrightarrow> card (Delta ((`) f ` M) D) \<le> 1" for D
  proof(goal_cases)
    case 1
    then obtain X where X: "X \<in> \<D>" "D = f ` X" 
      by auto
    moreover have "inj_on f (Vs M \<union> X)"
      by (meson Sup_le_iff \<open>inj_on f (Vs M \<union> (\<Union> \<D> \<union> A))\<close> calculation(1) set_eq_subset subset_inj_on
          sup.coboundedI1 sup_mono)
    moreover have "inj_on ((`) f) (Delta M X)"
      by (metis Vs_def assms(1) in_DeltaD(2) inj_on_Un inj_on_image inj_on_subset subsetI)
    ultimately show ?case
      using assms(4) edmonds_gallaiD(10)
      unfolding Union_of_imaged f_union X
      by(simp add: Delta_image card_image)
  qed
  have goal11: "Vs ((`) f ` G) - \<Union> ((`) f ` \<D>) \<subseteq> Vs ((`) f ` M)"
    unfolding Vs_of_imaged_graph Union_of_imaged
    by (meson image_diff_subset image_mono local.edmonds_gallaiD(11) subset_trans)
  have inj_on6: "inj_on f (Vs G \<union> A)"
    by (metis Neighbourhood_in_G inj_on2 local.edmonds_gallaiD(2,4) sup.absorb1)
  have inj_on7: "inj_on ((`) f) (M \<union> (G \<lbrakk>A\<rbrakk>))"
    by (metis (no_types, lifting) Vs_def assms(1) graph_inter_Vs_subset(1) inf_sup_aci(5,8) inf_sup_ord(4)
        inj_on_image inj_on_subset sup.mono)
  have goal12: "(`) f ` M \<inter> (((`) f ` G) \<lbrakk>f ` A\<rbrakk>) = {}"
    using  inj_on6 inj_on7
    by(simp add: graph_inter_Vs_image inj_on_inter edmonds_gallaiD(12))


  show ?thesis
    by(intro edmonds_gallaiI goal1 goal2 goal3 goal4 goal5 goal6 goal7 goal8 goal9 goal10
        goal11 goal12|
        assumption)+
qed

locale obtain_edmonds_gallai =
  fixes G
  assumes graph_invar:"graph_invar (G:: 'v set set)"
begin

datatype 'a edg_node = act (vertex: 'a) | dummy (index: nat)

definition "G' = (image act) ` G"

lemma graph_invar': "graph_invar G'"
  unfolding G'_def
  by(intro inj_image_graph_invar)
    (auto simp add: graph_invar intro!: injI)

interpretation compute: compute_alt_path_and_edg_use
  where sel = "\<lambda> X. (SOME x. x \<in> X)"
    and create_vert = "\<lambda> X. (SOME x. x \<notin> X)"
    and E = G'
    and sel_from_sets = "\<lambda> P X. (SOME x. x \<in> X \<and> P x)"
proof(unfold_locales, goal_cases)
  case 1
  then show ?case 
    using graph_invar' by auto
next
  case (2 s)
  then show ?case 
    by (simp add: some_in_eq)
next
  case (3 vs)
  have "\<exists> x. x \<notin> vs"
  proof-
    define i where "i = Max (insert 0 {i | i. dummy i \<in> vs})"
    have "finite (insert 0 {i | i. dummy i \<in> vs})" 
      using 3 
      by (auto intro!: finite_subset[of "{i | i. dummy i \<in> vs}" 
            "index ` {dummy i | i. dummy i \<in> vs}", simplified] image_eqI finite_imageI
          finite_subset[of "{dummy i |i. dummy i \<in> vs}" vs])
    hence "dummy j \<in> vs \<Longrightarrow> i \<ge> j" for j
      by(auto simp add: i_def)
    hence "dummy (Suc i) \<notin> vs"
      by force
    thus ?thesis
      by auto
  qed
  then show ?case
    using someI_ex[of "\<lambda>R. R \<notin> vs"] by auto
next
  case (4 \<D> P)
  then show ?case 
    using someI_ex[of "\<lambda>uub. uub \<in> \<D> \<and> P uub"] by auto
next
  case (5 \<D> P)
  then show ?case 
    using someI_ex[of "\<lambda>uub. uub \<in> \<D> \<and> P uub"] by auto
qed

context
  fixes M::" 'v set set"
begin

abbreviation "computed_decomposition \<equiv> compute.find_decomposition G' (image act ` M)"

lemmas computed_decomposition_correct = compute.find_decomposition_correct

definition "Odds = (image vertex) ` (fst computed_decomposition)"

definition "evens = vertex ` (snd computed_decomposition)"

lemma G_vertex_image:"G = (image vertex) ` G'" 
  using graph_invar image_iff 
  by (fastforce simp add: G'_def)

lemma vertex_inj_on_G':
  "GG \<subseteq> G' \<Longrightarrow> inj_on vertex (Vs GG)"
proof(rule, goal_cases)
  case 1
  moreover have "\<lbrakk>GG \<subseteq> (`) act ` G; x \<in> Vs GG; y \<in> Vs GG; vertex x = vertex y\<rbrakk> \<Longrightarrow> x = y" for x y
    by(cases x, all \<open>cases y\<close>) (auto simp add: vs_member)
  ultimately show ?case
    by(auto simp add: inj_on_def G'_def)
qed

lemma decomposition_correct: 
  assumes "max_card_matching G M"
  shows "edmonds_gallai G M Odds evens"
proof-
  have M'_max: "max_card_matching G' ((`) act ` M)"
  proof(subst G'_def, subst max_card_matching_image_iff, goal_cases)
    case 1
    then show ?case 
      by(auto intro!: inj_onI)
  qed (simp add: assms)
  have M': "edmonds_gallai G' (image act ` M) (fst computed_decomposition)
              (snd computed_decomposition)"
    using M'_max  computed_decomposition_correct by auto
  have M'_def: "M = (image vertex) ` ((`) act ` M)" 
  proof(rule, all \<open>rule\<close>, goal_cases)
    case (1 e)
    then show ?case 
      by(intro rev_image_eqI[of "(`) act e" "(`) act ` M" _ "(`) vertex"])
        (auto simp add: image_comp)
  qed (auto simp add: image_comp)
  have G'_absorb_M':"G' \<union>  ((`) act ` M) = G'"
    using M'_max max_card_matchingDs(1) by blast
  have vertex_inj_on: "inj_on vertex (Vs (G' \<union> ((`) act ` M)))" 
    by(auto intro: vertex_inj_on_G' simp add: G'_absorb_M')
  have "dblton_graph ((`) act ` M)" 
    using G'_absorb_M' graph_invar' by auto
  hence "edmonds_gallai G M Odds evens"
    apply(subst G_vertex_image, subst M'_def)
   unfolding Odds_def evens_def
   by(intro edmonds_gallai_inj_carry_over)
     (simp_all add: G'_absorb_M' vertex_inj_on_G' graph_invar'
        M'(1) compute.g.graph_abs_subset graph_abs.dblton_E max_card_matchingDs(1))
  thus ?thesis
    by auto
qed
end
end

definition "inessential G v = (\<exists> M. max_card_matching G M \<and> v \<notin> Vs M)"

lemma inessentialE:
  "\<lbrakk>inessential G v; \<And> M. \<lbrakk> max_card_matching G M; v \<notin> Vs M\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  and inessentialI:
  "\<lbrakk> max_card_matching G M; v \<notin> Vs M\<rbrakk> \<Longrightarrow> inessential G v"
  and inessentialD: 
  "inessential G v \<Longrightarrow> \<exists> M. max_card_matching G M \<and> v \<notin> Vs M"
  by(auto simp add: inessential_def)

definition "inessentials G = {v . inessential G v \<and> v \<in> Vs G}"

lemma in_inessentialsE:
  "\<lbrakk>v \<in> inessentials G; \<lbrakk>inessential G v; v \<in> Vs G\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  and in_inessentialsI:
  "\<lbrakk>inessential G v; v \<in> Vs G\<rbrakk> \<Longrightarrow> v \<in> inessentials G"
  by(auto simp add: inessentials_def)

lemma uncovered_by_a_max_matching_even_in_other_max_matching:
  assumes "max_card_matching G M" "max_card_matching G M'" "v \<notin> Vs M" "graph_invar G"
  shows "even_vert G M' v"
proof(cases "v \<in> Vs M'")
  case False
  then show ?thesis
    by(auto intro!: exI[of _ "[v]"] simp add: even_vert_def alt_list.intros(1))
next
  case True
  note M_props = max_card_matchingDs[OF assms(1)]
  note M'_props = max_card_matchingDs[OF assms(2)]

  have x_inVs_M_M':"v \<in> Vs (M \<union> M')"
    by (simp add: True vs_union)
  define C where "C = connected_component (M \<union> M') v"
  have x_in_C: "v \<in> C"
    by (simp add: C_def in_own_connected_component)
  interpret graph_abs_MM': graph_abs "M \<union> M'"
    using M'_props(1) M_props(1) assms(4) graph_abs.intro graph_abs_mono by fastforce     
  have dbltonM: "dblton_graph M" and dbltonM': "dblton_graph M'" 
    using M_props(1) M'_props(1) assms(4) by blast+
  have C_is_component: "C \<in> connected_components (M \<union> M')" 
    by (simp add: C_def connected_component_in_components x_inVs_M_M')
  have deg_in_MM': "degree (M \<union> M') v \<le> 2" for v
    using M_props M'_props  by(auto  intro!: degree_matching_union)
  define p where "p = (component_path' (M \<union> M') C)"
  note p_props = graph_abs_MM'.component_path'_works[OF C_is_component deg_in_MM', folded p_def]
  have p_not_Nil: "p \<noteq> []" 
    using p_props(2) x_in_C by fastforce
  have "v = hd p \<or> v = last p"
  proof(rule ccontr, goal_cases)
    case 1
    then obtain p1 p2 y z where p_split: "p = p1@[y,v,z]@p2" 
      by (metis element_of_list_cases last_ConsL last_appendR list.sel(1) not_Cons_self2 p_props(2)
          x_in_C)
    have "{y, v} \<in> set (edges_of_path p)"  "{v, z} \<in> set (edges_of_path p)"
      using edges_of_path_append_subset p_split by fastforce+
    moreover have "set (edges_of_path p) \<subseteq> M \<union> M'"
      by (simp add: p_props(1) path_edges_subset)
    ultimately have "{y, v} \<in> M \<union> M'"  "{v, z} \<in> M \<union> M'" by auto
    hence yx_xz_in_M': "{y, v} \<in> M'"  "{v, z} \<in> M'"
      using assms(3) insert_commute  assms(3) by auto
    hence "{y, v} \<noteq> {v, z}" 
      using p_props(3) p_split yx_xz_in_M' by (auto simp add: doubleton_eq_iff)
    thus False 
      using  matching_edges_not_eqD(3)[OF M'_props(2)] yx_xz_in_M'(1,2)
      by fast
  qed
  hence "\<exists> p. path (M \<union> M') p \<and> set p = C \<and> distinct p \<and> p \<noteq> Nil \<and> hd p = v"
    using p_not_Nil p_props
    by (auto  intro: exI[of _ "rev p"] rev_path_is_path simp add: hd_rev)
  then obtain p where p_props:"path (M \<union> M') p" "set p = C" "distinct p" "p \<noteq> Nil" "hd p = v"
    by auto
  obtain e where e_for_x: "v \<in> e" "e \<in> M'"
    using assms(3) x_inVs_M_M' by(auto elim!: in_Vs_unionE  simp add: vs_member)
  then obtain y where yx:"y \<in> e" "v \<noteq> y"
    using graph_abs_MM'.subset_edges_G by auto
  hence e_is_xy:"e = {v, y}" 
    using e_for_x(1,2) graph_abs_MM'.subset_edges_G[of "{e}" e]
    by auto
  hence "reachable (M \<union> M') v y" 
    using e_for_x
    by(auto intro!: edges_reachable)
  hence "v \<in> set p" "y \<in> set p"
    using x_in_C
    by (auto simp add: p_props(2) C_def in_connected_componentI)
  hence length_p: "2 \<le> length p"
    using yx(2) by(cases p rule: list_cases3) auto
  have alt_path_M_p: "alt_path M p" 
    and alt_list_M_M'_p: 
    "alt_list (\<lambda>e. e \<in> M' \<and> e \<notin> M) (\<lambda>e. e \<in> M \<and> e \<notin> M') (edges_of_path p)"
    using  p_props(1,3,5) length_p M_props(1,2) M'_props(1,2) assms(3) dbltonM dbltonM'
    by(all \<open>intro union_of_matchings_alt_path[of M M'] union_of_matchings_alt_list_M'_M[of M M']\<close>)
      auto
  have walk_p: "walk_betw (M \<union> M') v p (last p)"
    by (simp add: nonempty_path_walk_between p_props(1,4,5))
  have p_degree: "x \<in> set p \<Longrightarrow> degree (M \<union> M') x \<le> 2" for x
    by (simp add: deg_in_MM')
  note x_and_last_degr_same =
    component_walk_vertex_degress(3)[OF p_degree length_p p_props(3) walk_p
      p_props(2)[simplified C_def] graph_abs_MM'.graph, simplified]
  moreover have degree_x: "degree (M\<union>M') v = 1"
    using assms(3) e_for_x M'_props(2)
    by(auto intro!: unique_edge_degree_one[of _ e]
        dest: matching_unique_match)
  ultimately have degree_last_p:"degree (M\<union>M') (last p) = 1"
    by auto
  have odd_p: "odd (length p)"
  proof(rule notI, goal_cases)
    case 1
    hence last_edge: "last (edges_of_path p) \<notin> M" "last (edges_of_path p) \<in> M'" 
      using p_props(4) alt_list_M_M'_p
        alternating_list_odd_last[of "\<lambda>e. e \<in> M' \<and> e \<notin> M" "\<lambda>e. e \<in> M \<and> e \<notin> M'" 
          "edges_of_path p"]
      by(auto simp add: edges_of_path_length')
    moreover have "last p \<notin> Vs M"
    proof(rule ccontr, goal_cases)
      case 1
      hence "last (edges_of_path p) \<in> M" 
        using "1" degree_last_p length_p last_edge(2)  graph_abs_MM'.last_v_in_last_e'[of p]
          degree_one_unique[of "M \<union> M'" "last p"]
        by (auto elim!: vs_member_elim)
      thus ?case
        by (simp add: last_edge(1))
    qed
    ultimately have "matching_augmenting_path M p"
      by (simp add: alt_path_M_p assms(3) length_p matching_augmenting_path_def p_props(5))
    hence "graph_augmenting_path G M p"
      using M'_props(1) M_props(1) p_props(1,3) path_subset by fastforce
    hence "\<not> max_card_matching G M" 
      using assms(4) Berge[of M G] finite_Vs_then_finite[of M] graph_invar_subset[of G M]
      by(auto  simp add: max_card_matching_def linorder_not_less[of "card M" "card _", symmetric])
    thus False
      by (simp add: assms(1))
  qed
  moreover then have "alt_path M' (rev p)" 
    using alt_list_M_M'_p alt_list_cong
    by(intro rev_of_rev_alt_path_is_alt_path) fastforce+
  moreover have "hd (rev p) \<notin> Vs M'" 
  proof-
    have last_edge: "last (edges_of_path p) \<notin> M'" "last (edges_of_path p) \<in> M" 
      using p_props(4) alt_list_M_M'_p length_p odd_p
        alternating_list_even_last
      by(fastforce simp add: edges_of_path_length')+
    moreover have "last p \<notin> Vs M'"
    proof(rule ccontr, goal_cases)
      case 1
      hence "last (edges_of_path p) \<in> M'" 
        using "1" degree_last_p length_p last_edge(2)  graph_abs_MM'.last_v_in_last_e'[of p]
          degree_one_unique[of "M \<union> M'" "last p"]
        by (auto elim!: vs_member_elim)
      thus ?case
        by (simp add: last_edge(1))
    qed
    ultimately show ?thesis
      by (simp add: hd_rev)
  qed
  moreover have "last (rev p) = v"
    by (simp add: last_rev p_props(5))
  moreover have "distinct (rev p)" 
    by (simp add: p_props(3))
  moreover have "path G (rev p)" 
    using M'_props(1) M_props(1) p_props(1) path_subset rev_path_is_path_iff by fastforce
  ultimately show ?thesis
    unfolding even_vert_def
    by(intro exI[of _ "rev p"]) auto
qed

lemma even_uncovered_by_other_max_matching:
  assumes "graph_invar G" "max_card_matching G M" "even_vert G M v" "v \<in> Vs G"
  shows "\<exists> M'. max_card_matching G M' \<and> v \<notin> Vs M'"
proof(cases "v \<notin> Vs M")
  case True
  then show ?thesis 
    using assms by auto
next
  case False
  obtain p where
    "odd (length p)" "alt_path M p" "hd p \<notin> Vs M" "last p = v" "distinct p"
    "path G p \<or> length p = 1"
    using even_vertD[OF assms(3)] by auto
  hence p: "odd (length p)" "alt_path M p" "hd p \<notin> Vs M" "last p = v" "distinct p" "path G p" 
    using assms(4)
    by(all \<open>cases p rule: list_cases3\<close>) auto
  have length_p_geq_3:"length p \<ge> 3"
    using p assms(3) False Suc_le_eq odd_pos
    by(cases p rule: list_cases3)  auto
  note M_props = max_card_matchingDs[OF assms(2)]
  have "matching (M \<oplus> set (edges_of_path p))"
    using p(1,2,3,5) M_props(2)
    by(auto intro: symm_diff_is_matching)
  moreover have "M \<oplus> set (edges_of_path p) \<subseteq> G"
    using M_props(1) p(6) path_ball_edges
    by (auto dest!: set_mp[OF sym_diff_subset])
  moreover have "card (M \<oplus> set (edges_of_path p)) = card M"
    using p(1,2,3,5) M_props(1,2) assms(1)
    by(auto intro!: card_symm_diff_matching rev_finite_subset[of G M] 
        intro: finite_Vs_then_finite 
        simp add: edges_of_path_length)
  ultimately have "max_card_matching G (M \<oplus> set (edges_of_path p))"
    by (simp add: M_props(3) max_card_matchingI')
  moreover have "v \<notin> Vs (M \<oplus> set (edges_of_path p))"
    using M_props(2) p(1,2,4,5) length_p_geq_3
    by(subst rematch_atl_path_Vs_change) auto
  ultimately show ?thesis
    by auto
qed

lemma inessentials_are_evens_of_max_matching:
  assumes "graph_invar G" "max_card_matching G M" 
  shows "inessentials G = {v | v. v \<in> Vs G \<and> even_vert G M v}"
  using assms
  by(auto elim!: in_inessentialsE inessentialE
          intro: uncovered_by_a_max_matching_even_in_other_max_matching
                 in_inessentialsI inessentialI
          dest!: even_uncovered_by_other_max_matching[OF assms])

lemma two_unconnected_sets_connected_component_not_inter_both:
  assumes "(connected_component G z) \<inter> X \<noteq> {}"
          "(connected_component G z) \<inter> Y \<noteq> {}"
          "Vs G \<subseteq> X \<union> Y" "X \<inter> Y  = {}" "X \<leftarrow>|\<rightarrow>\<^bsub>G\<^esub> Y"
    shows False
proof-
  obtain x y where xy: "x \<in> X" "x \<in> connected_component G z"
     "y \<in> Y" "y \<in> connected_component G z"
    using assms by auto
  then obtain p where p: "walk_betw G x p y" 
    using assms(4) connected_components_member_eq[of x G z] in_con_comp_has_walk[of y G x] 
    by auto
  have p_in_G: "set p \<subseteq> Vs G" 
    using p walk_in_Vs by force
  have xy_in_p: "x \<in> set p" "y \<in> set p" 
    using hd_in_set p by(auto simp add: walk_betw_def)
  have in_p_not_in_rw:"z \<in> set p \<Longrightarrow> z \<notin> X \<longleftrightarrow> z \<in> Y"  "z \<in> set p \<Longrightarrow> z \<notin> Y \<longleftrightarrow> z \<in> X" for z
    using assms(3,4) p_in_G by auto
  obtain p1 p2 x' y' where p_split: "p = p1@[x', y']@p2"
    "x' \<in> X \<and> y' \<in> Y \<or> x' \<in> Y \<and> y' \<in> X" 
    using list_P_switch[of x p "\<lambda> x. x \<in> X" y]  xy_in_p xy(1,3)
    by(auto simp add: in_p_not_in_rw)
  hence "{x', y'} \<in> G" 
    using edge_mid_path p by(auto simp add: walk_betw_def)
  hence "X \<longleftrightarrow>\<^bsub>G\<^esub> Y" 
    using p_split(2) 
    by(auto intro: exI[of _ y', OF exI[of _ x']] 
         simp add: connected_set_of_vertices_def doubleton_eq_iff insert_commute)
  thus False
    by (simp add: assms(5))
qed

lemma connected_sets_of_certices_mono:
  "\<lbrakk>connected_set_of_vertices X G Y;G\<subseteq> G'; X \<subseteq> X'; Y \<subseteq> Y'\<rbrakk> \<Longrightarrow> connected_set_of_vertices X' G' Y'"
and un_connected_sets_of_certices_anti_mono:
  "\<lbrakk>\<not>connected_set_of_vertices X' G' Y';G\<subseteq> G'; X \<subseteq> X'; Y \<subseteq> Y'\<rbrakk> \<Longrightarrow> \<not>connected_set_of_vertices X G Y"
  by(force simp add: connected_set_of_vertices_def)+

lemma whole_edge_in_comp:
 "\<lbrakk>dblton_graph G; x \<in> e; x \<in> connected_component G y; e \<in> G\<rbrakk> 
   \<Longrightarrow> e \<subseteq> connected_component G y" 
proof(goal_cases)
  case 1
  hence reach1: "reachable G y x" 
    using vs_member_intro[of x e G] Paths.reachable_refl[of x G] in_connected_componentE[of x G y]
    by auto
  moreover obtain z where z: "e = {x, z}"
    using "1"(1,2,4) by blast
  ultimately have "reachable G y z"
    using "1"(4) edges_reachable[of x z G] Paths.reachable_trans[of G y x z] 
    by auto
  thus ?case
    by (simp add: "1"(3) in_connected_componentI z)
qed

lemma Vs_of_graph_inter_component_is_component:
  "\<lbrakk>y \<in> Vs G; dblton_graph G\<rbrakk> \<Longrightarrow> Vs (G\<lbrakk>connected_component G y\<rbrakk>) = connected_component G y"
proof(rule, all \<open>rule\<close>, goal_cases)
  case (1 x)
  then show ?case 
 using graph_inter_Vs_subset(2) by force
next
  case (2 x)
  then obtain e where e: "e \<in> G" "x \<in> e" 
    using vs_member[of x G] in_connected_component_in_edges[of x G y]
    by auto
  hence "e \<subseteq> connected_component G y"
    by (simp add: "2"(2,3) whole_edge_in_comp)
  hence "e \<in> G \<lbrakk>connected_component G y\<rbrakk>"
    by (simp add: e(1) in_graph_inter_VsI)
  then show ?case
    using e(2) by blast
qed

lemma perfect_matching_perfect_matching_of_component:
  assumes "perfect_matching G M" "y \<in> Vs G" "dblton_graph G"
  shows "perfect_matching (G\<lbrakk>connected_component G y\<rbrakk>) (M \<lbrakk>connected_component G y\<rbrakk>)"
proof(rule perfect_matchingI, goal_cases)
  case 1
  then show ?case
  using assms 
  by(auto elim!: perfect_matchingE 
       simp add: graph_matching_inter_Vs 
           dest: graph_inter_subset)
next
  case 2
  then show ?case 
  using assms 
  by(auto elim!: perfect_matchingE
       simp add: graph_matching_inter_Vs 
           dest: graph_inter_subset)
next
  case 3
  then show ?case 
  proof(rule, all \<open>rule, elim vs_member_elim\<close>, goal_cases)
    case (1 x e)
    then obtain e' where e': "e' \<in> M" "x \<in> e'" 
      using assms(1)
      by(auto elim!:  perfect_matching_edgeE dest!: in_graph_inter_VsD(1))
    hence "e' \<in>  M \<lbrakk>connected_component G y\<rbrakk>" 
      using 1(1) assms(1,3) 1(2)
       perfect_matching_member[of G M] whole_edge_in_comp[OF assms(3)e'(2), of y]
       in_graph_inter_VsI[of e' M "connected_component G y"]
      by (auto elim: in_graph_inter_VsE)
    then show ?case 
      using e'(2) by blast
  next
    case (2 x e)
    then show ?case 
      using assms graph_inter_Vs_subset(2) Vs_of_graph_inter_component_is_component[OF assms(2,3)]
      by force
  qed
qed

lemma perfect_matching_even_graph:
  assumes "perfect_matching G M" "dblton_graph G"
  shows "even (card (Vs G))"
  using assms(1,2) dvd_triv_left[of "2" "card M"] perfect_matching_card[of G M]
  by (fastforce simp add: graph_abs_def)

lemma perfect_matching_component_even:
  assumes "perfect_matching G M" "y \<in> Vs G" "dblton_graph G"
  shows "even (card (connected_component G y))"
proof(cases "finite (connected_component G y)")
  case True
  have "perfect_matching (G\<lbrakk>connected_component G y\<rbrakk>) (M \<lbrakk>connected_component G y\<rbrakk>)"
    by (simp add: assms(1,2,3) perfect_matching_perfect_matching_of_component)
  hence "even (card (Vs (G\<lbrakk>connected_component G y\<rbrakk>)))" 
    by (simp add: assms(3) dblton_graph_Vs_inter perfect_matching_even_graph)
  moreover have "Vs (G\<lbrakk>connected_component G y\<rbrakk>) = connected_component G y"
    by (simp add: Vs_of_graph_inter_component_is_component assms(2,3))
  ultimately show ?thesis 
    by simp
qed simp

lemma empty_delta_component_confined:
  assumes "dblton_graph G" "Delta G X = {}" "x \<in> X"
  shows "connected_component G x \<subseteq> X"
proof(rule ccontr, goal_cases)
  case 1
  obtain y where xy: "y \<in> connected_component G x" "y \<notin> X"
   using "1" by blast
  then obtain p where p: "walk_betw G x p y"
    using assms(3) in_con_comp_has_walk[of y G x]
    by auto
  have p_in_G: "set p \<subseteq> Vs G" 
    using p walk_in_Vs by force
  have xy_in_p: "x \<in> set p" "y \<in> set p" 
    using hd_in_set p by(auto simp add: walk_betw_def)
  obtain p1 p2 x' y' where p_split: "p = p1@[x', y']@p2"
    "x' \<in> X \<and> y' \<notin> X \<or> x' \<notin> X  \<and> y' \<in> X" 
    using list_P_switch[of x p "\<lambda> x. x \<in> X" y]  xy_in_p xy(2) assms(3)
    by auto
  hence "{x', y'} \<in> G" 
    using edge_mid_path p by(auto simp add: walk_betw_def)
  hence "{x', y'} \<in> Delta G X"
    using  p_split(2) by(auto intro: in_DeltaI)
  thus False
    using assms(2) by auto
qed

lemma component_of_factor_critical_odd:
  assumes "\<And> x. x \<in> X \<Longrightarrow> \<exists> M. graph_matching (G \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x}"
          "connected_component G y \<subseteq> X" "graph_invar G"
    shows "odd (card (connected_component G y))" 
proof-
  obtain M where M: "graph_matching (G \<lbrakk>X\<rbrakk>) M" "Vs M = X - {y}"
    using assms(1,2) in_own_connected_component[of y] by force
  have matching_confined_in_component:
    "graph_matching (G \<lbrakk>connected_component G y\<rbrakk>) (M \<lbrakk>connected_component G y\<rbrakk>)"
    using M(1)  graph_inter_Vs_subset(1) 
    by(intro graph_matching_inter_Vs) auto
  have Vs_M_projected_subset: "Vs (M \<lbrakk>connected_component G y\<rbrakk>) \<subseteq> connected_component G y - {y}"
    using M(2) graph_inter_Vs_subset(1,2)[of M "connected_component G y"]
      Vs_subset[of " M \<lbrakk>connected_component G y\<rbrakk>" M]
    by auto
  have Vs_M_projected_superset:
       "Vs (M \<lbrakk>connected_component G y\<rbrakk>) \<supseteq> connected_component G y - {y}"
  proof(rule, goal_cases)
    case (1 x)
    hence 1: "x \<in> connected_component G y" "x \<noteq> y" 
      by auto
    then obtain e where e: "e \<in> M" "x \<in> e"
      using M(2) assms(2) vs_member[of x M] 
      by auto
    hence "e \<subseteq> connected_component G y" 
      using "1"(1) M(1) assms(3) in_graph_inter_VsD(1) whole_edge_in_comp[of G x e]
      by force
    hence "e \<in> M \<lbrakk>connected_component G y\<rbrakk>"
      by (simp add: e(1) in_graph_inter_VsI)
    then show ?case 
      using e(2) by auto
  qed
  have component_is_M_vs: "connected_component G y - {y} = Vs (M \<lbrakk>connected_component G y\<rbrakk>)"
    by (simp add: Vs_M_projected_subset Vs_M_projected_superset subset_antisym)
  moreover have perfect_M:
   "perfect_matching (G \<lbrakk>connected_component G y - {y}\<rbrakk>) (M \<lbrakk>connected_component G y - {y}\<rbrakk>)"
  proof(rule perfect_matchingI, goal_cases)
    case 1
    then show ?case 
      using M(1) graph_inter_Vs_subset(1) graph_inter_subset[of M G] by force
  next
    case 2
    then show ?case 
      using M(1) graph_matching_inter_Vs by auto
  next
    case 3
    have "perfect_matching ( G \<lbrakk>Vs ( M \<lbrakk>connected_component G y\<rbrakk>)\<rbrakk>) ( M \<lbrakk>connected_component G y\<rbrakk>)"
     using matching_confined_in_component graph_inter_Vs_subset(1)[of G "connected_component G y"]
        perfect_matching_if_projected_to_matched_verts[of " M \<lbrakk>connected_component G y\<rbrakk>" G]
     by(auto dest: perfect_matchingD(3))
   moreover have "perfect_matching ( M \<lbrakk>Vs ( M \<lbrakk>connected_component G y\<rbrakk>)\<rbrakk>)
             ( M \<lbrakk>connected_component G y\<rbrakk>)"
      using matching_confined_in_component 
        graph_inter_Vs_subset(1)[of M "connected_component G y"]
        perfect_matching_if_projected_to_matched_verts[of " M \<lbrakk>connected_component G y\<rbrakk>" M]
      by(auto dest: perfect_matchingD(3))
    ultimately show ?case
      using matching_confined_in_component component_is_M_vs
      by(force dest: perfect_matchingD(3))
  qed
  hence "Vs (G \<lbrakk>connected_component G y - {y}\<rbrakk>) = connected_component G y - {y}"
    using component_is_M_vs 
    by (simp add: graph_inter_Vs_subset(1) matching_confined_in_component perfect_matchingD(3)
        perfect_matching_if_projected_to_matched_verts)
  moreover have "even (card (Vs (G \<lbrakk>connected_component G y - {y}\<rbrakk>)))"
   by(auto intro!: perfect_matching_even_graph[OF perfect_M]
         simp add: assms(3) dblton_graph_Vs_inter)
  ultimately have "even (card (connected_component G y - {y}))" 
    by simp
  moreover have "card (connected_component G y - {y}) +1 = card (connected_component G y)"
    using assms(3)  card_Suc_Diff1[of "connected_component G y" y] 
          in_connected_componentI2[of y y G] component_is_finite[of G y]
    by auto
  ultimately show ?thesis
    by presburger
qed

lemma component_Delta_empty:  
  "Delta G (connected_component G y) = {}"
  using ex_in_conv[of "Delta G (connected_component G y)"] connected_components_member_eq[of _ G y]
       vertices_edges_in_same_component[of _ _ G]
  by(auto elim!: in_DeltaE)

lemma even_number_of_matching_verts:
  "\<lbrakk>matching M; dblton_graph M\<rbrakk> \<Longrightarrow> even ( card (Vs M))"
  using  dvd_def[of "2" "2 * card M"] matching_vertices_double_size[of M]
  by fastforce

lemma odd_component_not_all_matched:
  assumes "graph_invar G" "graph_matching G M"
        "y \<in> Vs G" "odd (card (connected_component G y))"
    shows "\<not> connected_component G y \<subseteq> Vs M"
proof(rule notI, goal_cases)
  case 1
  have "connected_component G y \<subseteq> Vs G"
    by (simp add: assms(3) connected_component_subset)
  have Delta_empty:  "Delta G (connected_component G y) = {}" 
    by (simp add: component_Delta_empty)
  hence M_delta_empty: "Delta M (connected_component G y) = {}"
    using Delta_set_mp assms(2) by blast
  hence "card (connected_component G y - Vs {uu \<in> M. uu \<subseteq> connected_component G y}) = 0"
    using assms(1,2)  graph_invar_subset
    by(subst unmatcheds_in_set_delta_card[OF _ 1]) auto
  hence "(connected_component G y - Vs {uu \<in> M. uu \<subseteq> connected_component G y}) = {}"
    by (simp add: assms(1) component_is_finite)
  hence "connected_component G y = Vs {uu \<in> M. uu \<subseteq> connected_component G y}"
    by (auto simp add: vs_member)
  moreover have "even (card (Vs {uu \<in> M. uu \<subseteq> connected_component G y}))"
    using assms(1,2) 
    by(auto intro!: even_number_of_matching_verts intro: matching_subgraph)
  ultimately show False
    using assms(4) by auto
qed

lemma factor_critical_is_whole_component:
  assumes "\<And> x. x \<in> X \<Longrightarrow> \<exists> M. graph_matching (G \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x}"
          "y \<in> X" "Delta G X = {}" "graph_invar G"
    shows "connected_component G y = X"
proof(rule ccontr, goal_cases)
  case 1
  have ys_component_in_X: "connected_component G y \<subseteq> X"
    by (simp add: assms(2,3,4) empty_delta_component_confined)
  then obtain x where x: "x \<in> X" "x \<notin> connected_component G y"
    using assms(2) 1 by auto
  note components_odd = component_of_factor_critical_odd[OF assms(1) _ assms(4), simplified]
  obtain M where M: "graph_matching (G \<lbrakk>X\<rbrakk>) M" "Vs M = X - {x}"
    using x(1) assms(1) by force
  note odd_y_comp = components_odd[OF ys_component_in_X]
  have y_in_G:"y \<in> Vs G" 
  proof-
    have "y \<in> Vs M"
      using M(2) assms(2) in_own_connected_component x(2) by fastforce
    moreover have "Vs M \<subseteq> Vs G"
      using M(1) graph_inter_Vs_subset(1)[of G X] Vs_subset[of M G]
      by auto
    ultimately show ?thesis
      by auto
  qed
  have "\<not> connected_component G y \<subseteq> Vs M"
    using assms(4) M(1) in_graph_inter_VsD(1)[of _ G X] y_in_G odd_y_comp
    by(intro odd_component_not_all_matched) auto
  then obtain y' where y': "y' \<in> connected_component G y" "y' \<notin> Vs M"
    by auto
  moreover hence "y' \<in> X"
    using ys_component_in_X by blast
  moreover have "y' \<noteq> x" 
    using x(2) y'(1) by blast
  ultimately show False 
    using M(2) by blast
qed

lemma factor_critical_is_odd:
  assumes "\<And> x. x \<in> X \<Longrightarrow> \<exists> M. graph_matching (G \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x}"
          "y \<in> X" "Delta G X = {}" "graph_invar G"
        shows "odd (card X)"
  using factor_critical_is_whole_component[OF assms, simplified]
        component_of_factor_critical_odd[OF assms(1) _ assms(4), simplified]
  by auto

lemma factor_critical_is_component_and_odd:
  assumes "\<And> x. x \<in> X \<Longrightarrow> \<exists> M. graph_matching (G \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x}"
          "y \<in> X" "Delta G X = {}" "graph_invar G"
        shows "connected_component G y = X \<and> odd (card X)" 
  using factor_critical_is_whole_component[OF assms, simplified]
        component_of_factor_critical_odd[OF assms(1) _ assms(4), simplified]
  by auto

lemma graph_diff_alias: "graph_diff G A = G \<setminus> A"
  by(auto simp add: graph_diff_def remove_vertices_graph_def)

lemma in_remove_vertices_graphE: 
  "\<lbrakk>e \<in> G \<setminus> X; \<lbrakk>e \<in> G; e \<inter> X = {}\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp add: remove_vertices_graph_def)

lemma walk_betw_remove_verts:
  "\<lbrakk>walk_betw G u p v; set p\<inter> X = {}; length p \<ge> 2\<rbrakk> \<Longrightarrow> walk_betw (G \<setminus> X) u p v"
  by(rule walk_betw_strengthen)
    (auto intro!: in_remove_verticesI 
           intro: path_ball_edges[OF walk_between_nonempty_pathD(1)]
            dest: v_in_edge_in_path_gen)

lemma connected_component_same_if_indep_of_removeds:
  "connected_component G x \<inter> X = {} 
    \<Longrightarrow> connected_component (G \<setminus> X) x = connected_component G x"
proof(rule, all \<open>rule\<close>, goal_cases)
  case (1 y)
  then show ?case 
    using remove_vertices_subgraph[of G X] con_comp_subset[of "G \<setminus> X" G x]
    by auto
next
  case (2 y)
  then show ?case 
  proof(elim in_connected_componentE, goal_cases)
    case 1
    then show ?case 
    proof(elim reachableE, goal_cases)
      case (1 p)
      thus ?case
      proof(cases "x = y", goal_cases)
        case 1
        then show ?case
          by (simp add: in_connected_componentI2)
      next
        case 2
      hence "set p \<inter> X = {}"
        by (simp add: disjoint_iff vertices_path_in_component)
      hence "walk_betw (G \<setminus> X) x p y"
        using 2
        by(auto intro!: walk_betw_remove_verts simp add: walk_betw_length)
      hence "reachable (G \<setminus> X) x y"
        by (simp add: reachableI)
      then show ?case 
        by (simp add: in_connected_componentI)
    qed
  qed
  next
    case 2
    then show ?case 
      by (simp add: in_own_connected_component)
  qed
qed

lemma remove_irrelevants_graph_inter_Vs:
  "A \<inter> D = {} \<Longrightarrow> (G \<setminus> A) \<lbrakk>D\<rbrakk> = G \<lbrakk>D\<rbrakk>"
  by(auto simp add: remove_vertices_graph_def graph_inter_Vs_def)

lemma matched_vertex_not_in_Vs_of_graph_inter_Vs:
  assumes "matching M" "e \<in> M" "x \<in> e" "\<not> e \<subseteq> X"
  shows "x \<notin> Vs (M\<lbrakk>X\<rbrakk>)"
  using assms
  by (auto elim!: in_graph_inter_VsE 
        simp add: vs_member 
            dest: matching_unique_match)

lemma select_unique_representative_same_card_and_bijection:
  assumes "\<And> XX. XX \<in> \<X> \<Longrightarrow> \<exists>! x \<in> X. x \<in> XX"
          "\<And> x. x \<in> X \<Longrightarrow> \<exists>! XX \<in> \<X>. x \<in> XX"
          "finite X" "finite \<X>"
    shows "card X = card \<X> \<and> (\<exists> f. bij_betw f X \<X>)"
proof-
  define f1 where "f1 = (\<lambda> x. SOME XX. XX \<in> \<X> \<and> x \<in> XX)"
  have f1_props: "inj_on f1 X \<and> f1 ` X \<subseteq> \<X>"
    proof(rule, all \<open>(rule inj_onI) | (rule, elim imageE)\<close>, goal_cases)
      case (1 x y)
      then show ?case
        using someI_ex[of "\<lambda>uub. uub \<in> \<X> \<and> y \<in> uub"] someI_ex[of "\<lambda>uub. uub \<in> \<X> \<and> x \<in> uub"] 
              assms(1,2) 
        by (force simp add: f1_def)
    next
      case (2 XX x)
      then show ?case 
        using  assms(2)[of x]  verit_sko_ex'[of "\<lambda>uub. uub \<in> \<X> \<and> x \<in> uub"
            "(SOME uub. uub \<in> \<X> \<and> x \<in> uub) \<in> \<X> \<and> x \<in> (SOME uub. uub \<in> \<X> \<and> x \<in> uub)"]
        by(auto simp add: f1_def)
    qed

    have card1:  "card X \<le> card \<X>"
      using card_inj_on_le[where f = f1, OF _ _ assms(4)] f1_props 
      by simp
    define f2 where "f2 = (\<lambda> XX. SOME x. x \<in> X \<and> x \<in> XX)"
    have f2_props:"inj_on f2 \<X> \<and> f2 ` \<X> \<subseteq> X"
    proof(rule, all \<open>(rule inj_onI) | (rule, elim imageE)\<close>, goal_cases)
      case (1 XX YY)
      thus ?case
        by (metis (lifting) assms(1,2) f2_def someI_ex)
    next
      case (2 x XX)
      then show ?case 
        using  assms(1)[of XX] someI_ex[of "\<lambda>R. R \<in> X \<and> R \<in> XX"]
        by(auto simp add: f2_def)
    qed
    have card2: "card X \<ge> card \<X>"
      using card_inj_on_le[where f = f2, OF _ _ assms(3)] f2_props
      by auto
    obtain f where "bij_betw f X \<X>"
      using Schroeder_Bernstein[of f1 X \<X> f2] f1_props f2_props 
      by auto
    thus ?thesis 
      using card1 card2 
      by auto
qed

lemma edmonds_gallai_on_matching_props:
  assumes "graph_invar G" "max_card_matching G M" "edmonds_gallai G M \<D> A"
  shows "odd_comps_in_diff G A = \<D>" (is ?thesis_odd_comps)
        "A = Neighbourhood G (\<Union> \<D>)" (is ?neighbourhood_thesis)
        "\<And> X x. \<lbrakk>X \<in> \<D>; x \<in> X\<rbrakk> \<Longrightarrow> \<exists> M. graph_matching (G \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x}"
        "\<And> X. X \<in> \<D> \<Longrightarrow> \<exists> x. x \<in> X \<and> Vs (M\<lbrakk>X\<rbrakk>) = X - {x}"
        "perfect_matching (G \<setminus> (\<Union> \<D> \<union> A)) (M \<setminus> (\<Union> \<D> \<union> A))" (is ?thesis_perfect)
        "\<And> X. \<lbrakk>X \<subseteq> A; X \<noteq> {}\<rbrakk> \<Longrightarrow> card X \<le> card {D | D . D \<in> \<D> \<and> X \<longleftrightarrow>\<^bsub>G\<^esub> D}"
        "\<And> X. \<lbrakk>X \<subseteq> A; X \<noteq> {}; card X = card {D |D. D \<in> \<D> \<and> X \<longleftrightarrow>\<^bsub>G\<^esub> D}\<rbrakk> 
          \<Longrightarrow> X \<union>  \<Union> {D |D. D \<in> \<D> \<and> X \<longleftrightarrow>\<^bsub>G\<^esub> D} \<subseteq> Vs M"
        "\<exists> m. inj_on m A \<and> m ` A \<subseteq> \<Union> \<D> \<and> (\<forall> x \<in> A. {x, m x} \<in> M)
              \<and> (\<forall> x y. x \<in> A \<and> y \<in> A \<and> x \<noteq> y \<longrightarrow>
                     (\<exists> D1 D2. D1 \<in> \<D> \<and> D2 \<in> \<D> \<and> D1 \<noteq> D2  \<and> (m x) \<in> D1 \<and> (m y) \<in> D2))"
          (is ?thesis_distinct_match)
        "2 * card M + (int (card \<D>) - int (card A)) = card (Vs G)" (is ?thesis_berge_formula)
        "\<And> e. \<lbrakk>e \<in> M; 
               e \<subseteq> Vs G - \<Union> \<D> - A \<Longrightarrow> P;
               \<And> x y D. \<lbrakk> e = {x, y}; x \<in> A; y \<in> D; D \<in> \<D>; x \<noteq> y\<rbrakk> \<Longrightarrow> P;
               \<And> D. \<lbrakk>D \<in> \<D>; e \<subseteq> D\<rbrakk> \<Longrightarrow> P\<rbrakk>
               \<Longrightarrow> P"
        "\<Union> \<D> = inessentials G"
        "\<exists> m. inj_on m (Vs G - Vs M) \<and> m ` (Vs G - Vs M) \<subseteq> \<D>"
        "\<And> e. \<lbrakk>e \<in> G; 
               e \<subseteq> Vs G - \<Union> \<D> - A \<Longrightarrow> P;
               e \<subseteq> A \<Longrightarrow> P;
               \<And> x y D. \<lbrakk> e = {x, y}; x \<in> A; y \<in> D; D \<in> \<D>; x \<noteq> y\<rbrakk> \<Longrightarrow> P;
               \<And> x y. \<lbrakk> e = {x, y}; x \<in> A; y \<in> Vs G - \<Union> \<D> - A; x \<noteq> y\<rbrakk> \<Longrightarrow> P;
               \<And> D. \<lbrakk>D \<in> \<D>; e \<subseteq> D\<rbrakk> \<Longrightarrow> P\<rbrakk>
               \<Longrightarrow> P"
proof-
  note edmonds_gallaiD = edmonds_gallaiD[OF assms(3)]
  show first_theses: ?neighbourhood_thesis
        "\<And> X x. \<lbrakk>X \<in> \<D>; x \<in> X\<rbrakk> \<Longrightarrow> \<exists> M. graph_matching (G \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x}"
        "\<And> X. X \<in> \<D> \<Longrightarrow> \<exists> x. x \<in> X \<and> Vs (M\<lbrakk>X\<rbrakk>) = X - {x}"
    using edmonds_gallaiD by auto

  have A_in_G:"A \<subseteq> Vs G" 
    by (simp add: Neighbourhood_in_G first_theses(1))
  have unconnected_sides: "Vs G - A - \<Union> \<D> \<leftarrow>|\<rightarrow>\<^bsub>G\<^esub> \<Union> \<D>" 
    by(auto elim!: not_in_NeighbourhoodE 
         simp add: first_theses(1) connected_set_of_vertices_def doubleton_eq_iff  insert_commute)
  hence unconnected_sides_A_removed: "Vs G - A - \<Union> \<D> \<leftarrow>|\<rightarrow>\<^bsub>G \<setminus> A\<^esub> \<Union> \<D>" 
    using  un_connected_sets_of_certices_anti_mono[OF _ remove_vertices_subgraph] by force
  have unconnected_D: "D \<in> \<D> \<Longrightarrow> Vs G - A - D \<leftarrow>|\<rightarrow>\<^bsub>G\<^esub> D" for D
  proof(rule ccontr, goal_cases)
    case 1
    then obtain u v where uv: "{u, v} \<in> G" "u \<in> Vs G" "u \<notin> D" "v \<in> D"
      by(auto simp add: connected_set_of_vertices_def)
    then obtain D' where D': "D' \<in> \<D>" "u \<in> D'"
      using edmonds_gallaiD(5)[of _ D] 1
      by(force elim!: not_in_NeighbourhoodE  
           simp add: connected_set_of_vertices_def first_theses(1) insert_commute)
    thus False
      using "1"(1) edmonds_gallaiD(5) uv(1,3,4)
      by(auto simp add:  connected_set_of_vertices_def)
  qed
  hence unconnected_D_A_removed: "D \<in> \<D> \<Longrightarrow> Vs G - A - D \<leftarrow>|\<rightarrow>\<^bsub>G \<setminus> A\<^esub> D" for D
    using  un_connected_sets_of_certices_anti_mono[OF _ remove_vertices_subgraph] by force
    have Vs1: "Vs (G \<setminus> A) \<subseteq> Vs G - A \<union> (Vs G - A - \<Union> \<D>)" 
     using remove_vertices_not_vs[of _ A G] remove_vertices_subgraph_Vs[of _ G A]
     by auto
   have Vs2:"Vs (G \<setminus> A) \<subseteq> Vs G - A - \<Union> \<D> \<union> \<Union> \<D>"
     using Vs1 by auto
   have Vs3: "Vs(G \<setminus> A) \<subseteq> Vs G  -A"
     using Vs1 by auto
   have D_delta_A_removed_empty: "D \<in> \<D> \<Longrightarrow> Delta (G \<setminus> A) D = {}" for D 
   proof(rule ccontr, goal_cases)
     case 1
     then obtain u v where "{u, v} \<in> G \<setminus> A" "u \<in> D" "v \<notin> D"
       by (auto elim!: in_DeltaE)
     thus ?case 
       using Vs3 doubleton_eq_iff[of u v v u]  unconnected_D_A_removed[OF 1(1)]
         connected_set_of_vertices_def[of "Vs G - A - D" "G \<setminus> A" D]
         edges_are_Vs_2[of u v "G \<setminus> A"]
       by auto
   qed
   have a_comp_in_remainings_or_in_some_D:
    "X \<in> comps (Vs G - A) (G \<setminus> A) \<Longrightarrow> X \<subseteq> Vs G - A - \<Union> \<D> \<or> (\<exists> X'. X' \<in> \<D> \<and> X \<subseteq> X')" for X
  proof(cases "X \<subseteq> Vs G - A - \<Union> \<D>", goal_cases)
    case 2
    then obtain x where x: "x \<in> X" "x \<notin>  Vs G - A - \<Union> \<D>"
      by auto
    obtain x' where x': "x' \<in> Vs G - A" "X = connected_component (G \<setminus> A) x'"
      using 2 by(auto simp add: comps_def)
    have X_in_G: "X \<subseteq> Vs G" 
      using x'(1,2)remove_vertices_subgraph_Vs[of _ G A] in_connected_component_in_edges[of _ "G \<setminus> A" x']
      by fastforce
    then obtain D where D: "D \<in> \<D>" "x \<in> D" 
      using x(1,2) x'(1,2) remove_vertices_not_vs[of x A G] DiffI[of x "Vs G" A]
        in_connected_component_in_edges[of x "G \<setminus> A" x']
      by auto
    have X_in_D: "X \<subseteq> \<Union> \<D>"
    proof(rule ccontr, goal_cases)
      case 1
      then obtain y where "y \<in> X" "y \<in> Vs G - A - \<Union> \<D>"
        using 2(1) remove_vertices_not_vs[of _ A G] remove_vertices_subgraph_Vs[of _ G A]
          in_connected_component_in_edges[of _ "G \<setminus> A"] 
        by(fastforce simp add: comps_def)
      then show ?case 
        using x'(2)  D(1,2) x(1) Vs2 unconnected_sides_A_removed
         by(intro two_unconnected_sets_connected_component_not_inter_both[
                                                   of "G \<setminus> A" x' "Vs G - A - \<Union> \<D>" "\<Union> \<D>"])
            auto
     qed
     then obtain D x'' where D: "D \<in> \<D>" "X \<inter> D \<noteq> {}" "x'' \<in> X" "x'' \<in> D"
       using D(1,2) x(1) by auto
     moreover have "X \<subseteq> D"
     proof(rule ccontr, goal_cases)
       case 1
       then obtain D' y' where "D' \<in> \<D>" "y' \<in> D'" "D' \<noteq> D" "y' \<in> X"
         using X_in_D by force
       show ?case
       proof(rule two_unconnected_sets_connected_component_not_inter_both[of 
                    "G \<setminus> A" x' D "Vs (G \<setminus> A) - D"], goal_cases)
         case 1
         then show ?case 
           using calculation(2) x'(2) by auto
       next
         case 2
         then show ?case 
           by (metis "1" Int_Diff calculation(3,4) connected_component_subset diff_shunt_var in_connected_componentE
               inf.order_iff subsetI x'(2))
       next
         case 3
         then show ?case 
           by simp
       next
         case 4
         then show ?case 
           by simp
       next
         case 5
         hence "D \<leftarrow>|\<rightarrow>\<^bsub>G \<setminus> A\<^esub> Vs G - A - D"
           using unconnected_D_A_removed[of D] calculation(1) 
           by(auto simp add: connected_sym)
         then show ?case 
           using Vs3 connected_sets_of_certices_mono[OF _ subset_refl] Diff_mono by fastforce
       qed
     qed
     ultimately show ?case 
       by auto
   qed auto

   have dblton_M:"dblton_graph M" 
     using assms(1,2) max_card_matchingDs(1) by fastforce

   have x_in_G_without_a_without_D_in_M_Vs: 
     "x \<in> Vs G - A- \<Union> \<D> \<Longrightarrow> x \<in> Vs (M \<setminus> \<Union> \<D> \<union> A)" for x
   proof(goal_cases)
     case 1
     note one = this
      then obtain e' where e': "e' \<in> M" "x \<in> e'" "x \<notin> A" "x \<notin> \<Union> \<D>"
         using edmonds_gallaiD(11) subsetD[of "Vs G - \<Union> \<D>" "Vs M" x]
         by (auto simp add: vs_member)
       moreover have "e' \<in> M \<setminus> \<Union> \<D> \<union> A"
       proof(rule in_remove_verticesI[OF e'(1)], rule ccontr, goal_cases)
         case 1
         obtain y where "e' = {x, y}" "x \<noteq> y" 
           using dblton_M e'(1,2) by blast
         then obtain x y where  "e' = {x, y}" "x \<noteq> y" "x \<in> (\<Union> \<D> \<union> A)" "y \<notin> (\<Union> \<D> \<union> A)"
           using "1" first_theses(1)  e'(4,3)
           by(auto simp add: doubleton_eq_iff) 
         hence "e' \<in> Delta M (\<Union> \<D> \<union> A)" 
           using e'(1)
           by(auto intro!: in_DeltaI[of "{x, y}" x y])
         thus False
           by (simp add: local.edmonds_gallaiD(9))
       qed
       ultimately show ?case
         by auto
     qed

   have Vs_G_without_D_A_is_Vs_M:  "Vs (G \<setminus> \<Union> \<D> \<union> A) = Vs (M \<setminus> \<Union> \<D> \<union> A)"
    proof(rule, all \<open>rule, elim vs_member_elim in_remove_vertices_graphE\<close>, goal_cases)
       case (1 x e)
       note one = this
       thus ?case
         using  vs_member_intro[of x e G] x_in_G_without_a_without_D_in_M_Vs[of x]
         by auto
     next
       case (2 x e)
       then show ?case 
         using assms(2)
         by(auto intro: in_remove_vertices_vsI dest!: max_card_matchingD)
     qed

   show perfect_on_remainder: "perfect_matching (G \<setminus> (\<Union> \<D> \<union> A)) (M \<setminus> (\<Union> \<D> \<union> A))"
   proof(rule perfect_matchingI, goal_cases)
     case 1
     then show ?case 
       using assms(2)
       by(auto dest: max_card_matchingDs(1) remove_vertices_mono)
   next
     case 2
     then show ?case
       using assms(2)
       by(auto dest: matching_remove_vertices max_card_matchingD)
   next
     case 3
     then show ?case 
       using Vs_G_without_D_A_is_Vs_M by simp
   qed

   have x_in_G_without_a_without_D_in_G_Vs: 
     "x \<in> Vs G - A- \<Union> \<D> \<Longrightarrow> x \<in> Vs (G \<setminus> \<Union> \<D> \<union> A)" for x
     using Vs_G_without_D_A_is_Vs_M x_in_G_without_a_without_D_in_M_Vs by presburger

   have other_component_is_even:
      "connected_component (G \<setminus> A) x \<subseteq> Vs G - A- \<Union> \<D>
          \<Longrightarrow> even (card ( connected_component (G \<setminus> A) x))"
     for x
   proof(goal_cases)
     case 1
     have same_comp:"connected_component (G \<setminus> A) x = connected_component (G \<setminus>  \<Union> \<D> \<union> A) x"
       using 1
       by(subst connected_component_same_if_indep_of_removeds[of "G \<setminus> A" x "\<Union> \<D>", symmetric])
         (auto simp add: remove_remove_union sup_commute)
     show ?case 
       unfolding same_comp
       using perfect_on_remainder 1 in_own_connected_component[of x "G \<setminus> A"]
       by(intro perfect_matching_component_even)
         (auto intro!: x_in_G_without_a_without_D_in_G_Vs 
             simp add: assms(1) graph_invar_remove_vertices)
   qed

   have X_in_D_inter_A_empty: "X \<in> \<D> \<Longrightarrow> X \<inter> A = {}"  for X
     using self_not_in_Neighbourhood[of _ "\<Union> \<D>" G]
     by(auto simp add:  first_theses(1))
 
  show ?thesis_odd_comps
    unfolding odd_comps_in_diff_def
  proof(rule, all \<open>rule\<close>, goal_cases)
    case (1 X)
    then obtain x where x: "x \<in> Vs G - A" "X = connected_component (G \<setminus> A) x" "odd (card X)"
     using  graph_diff_subset[of G A] Vs_subset[of "G \<setminus> A" G] remove_vertices_not_vs[of _ A G]
            connected_components_notE_singletons[of _ "G \<setminus> A"]
     by (fastforce simp add: odd_components_def singl_in_diff_def odd_component_def graph_diff_alias) 
   obtain D where D: "D \<in> \<D>" "connected_component (G \<setminus> A) x \<subseteq> D"
     using a_comp_in_remainings_or_in_some_D[of X] other_component_is_even[of x] x(2) x
     by(auto simp add: comps_def)
   moreover have "X = D"
     unfolding x(2)
   proof(rule factor_critical_is_whole_component, goal_cases)
     case (1 x)
     then show ?case
       using X_in_D_inter_A_empty D(1)first_theses(2)
       by(subst remove_irrelevants_graph_inter_Vs) auto
   next
     case 2
     then show ?case 
       using D(2) in_own_connected_component by force
   next
     case 3
     then show ?case 
       using D_delta_A_removed_empty D(1) by auto
   qed (simp add: assms(1) graph_invar_remove_vertices)
   ultimately show ?case 
     by simp
  next
    case (2 X)
    then obtain x where x: "x \<in> X"
      using local.edmonds_gallaiD(3) by auto
    have "connected_component (G \<setminus> A) x = X \<and> odd (card X)"
    proof(rule factor_critical_is_component_and_odd[of X "G \<setminus> A" x], goal_cases)
      case 1
       then show ?case
       using X_in_D_inter_A_empty x first_theses(2) 2
       by(subst remove_irrelevants_graph_inter_Vs) auto
   next
     case 2
     then show ?case 
       using x in_own_connected_component by force
   next
     case 3
     then show ?case 
       using D_delta_A_removed_empty 2 by auto
   qed (simp add: assms(1) graph_invar_remove_vertices)
   moreover have "x \<in> Vs (G \<setminus> A) \<or> (x \<in> Vs G \<and> x \<notin> A \<and> x \<notin> Vs (G \<setminus> A))"
     using "2" local.edmonds_gallaiD(2) x X_in_D_inter_A_empty by auto
   moreover have "\<lbrakk>x \<in> Vs G; x \<notin> A; x \<notin> Vs (G \<setminus> A)\<rbrakk> \<Longrightarrow> X = {x}"
     using calculation(1) by(auto intro!: connected_components_notE_singletons)
   ultimately show ?case
     by(auto simp add: graph_diff_alias odd_components_def odd_component_def singl_in_diff_def)
 qed

  define m where "m = (\<lambda> x. (SOME y. {x, y} \<in> M))"

  have matching_Neighbourhood_A_in_D:"Neighbourhood M A \<subseteq> \<Union> \<D>"
  proof(rule, elim  in_NeighbourhoodE, goal_cases)
    case (1 x y)
    then show ?case 
      using edmonds_gallaiD(9)  in_DeltaI[of "{_, _}" _ _ M "\<Union> \<D> \<union> A"]
      by blast
  qed
  have no_matching_in_A: "\<lbrakk>e \<in> M; e \<subseteq> A\<rbrakk> \<Longrightarrow> False" for e 
    using assms(2) edmonds_gallaiD(12)
      max_card_matching_subgraphD[of G M e] in_graph_inter_VsI[of e G A]
    by auto

  have m_on_A: "\<lbrakk>x \<in> A; y = m x\<rbrakk> \<Longrightarrow> {x, y} \<in> M \<and> y \<in> \<Union> \<D> \<and> y \<notin> A \<and> x \<notin> \<Union> \<D>" for x y
  proof(goal_cases)
    case 1
    hence x_in_M:"x \<in> Vs M" 
      using  A_in_G edmonds_gallaiD(11) self_not_in_Neighbourhood[of x "\<Union> \<D>" G] 
             subsetD[of "Vs G - \<Union> \<D>" "Vs M" x]
      by (auto simp add:  first_theses(1))
    then obtain e where e:"x \<in> e" "e \<in> M" 
      by (auto simp add: vs_member)
    then obtain y' where y': "e = {x, y'}" "x \<noteq> y'"
      using dblton_M by blast
    hence e':"{x, m x} \<in> M"  
      using e(2) someI[of "\<lambda> y. {x, y} \<in> M" ] by(auto simp add: m_def)
    hence y_is_y': "y = y'" 
      using "1"(2) assms(2)  e(2) max_card_matchingDs(2) y'(1)
      by(auto intro!: doubleton_in_matching(1))
    moreover have "y \<in> \<Union> \<D>" "y \<notin> A"
      using "1"(1) e(2) in_NeighbourhoodI matching_Neighbourhood_A_in_D no_matching_in_A y'(1) y_is_y'
      by fastforce+
    moreover have "x \<notin> \<Union> \<D>" 
      using "1"(1) X_in_D_inter_A_empty by auto
    ultimately show ?case
      using e(2) y'(1) by auto
  qed

  have m_on_obtain_Ds:
     "\<lbrakk>x \<in> A; y \<in> A; x \<noteq> y\<rbrakk> \<Longrightarrow> 
        \<exists>D1 D2. D1 \<in> \<D> \<and> D2 \<in> \<D> \<and> D1 \<noteq> D2 \<and> m x \<in> D1 \<and> m y \<in> D2" for x y
  proof(goal_cases)
    case 1
    note one = this
    then obtain D1 D2 where D1D2: "D1 \<in> \<D>" "D2 \<in> \<D>" "m x \<in> D1" "m y \<in> D2"
          "{x, m x} \<in> M" "{y, m y} \<in> M" "x \<notin> D1"  "x \<notin> D2" "y \<notin> D1" "y \<notin> D2"
      using m_on_A[of x "m x"] m_on_A[of y "m y"] by auto
    note near_perfects = first_theses(3)[OF D1D2(1)] first_theses(3)[OF D1D2(2)]
    have "D1 \<noteq> D2"
    proof(rule notI, goal_cases)
      case 1
      have "m x \<notin> Vs ( M \<lbrakk>D1\<rbrakk>)"
        using assms(2) D1D2(5,7)
        by(intro matched_vertex_not_in_Vs_of_graph_inter_Vs[of M "{x, m x}"])
          (auto dest: max_card_matchingDs(2))
      moreover have "m y \<notin> Vs ( M \<lbrakk>D2\<rbrakk>)"
        using assms(2) D1D2(6,10)
        by(intro matched_vertex_not_in_Vs_of_graph_inter_Vs[of M "{y, m y}"])
          (auto dest: max_card_matchingDs(2))
      ultimately have "m x = m y"
        using "1" D1D2(3,4) near_perfects(2) by blast
      moreover hence "{x, m x} = {y, m y}"
        using D1D2(5,6) assms(2) 
        by(intro matching_unique_match[of M "m x"])
          (auto dest: max_card_matchingD)
      ultimately have "x = y"
        by(auto simp add: doubleton_eq_iff)
      thus False
        using one(3) by simp
    qed
    thus ?case
      using D1D2(1,2,3,4) by blast
  qed

  have m_inj_on_A: "inj_on m A"
  proof(rule inj_onI, rule ccontr, goal_cases)
    case (1 x y)
    obtain D1 D2 where "D1 \<in> \<D>" "D2 \<in> \<D>" "D1 \<noteq> D2" "m x \<in> D1" "m y \<in> D2"
      using m_on_obtain_Ds[OF 1(1,2)] 1 by auto
    moreover have "D1 \<inter> D2 = {}" 
      using calculation(1,2,3) disjointD local.edmonds_gallaiD(1) by blast
    ultimately have "m x \<noteq> m y" 
      by auto
    thus False
      using 1 by auto
  qed

  have m_image_in_D: "m ` A \<subseteq> \<Union> \<D>"  and  m_in_matching: "x\<in>A \<Longrightarrow> {x, m x} \<in> M" for x
    using  m_on_A by auto

  show ?thesis_distinct_match 
    using m_image_in_D m_in_matching m_on_obtain_Ds
    by(auto intro!: exI[of _ m] simp add: m_inj_on_A)

  show graph_edge_cases:
    "\<And> e. \<lbrakk>e \<in> G;
     e \<subseteq> Vs G - \<Union> \<D> - A \<Longrightarrow> P;
     e \<subseteq> A \<Longrightarrow> P; 
     \<And> x y D. \<lbrakk> e = {x, y}; x \<in> A; y \<in> D; D \<in> \<D>; x \<noteq> y\<rbrakk> \<Longrightarrow> P;
     \<And> x y. \<lbrakk> e = {x, y}; x \<in> A; y \<in> Vs G - \<Union> \<D> - A; x \<noteq> y\<rbrakk> \<Longrightarrow> P;
     \<And> D. \<lbrakk>D \<in> \<D>; e \<subseteq> D\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  proof(goal_cases)
    case (1 e)
    then show ?case 
    proof(cases "e \<subseteq> Vs G - \<Union> \<D> - A", goal_cases)
      case 1
      then show ?case 
        by simp
    next
      case 2
      then obtain x y where xy: "e = {x, y}" "x \<noteq> y" 
        using assms(1) by(auto elim!: dblton_graphE)
      then show ?case
        using 2
      proof(cases "e \<inter> A \<noteq> {}", goal_cases)
        case 1
        thus ?case
        proof(cases "e \<subseteq> A", goal_cases)
          case 1
          thus ?case
            by simp
        next
          case 2
          then obtain x y where xy: "e = {x, y}" "x \<noteq> y"  "x \<in> A"
            by auto
          hence "y \<in> \<Union> \<D> \<or> y \<in> Vs G - \<Union> \<D> - A"
            using "2"(11,3) by blast
          thus ?case
            using 2 xy
          proof(elim disjE, goal_cases)
            case 1
            then obtain D where "D \<in> \<D>" "y \<in> D" 
              by auto
            thus ?case 
              using xy by(auto intro!: 1(6)[of x y D])
          next
            case 2
            thus ?case 
              by presburger
          qed
        qed
      next
        case 2
        then obtain x y where xy: "e = {x, y}" "x \<noteq> y" 
          using assms(1) by(auto elim!: dblton_graphE)
        thus ?case
          using 2
        proof(cases "e \<inter> Vs G - \<Union> \<D> - A = {}", goal_cases)
          case 1
          have "e \<subseteq> \<Union> \<D>"
            using "1"(13) "2"(10,3) by auto
          then obtain D1 D2 where D1D2: "D1 \<in> \<D>"  "D2 \<in> \<D>" "x \<in> D1"  "y \<in> D2" 
            using xy(1) by auto
          have "D1 = D2" 
          proof(rule ccontr, goal_cases)
            case 1
            have "e \<in> G" 
              using "2"(3) assms(2) max_card_matching_subgraphD by auto
            hence "D1 \<longleftrightarrow>\<^bsub>G\<^esub> D2"
              using D1D2(3,4) connected_set_of_vertices_def xy(1) by blast
            then show ?case 
              by (simp add: "1" D1D2(1,2) edmonds_gallaiD(5))
          qed
          then show ?case 
            using "2"(8) D1D2(2,3,4) xy(1) by blast
        next
          case 2
          obtain x y where xy: "e = {x, y}" "x \<noteq> y" "x \<in> Vs G - \<Union> \<D> - A"  "y \<notin> Vs G - \<Union> \<D> - A"
            using "2"(11,13) xy(1) by blast
          hence "y \<in> \<Union> \<D>"
            using "2"(12,5)  edges_are_Vs_2 [of x y] by auto
          hence "x \<in> A" 
            using "2"(5) xy(1,3)
            by(auto simp add: first_theses(1) insert_commute intro: in_NeighbourhoodI[of y x G])
          hence False 
            using xy(3) by blast
          then show ?case 
            by simp
        qed
      qed
    qed
  qed

  show matching_edge_cases:
    "\<lbrakk>e \<in> M; e \<subseteq> Vs G - \<Union> \<D> - A \<Longrightarrow> P;
      \<And> x y D. \<lbrakk> e = {x, y}; x \<in> A; y \<in> D; D \<in> \<D>; x \<noteq> y\<rbrakk> \<Longrightarrow> P;
     \<And> D. \<lbrakk>D \<in> \<D>; e \<subseteq> D\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" for e
  proof(goal_cases)
    case 1
    note one = this
    hence "e \<in> G" 
      using assms(2) by(auto simp add: max_card_matching_subgraphD)
    thus ?case
    proof(elim graph_edge_cases, goal_cases)
      case 2
      hence False 
        using no_matching_in_A one(1) by auto
      then show ?case
        by simp
    next
      case (4 x y)
      hence False 
        using in_NeighbourhoodI[of x y M] matching_Neighbourhood_A_in_D one(1)
        by auto
      then show ?case 
        by simp
    qed (auto intro: one)
  qed
  
  define mD where "mD = (\<lambda> x. SOME D. D \<in> \<D> \<and> m x \<in> D \<and> x \<notin> D)"

  have mD_props: "x \<in> A \<Longrightarrow> mD x \<in> \<D> \<and> m x \<in> mD x \<and> x \<notin> mD x" for x
  proof( goal_cases)
    case 1
    obtain D where "D \<in> \<D>" "m x \<in> D" "x \<notin> D" 
      using  "1" m_on_A by force
    thus ?case 
      using someI[of "\<lambda> D. D \<in> \<D> \<and> m x \<in> D \<and> x \<notin> D"] 
      by(auto simp add: mD_def)
  qed

  have mD_image_in_D: "mD ` A \<subseteq> \<D>"
    using mD_props by force

  have Delta_M_D_unique:
    "\<lbrakk>e \<in> Delta M X; e' \<in> Delta M X; X \<in> \<D>\<rbrakk> \<Longrightarrow> e = e'" for e e' X
    using assms(1,2) Delta_finite[of M X]
       finite_Vs_then_finite[of M] edmonds_gallaiD(10)[of X]
      max_card_matchingDs(1)[of G M] graph_invar_subset[of G M]
    by (auto simp add: card_le_Suc0_iff_eq)

  have mD_inj_on_A: "\<lbrakk>x\<in>A; y \<in> A; x \<noteq> y\<rbrakk> \<Longrightarrow> mD x \<noteq> mD y" for x y
  proof(rule ccontr, goal_cases)
    case 1
    have props: "mD x \<in> \<D>" "m x \<in> mD x" "x \<notin> mD x" "mD y \<in> \<D>" "m y \<in> mD x" "y \<notin> mD y"
      using mD_props[of x] mD_props[of y] 1 by auto
    have in_matchings: "{x, m x} \<in> M" "{y, m y} \<in> M"
      using "1"(1,2) m_in_matching by auto
    hence "{x, m x} = {y, m y}"
      using props 1
      by(intro Delta_M_D_unique[of _ "mD x"])
        (auto intro!: in_DeltaI[of "{x, m x}" "m x" x] in_DeltaI[of "{y, m y}" "m y" y] 
            simp add: insert_commute)
    hence "x = y"
      using "1"(4) props(2,6) by fastforce
    thus False 
      using "1"(3) by auto
  qed

  have image_mD_better_bound: 
   "X \<subseteq> A \<Longrightarrow> mD ` X \<subseteq> {D |D. D \<in> \<D> \<and> X \<longleftrightarrow>\<^bsub>G\<^esub> D}" for X
  proof(rule, elim imageE, goal_cases)
    case (1 D x)
    hence D:"D \<in> \<D>" "m x \<in> D" "x \<notin> D"
      using mD_props by auto
    moreover hence "{m x, x} \<in> G" 
      using  "1"(1,3) assms(2)
      by(auto dest!: max_card_matching_subgraphD m_in_matching simp add: insert_commute)
    ultimately have "X \<longleftrightarrow>\<^bsub>G\<^esub> D" 
      using  "1"(3) by(auto simp add: connected_set_of_vertices_def insert_commute)
    then show ?case 
      using D by auto
  qed

  have finite_D: "finite \<D>" 
    using edmonds_gallaiD(2) assms(1) finite_UnionD[of \<D>] infinite_super[of "\<Union> \<D>" "Vs G"]
    by auto

  show number_neighbs_weak:
     "\<lbrakk>X \<subseteq> A; X \<noteq> {}\<rbrakk> \<Longrightarrow> card X \<le> card {D |D. D \<in> \<D> \<and> X \<longleftrightarrow>\<^bsub>G\<^esub> D}" for X
  proof(rule card_inj_on_le[where f = mD], goal_cases)
    case 1
    then show ?case 
      using mD_inj_on_A by(force simp add: inj_on_def)
  next
    case 2
    then show ?case 
      using image_mD_better_bound by presburger
  next
    case 3
    then show ?case 
      by (simp add: finite_D)
  qed

  have miss_in_D_unique:
    "\<lbrakk>x \<in> A; m x \<in> D; D \<in> \<D>; Vs (M \<lbrakk>D\<rbrakk>) \<subseteq> D - {y}; y \<in> D\<rbrakk> \<Longrightarrow> m x = y " for x y D
  proof(goal_cases)
    case 1
    have "m x \<notin> Vs (M \<lbrakk>D\<rbrakk>)"
      using assms(2) "1"(1,2,3) m_in_matching X_in_D_inter_A_empty
      by(intro matched_vertex_not_in_Vs_of_graph_inter_Vs[of _ "{x, m x}"])
        (auto dest: max_card_matchingDs(2))
    moreover have "Vs (M \<lbrakk>D\<rbrakk>) = D - {y}"
      using "1"(3,4,5) first_theses(3) by fastforce
    ultimately show ?case 
      by (simp add: "1"(2,4))
  qed

  show  "\<lbrakk>X \<subseteq> A; X \<noteq> {}; card X = card {D |D. D \<in> \<D> \<and> X \<longleftrightarrow>\<^bsub>G\<^esub> D}\<rbrakk> 
          \<Longrightarrow> X \<union>  \<Union> {D |D. D \<in> \<D> \<and> X \<longleftrightarrow>\<^bsub>G\<^esub> D} \<subseteq> Vs M" for X
  proof(rule, elim UnE, goal_cases)
    case (1 x)
    then show ?case
      using m_on_A[of x, OF _ refl] by blast
  next
    case (2 mx)
    then obtain D where D: "D \<in> \<D>" "X \<longleftrightarrow>\<^bsub>G\<^esub> D" "mx \<in> D"
      by auto
    have inj_on_X:"inj_on mD X"
      using "2"(1) inj_onI[of X mD] mD_inj_on_A in_mono[of X A] by fast
    have image_subs: "mD ` X \<subseteq> {D |D. D \<in> \<D> \<and> X \<longleftrightarrow>\<^bsub>G\<^esub> D}"
      using "2"(1) image_mD_better_bound by presburger
    have "bij_betw mD X {D |D. D \<in> \<D> \<and> X \<longleftrightarrow>\<^bsub>G\<^esub> D}"
    proof(rule ccontr, goal_cases)
      case 1
      hence "mD ` X \<subset> {D |D. D \<in> \<D> \<and> X \<longleftrightarrow>\<^bsub>G\<^esub> D}" 
        using inj_on_X image_subs by(auto simp add: bij_betw_def)
      hence "card (mD ` X) <  card {D |D. D \<in> \<D> \<and> X \<longleftrightarrow>\<^bsub>G\<^esub> D}"
        by(intro psubset_card_mono)(auto simp add: finite_D)
      moreover have "card (mD ` X) = card X"
        using card_image inj_on_X by auto
      ultimately show False
        using 2 by simp
    qed
    then obtain x where x: "x \<in> X" "mD x = D" 
      using  D(1,2) imageE[of D mD X] by(auto simp add: bij_betw_def) 
    have x_mx_in_M:"{x, m x} \<in> M" 
      using "2"(1) x m_in_matching by auto
    show ?case 
    proof(cases "mx = m x")
      case True
      then show ?thesis
        using  x_mx_in_M by auto
    next
      case False
      show ?thesis
      proof(rule ccontr, goal_cases)
        case 1
        hence "Vs (M \<lbrakk>D\<rbrakk>) \<subseteq> D - {mx}"
          using graph_inter_Vs_subset(1,2)[of M D] Vs_subset[of " M \<lbrakk>D\<rbrakk>" M]
          by auto
        hence "m x = mx" 
          using  "2"(1) x(1,2) mD_props D(3)
          by(intro miss_in_D_unique[where D = D]) auto
        thus ?case
          using False by simp
      qed
    qed
  qed

  have Dds_connecting_edge_contr: 
    "\<lbrakk>X \<in> \<D>; X \<noteq> Y; Y \<in> \<D>; x \<in> X; y \<in> Y; {x, y} \<in> G\<rbrakk> \<Longrightarrow> False" for x y X Y
    using  edmonds_gallaiD(5) by(fastforce simp add: connected_set_of_vertices_def)

  have md_inj_A: "inj_on mD A"
    using inj_on_def mD_inj_on_A by blast
  have bij_betw_mD2: "bij_betw mD A {D |D. D \<in> \<D> \<and> D \<subseteq> Vs M}"
  proof-
    have "mD ` A = {D |D. D \<in> \<D> \<and> D \<subseteq> Vs M}"
    proof(rule, all \<open>rule\<close>, elim imageE, goal_cases)
      case (1 D x)
      note one = this
      have D_in_D:"D \<in> \<D>"
        using "1"(1,2) mD_props by auto
      moreover have "D \<subseteq> Vs M"
      proof(rule ccontr, goal_cases)
        case 1
        then obtain y where y: "y \<in> D" "y \<notin> Vs M" by auto
        hence "Vs (M \<lbrakk>D\<rbrakk>) \<subseteq> D - {y}"
          using graph_inter_Vs_subset(1,2)[of M D] Vs_subset[of " M \<lbrakk>D\<rbrakk>" M]
          by auto
        hence "y = m x" 
          using mD_props miss_in_D_unique one(1,2) y(1) by fastforce
        hence "y \<in> Vs M" 
          using edges_are_Vs_2 m_on_A one(2) by fast
        then show False
          using y by simp
      qed
      ultimately show ?case 
        by simp
    next
      case (2 D)
      hence D: "D \<in> \<D>" "D \<subseteq> Vs M"
        by auto
      obtain x where x: "Vs (M\<lbrakk>D\<rbrakk>) = D - {x}" "x \<in> D"
        using D(1) first_theses(3) by force
      obtain y where y: "{x, y} \<in> M" "x \<noteq> y"
        using x(2) assms(1,2) D(2) max_card_matchingDs(1)[of G M] subsetD[of D "Vs M" x]
          graph_invar_no_edge_no_vertex[of M x] graph_invar_subset[of G M] graph_invar_edgeD[of M x x]
        by force
      have y_not_in_D:"y \<notin> D" 
       using x(1,2) Vs_def[of " M \<lbrakk>D\<rbrakk>"] y(1) in_graph_inter_VsI[of "{x, y}" M D]
       by auto
     have y_in_A:"y \<in> A" 
       using max_card_matchingDs(1)[OF assms(2)] y(1)  D(1) x(2)
             Dds_connecting_edge_contr[of D _ x y] y_not_in_D
       by(auto intro!: in_NeighbourhoodI[of x y G] simp add: first_theses(1))
     hence my_is_x: "m y = x" 
       using assms(2) y(1)  doubleton_in_matching(1)[of M y "m y" x]
          m_on_A[of y "m y"] max_card_matchingDs(2)[of G M]
       by(auto simp add: insert_commute)
     note mD_props' = mD_props[OF y_in_A]
     hence "mD y = D"
       using my_is_x mD_props' D(1) edmonds_gallaiD(1)x(2) by (auto simp add: disjoint_def)
     then show ?case 
       using y_in_A by blast
   qed
   thus ?thesis
     using md_inj_A 
     by(auto simp add: bij_betw_def)
 qed

  have card_rw_1:"card (Vs G) = card (Vs M) + card (Vs G - Vs M)"
    using assms(1,2) card_Un_disjoint[of "Vs M" "Vs G - Vs M"] Vs_subset[of M G] 
       max_card_matchingD[of G M] Diff_partition[of "Vs M" "Vs G"] finite_subset[of "Vs M" "Vs G"]
    by auto
  have card_rw_2: "card (Vs M) = 2 * card M" 
    using assms(1,2) max_card_matchingD[of G M] matching_vertices_double_size[of M]
      graph_invar_subgraph[of G M] 
    by auto
  have card_rw_3:"card \<D> = card {D | D. D \<in> \<D> \<and> D \<subseteq> Vs M} + card {D | D. D \<in> \<D> \<and> \<not> D \<subseteq> Vs M}"
    by(subst card_Un_disjnt[symmetric])
      (auto intro!: arg_cong[where f = card] simp add: disjnt_def finite_D)
  have card_A_leq_card_D: "card A \<le> card \<D>" 
    using md_inj_A mD_props finite_D
    by(intro card_inj_on_le[of "mD"]) auto
  have card_rw_4:"card {D |D. D \<in> \<D> \<and> D \<subseteq> Vs M} = card A"
    using bij_betw_same_card bij_betw_mD2 by force
  have card_rw_5:"card (Vs G - Vs M) = card {D |D. D \<in> \<D> \<and> \<not> D \<subseteq> Vs M} \<and>
                  (\<exists> um. bij_betw um (Vs G - Vs M) {D |D. D \<in> \<D> \<and> \<not> D \<subseteq> Vs M})"
  proof(rule select_unique_representative_same_card_and_bijection, goal_cases)
    case (1 D)
    hence D: "D \<in> \<D>" "\<not> D \<subseteq> Vs M" by auto
    then obtain x where x: "x \<in> D" "x \<notin> Vs M"
      by auto
    have x_prop: "x \<in> Vs G - Vs M" "x \<in> D"
      using x D edmonds_gallaiD(2) by auto
    moreover have "\<lbrakk>x' \<in> Vs G - Vs M; x' \<in> D\<rbrakk> \<Longrightarrow> x' = x" for x'
    proof(rule ccontr, goal_cases)
      case 1
      have "x' \<notin> Vs (M\<lbrakk>D\<rbrakk>)" 
        using"1"(1) not_in_Vs_no_edge[of x' " M \<lbrakk>D\<rbrakk>"] not_in_Vs_no_edge[of x' M]
              in_graph_inter_VsD(1)[of _ M D] 
        by auto
      moreover have "x \<notin> Vs (M\<lbrakk>D\<rbrakk>)" 
        using x not_in_Vs_no_edge[of x " M \<lbrakk>D\<rbrakk>"] not_in_Vs_no_edge[of x' M]
              in_graph_inter_VsD(1)[of _ M D] 
        by auto
      ultimately have "x = x'" 
        using "1"(2) D(1) first_theses(3) x_prop(2) by fastforce
      thus False
        using 1 by simp
    qed
    ultimately show ?case 
      by metis
  next
    case (2 x)
    moreover then obtain D where D: "D \<in> \<D>" "x \<in> D"
      using edmonds_gallaiD(11) by auto
    moreover have D_not_in_M: "\<not> D \<subseteq> Vs M"
      using "2" D(2) by blast
    ultimately show ?case
      using edmonds_gallaiD(1)
      by(intro ex1I[of _ D]) (auto simp add: disjoint_def)
  qed (auto simp add: finite_D assms(1))
  hence card_rw_5:"card (Vs G - Vs M) = card {D |D. D \<in> \<D> \<and> \<not> D \<subseteq> Vs M}"
        and biject: "(\<exists> um. bij_betw um (Vs G - Vs M) {D |D. D \<in> \<D> \<and> \<not> D \<subseteq> Vs M})"
    by auto

  show "2 * card  M + (int (card \<D>) - int (card A)) = card (Vs G)"
    using card_A_leq_card_D
    unfolding card_rw_1 card_rw_2 card_rw_3 card_rw_4 card_rw_5
    by simp

  show  "\<Union> \<D> = inessentials G"
    using edmonds_gallaiD(2,8)
    unfolding inessentials_are_evens_of_max_matching[OF assms(1,2)]
    by auto
  obtain um where um: "bij_betw um (Vs G - Vs M) {D |D. D \<in> \<D> \<and> \<not> D \<subseteq> Vs M}"
    using biject by auto
  thus "\<exists> m. inj_on m (Vs G - Vs M) \<and> m ` (Vs G - Vs M) \<subseteq> \<D>"
    using bij_betw_imp_surj_on[OF um]
    by(auto intro!: exI[of _ um] intro: bij_betw_imp_inj_on)
qed

lemma edmonds_gallai_on_matching_strong_hall:
  assumes "graph_invar G" "max_card_matching G M" "edmonds_gallai G M \<D> A"
  shows  "\<And> X. \<lbrakk>X \<subseteq> A; X \<noteq> {}\<rbrakk> \<Longrightarrow> card X < card {D | D . D \<in> \<D> \<and> X \<longleftrightarrow>\<^bsub>G\<^esub> D}"
proof(rule ccontr, goal_cases)
  case (1 X)
  note edmonds_gallaiD = edmonds_gallaiD[OF assms(3)]
  note edmonds_gallai_on_matching_props1 = edmonds_gallai_on_matching_props[OF assms]
  have X_card: "card X = card {D |D. D \<in> \<D> \<and> X \<longleftrightarrow>\<^bsub>G\<^esub> D}"
    using "1"(1,2,3) edmonds_gallai_on_matching_props1(6)[of X]
    by auto
  have finiteD: "finite \<D>"
    using assms(1) diff_components_finite edmonds_gallai_on_matching_props1(1) by auto
  have finite_X_nieghbs: "finite {D |D. D \<in> \<D> \<and> X \<longleftrightarrow>\<^bsub>G\<^esub> D}" 
    using finiteD by fastforce
  have X_in_G:"X \<subseteq> Vs G" 
    using "1"(1) Neighbourhood_in_G edmonds_gallai_on_matching_props1(2) by fastforce
  have finite_X:"finite X"
    using X_in_G assms(1) rev_finite_subset by auto
  hence "{D |D. D \<in> \<D> \<and> X \<longleftrightarrow>\<^bsub>G\<^esub> D} \<noteq> {}"
    using 1(2) X_card  card_gt_0_iff[of "{D |D. D \<in> \<D> \<and> X \<longleftrightarrow>\<^bsub>G\<^esub> D}"] by auto
  then obtain D where D: "D \<in> \<D>" "X \<longleftrightarrow>\<^bsub>G\<^esub> D" 
    by auto
  then obtain x where x: "x \<in> D"
    using edmonds_gallaiD(3) by auto
  hence "x \<in> inessentials G" 
    using D(1) edmonds_gallai_on_matching_props1(11) by auto
  hence inessntial_x: "inessential G x" 
    by(auto elim!: in_inessentialsE)
  then obtain M' where M': "max_card_matching G M'" "x \<notin> Vs M'"
    by(auto elim!: inessentialE)
  interpret computesth: obtain_edmonds_gallai G
    by unfold_locales (simp add: assms(1))
  note new_edg = computesth.decomposition_correct[OF M'(1)]
  note edmonds_gallai_on_matching_props2 =
         edmonds_gallai_on_matching_props[OF assms(1) M'(1) new_edg]
  note edg_rws = edmonds_gallai_on_matching_props2(1,2,11)
  note Odds_is = edg_rws(1)[simplified edg_rws(2, 3), symmetric] 
  note evens_is = edg_rws(2)[simplified edg_rws(3)]
        
  note old_edg_rws = edmonds_gallai_on_matching_props1(1,2,11)
  note D_is = old_edg_rws(1)[simplified old_edg_rws(2, 3), symmetric] 
  note A_is = old_edg_rws(2)[simplified old_edg_rws(3)]

  note transformed_to_snd = 
     edmonds_gallai_on_matching_props2(7)[simplified Odds_is evens_is, folded D_is A_is]

  show False
    using transformed_to_snd[OF 1(1,2) X_card] D M'(2) x by blast
qed

definition "adj_inessentials G = Neighbourhood G (inessentials G)"

abbreviation "\<oo>\<cc> \<equiv> odd_comps_in_diff"
abbreviation "\<A> \<equiv> adj_inessentials"
abbreviation "\<I> \<equiv> inessentials"

theorem edmonds_gallai_decomposition_all:
  assumes "graph_invar G" "max_card_matching G M"
  shows 
  "\<lbrakk>X \<in> \<oo>\<cc> G (\<A> G); x \<in> X\<rbrakk> \<Longrightarrow> \<exists>M. graph_matching ( G \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x}"
  "X \<in> \<oo>\<cc> G (\<A> G) \<Longrightarrow> \<exists>x. x \<in> X \<and> Vs ( M \<lbrakk>X\<rbrakk>) = X - {x}"
  "perfect_matching (G \<setminus> \<Union> (\<oo>\<cc> G (\<A> G)) \<union> \<A> G) (M \<setminus> \<Union> (\<oo>\<cc> G (\<A> G)) \<union> \<A> G)"
  "\<lbrakk>X \<subseteq> \<A> G; X \<noteq> {}\<rbrakk> \<Longrightarrow> card X < card {D |D. D \<in> \<oo>\<cc> G (\<A> G) \<and> X \<longleftrightarrow>\<^bsub>G\<^esub> D}"
  "\<exists>m. inj_on m (\<A> G) \<and> m ` \<A> G \<subseteq> \<Union> (\<oo>\<cc> G (\<A> G)) \<and>
        (\<forall>x\<in>\<A> G. {x, m x} \<in> M) \<and>
        (\<forall>x y. x \<in> \<A> G \<and> y \<in> \<A> G \<and> x \<noteq> y \<longrightarrow>
        (\<exists>D1 D2. D1 \<in> \<oo>\<cc> G (\<A> G) \<and> D2 \<in> \<oo>\<cc> G (\<A> G) \<and> D1 \<noteq> D2 \<and> m x \<in> D1 \<and> m y \<in> D2))"
  "2 * \<nu> G + (int (card (\<oo>\<cc> G (\<A> G))) - int (card (\<A> G))) = card (Vs G)"
  "\<lbrakk>e \<in> M ; \<lbrakk>e \<subseteq> Vs G - \<Union> (\<oo>\<cc> G (\<A> G)) - \<A> G\<rbrakk> \<Longrightarrow> P;
      \<And>x y D. \<lbrakk>e = {x, y}; x \<in> \<A> G; y \<in> D; D \<in> \<oo>\<cc> G (\<A> G); x \<noteq> y\<rbrakk> \<Longrightarrow> P;
      \<And>D. \<lbrakk>D \<in> \<oo>\<cc> G (\<A> G); e \<subseteq> D\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  "\<Union> (\<oo>\<cc> G (\<A> G)) = \<I> G"
  "\<exists>m. inj_on m (Vs G - Vs M) \<and> m ` (Vs G - Vs M) \<subseteq> \<oo>\<cc> G (\<A> G)"
  "\<lbrakk>e \<in> G; e \<subseteq> Vs G - \<Union> (\<oo>\<cc> G (\<A> G)) - \<A> G \<Longrightarrow> P; e \<subseteq> \<A> G \<Longrightarrow> P;
      \<And>x y D. \<lbrakk>e = {x, y}; x \<in> \<A> G; y \<in> D; D \<in> \<oo>\<cc> G (\<A> G); x \<noteq> y\<rbrakk> \<Longrightarrow> P;
      \<And>x y. \<lbrakk>e = {x, y}; x \<in> \<A> G; y \<in> Vs G - \<Union> (\<oo>\<cc> G (\<A> G)) - \<A> G; x \<noteq> y\<rbrakk> \<Longrightarrow> P;
      \<And>D. \<lbrakk>D \<in> \<oo>\<cc> G (\<A> G); e \<subseteq> D\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
proof-
interpret computesth: obtain_edmonds_gallai G
    by unfold_locales (simp add: assms(1))
  note new_edg = computesth.decomposition_correct[OF assms(2)]
  note edmonds_gallai_on_matching_props =
         edmonds_gallai_on_matching_props[OF assms new_edg]
  note edg_rws = edmonds_gallai_on_matching_props(1,2,11)
  note Odds_is = edg_rws(1)[simplified edg_rws(2, 3), symmetric] 
  note evens_is = edg_rws(2)[simplified edg_rws(3)]
        
  note edmonds_gallai_on_matching_props =
    edmonds_gallai_on_matching_props[simplified Odds_is evens_is, folded adj_inessentials_def]

  note strong_hall = 
    edmonds_gallai_on_matching_strong_hall[OF assms new_edg,
          simplified Odds_is evens_is, folded adj_inessentials_def]

  have nu_def: "\<nu> G = card M" 
    using assms(2) computesth.graph_invar max_matching_is_\<nu>[of G M] finite_Vs_then_finite[of G]
    by auto

  show   "\<lbrakk>X \<in> \<oo>\<cc> G (\<A> G); x \<in> X\<rbrakk> \<Longrightarrow> \<exists>M. graph_matching ( G \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x}"
  "X \<in> \<oo>\<cc> G (\<A> G) \<Longrightarrow> \<exists>x. x \<in> X \<and> Vs ( M \<lbrakk>X\<rbrakk>) = X - {x}"
  "perfect_matching (G \<setminus> \<Union> (\<oo>\<cc> G (\<A> G)) \<union> \<A> G) (M \<setminus> \<Union> (\<oo>\<cc> G (\<A> G)) \<union> \<A> G)"
  "\<lbrakk>X \<subseteq> \<A> G; X \<noteq> {}\<rbrakk> \<Longrightarrow> card X < card {D |D. D \<in> \<oo>\<cc> G (\<A> G) \<and> X \<longleftrightarrow>\<^bsub>G\<^esub> D}"
  "\<exists>m. inj_on m (\<A> G) \<and> m ` \<A> G \<subseteq> \<Union> (\<oo>\<cc> G (\<A> G)) \<and>
        (\<forall>x\<in>\<A> G. {x, m x} \<in> M) \<and>
        (\<forall>x y. x \<in> \<A> G \<and> y \<in> \<A> G \<and> x \<noteq> y \<longrightarrow>
               (\<exists>D1 D2. D1 \<in> \<oo>\<cc> G (\<A> G) \<and> D2 \<in> \<oo>\<cc> G (\<A> G) \<and> D1 \<noteq> D2 \<and> m x \<in> D1 \<and> m y \<in> D2))"
  "2 * \<nu> G + (int (card (\<oo>\<cc> G (\<A> G))) - int (card (\<A> G))) = card (Vs G)"
  "\<Union> (\<oo>\<cc> G (\<A> G)) = \<I> G"
  "\<exists>m. inj_on m (Vs G - Vs M) \<and> m ` (Vs G - Vs M) \<subseteq> \<oo>\<cc> G (\<A> G)"
    unfolding nu_def
    using edmonds_gallai_on_matching_props strong_hall by auto
  show "\<lbrakk>e \<in> M ; \<lbrakk>e \<subseteq> Vs G - \<Union> (\<oo>\<cc> G (\<A> G)) - \<A> G\<rbrakk> \<Longrightarrow> P;
      \<And>x y D. \<lbrakk>e = {x, y}; x \<in> \<A> G; y \<in> D; D \<in> \<oo>\<cc> G (\<A> G); x \<noteq> y\<rbrakk> \<Longrightarrow> P;
      \<And>D. \<lbrakk>D \<in> \<oo>\<cc> G (\<A> G); e \<subseteq> D\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  "\<lbrakk>e \<in> G; e \<subseteq> Vs G - \<Union> (\<oo>\<cc> G (\<A> G)) - \<A> G \<Longrightarrow> P; e \<subseteq> \<A> G \<Longrightarrow> P;
      \<And>x y D. \<lbrakk>e = {x, y}; x \<in> \<A> G; y \<in> D; D \<in> \<oo>\<cc> G (\<A> G); x \<noteq> y\<rbrakk> \<Longrightarrow> P;
      \<And>x y. \<lbrakk>e = {x, y}; x \<in> \<A> G; y \<in> Vs G - \<Union> (\<oo>\<cc> G (\<A> G)) - \<A> G; x \<noteq> y\<rbrakk> \<Longrightarrow> P;
      \<And>D. \<lbrakk>D \<in> \<oo>\<cc> G (\<A> G); e \<subseteq> D\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
      using  edmonds_gallai_on_matching_props(10,13)[of e P] by force+
  qed

theorem edmonds_gallai_decomposition_general:
 assumes "graph_invar G"
 shows 
  "\<lbrakk>X \<in> \<oo>\<cc> G (\<A> G); x \<in> X\<rbrakk> \<Longrightarrow> \<exists>M. graph_matching ( G \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x}"
  "\<exists> M. perfect_matching (G \<setminus> \<Union> (\<oo>\<cc> G (\<A> G)) \<union> \<A> G) M"
  "\<lbrakk>X \<subseteq> \<A> G; X \<noteq> {}\<rbrakk> \<Longrightarrow> card X < card {D |D. D \<in> \<oo>\<cc> G (\<A> G) \<and> X \<longleftrightarrow>\<^bsub>G\<^esub> D}"
  "2 * \<nu> G + (int (card (\<oo>\<cc> G (\<A> G))) - int (card (\<A> G))) = card (Vs G)"
  "\<Union> (\<oo>\<cc> G (\<A> G)) = \<I> G"
  "\<lbrakk>e \<in> G; e \<subseteq> Vs G - \<Union> (\<oo>\<cc> G (\<A> G)) - \<A> G \<Longrightarrow> P; e \<subseteq> \<A> G \<Longrightarrow> P;
    \<And>x y D. \<lbrakk>e = {x, y}; x \<in> \<A> G; y \<in> D; D \<in> \<oo>\<cc> G (\<A> G); x \<noteq> y\<rbrakk> \<Longrightarrow> P;
    \<And>x y. \<lbrakk>e = {x, y}; x \<in> \<A> G; y \<in> Vs G - \<Union> (\<oo>\<cc> G (\<A> G)) - \<A> G; x \<noteq> y\<rbrakk> \<Longrightarrow> P;
    \<And>D. \<lbrakk>D \<in> \<oo>\<cc> G (\<A> G); e \<subseteq> D\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
proof-
  obtain M where M: "max_card_matching G M"
    using assms finite_Vs_then_finite max_card_matching_exists by auto
  show"\<lbrakk>X \<in> \<oo>\<cc> G (\<A> G); x \<in> X\<rbrakk> \<Longrightarrow> \<exists>M. graph_matching ( G \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x}"
  "\<exists> M. perfect_matching (G \<setminus> \<Union> (\<oo>\<cc> G (\<A> G)) \<union> \<A> G) M"
  "\<lbrakk>X \<subseteq> \<A> G; X \<noteq> {}\<rbrakk> \<Longrightarrow> card X < card {D |D. D \<in> \<oo>\<cc> G (\<A> G) \<and> X \<longleftrightarrow>\<^bsub>G\<^esub> D}"
  "2 * \<nu> G + (int (card (\<oo>\<cc> G (\<A> G))) - int (card (\<A> G))) = card (Vs G)"
  "\<Union> (\<oo>\<cc> G (\<A> G)) = \<I> G"
    using edmonds_gallai_decomposition_all[OF assms M] by auto
  show   "\<lbrakk>e \<in> G; e \<subseteq> Vs G - \<Union> (\<oo>\<cc> G (\<A> G)) - \<A> G \<Longrightarrow> P; e \<subseteq> \<A> G \<Longrightarrow> P;
      \<And>x y D. \<lbrakk>e = {x, y}; x \<in> \<A> G; y \<in> D; D \<in> \<oo>\<cc> G (\<A> G); x \<noteq> y\<rbrakk> \<Longrightarrow> P;
      \<And>x y. \<lbrakk>e = {x, y}; x \<in> \<A> G; y \<in> Vs G - \<Union> (\<oo>\<cc> G (\<A> G)) - \<A> G; x \<noteq> y\<rbrakk> \<Longrightarrow> P;
      \<And>D. \<lbrakk>D \<in> \<oo>\<cc> G (\<A> G); e \<subseteq> D\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
    using edmonds_gallai_decomposition_all(10)[OF assms M, of e P] by simp
qed

lemmas edmonds_gallai_decomposition_max_matching_specific =
   edmonds_gallai_decomposition_all(2,3,5,7)

lemma decomposition_is_berge_maximiser:
  assumes "graph_invar G" "X \<subseteq> Vs G"
  shows "int (card (\<oo>\<cc> G X)) - int (card X) \<le> int (card (\<oo>\<cc> G (\<A> G))) - int (card (\<A> G))"
proof-
   obtain M where M: "max_card_matching G M"
     using assms(1) finite_Vs_then_finite max_card_matching_exists by auto
   hence graph_match:"graph_matching G M"
     by (simp add: max_card_matchingDs(1,2))
   have M_card: "card M = \<nu> G"
     by (simp add: M assms(1) finite_Vs_then_finite max_matching_is_\<nu>)
   show ?thesis
     using left_uncoverred_matching[OF assms(1) graph_match assms(2)]
           edmonds_gallai_decomposition_general(4)[OF assms(1), symmetric]
     by (auto simp add: algebra_simps M_card)
 qed

lemma decomposition_is_berge_maximiser_nat:
  assumes "graph_invar G" "X \<subseteq> Vs G"
  shows "card (\<oo>\<cc> G X) - card X \<le> card (\<oo>\<cc> G (\<A> G)) - card (\<A> G)"
  using decomposition_is_berge_maximiser[OF assms] by simp

lemma berge_max_geq_0:
  assumes "finite (Vs G)"
  shows "Max {int (card (\<oo>\<cc> G X)) - int (card X) | X. X \<subseteq> Vs G} \<ge> 0"
proof-
  have "Max {int (card (\<oo>\<cc> G X)) - int (card X) | X. X \<subseteq> Vs G} 
        \<ge> int (card (\<oo>\<cc> G {})) - int (card {})"
  proof(rule linorder_class.Max.coboundedI[of _ "int (card (\<oo>\<cc> G {})) - int (card {})"], goal_cases)
    case 1
    then show ?case 
      unfolding setcompr_eq_image
      by(auto intro!: finite_imageI[of _ "\<lambda> X. int (card (\<oo>\<cc> G X)) - int (card X)", simplified]
                      finite_Collect_subsets 
            simp add: assms(1))
  next
    case 2
    then show ?case 
      by force
  qed
  also have "int (card (\<oo>\<cc> G {})) - int (card {}) \<ge> 0"
    by auto
  finally show ?thesis
    by auto
qed
lemma berge_max_restricted_to_pos:
  assumes "finite (Vs G)"
  shows"Max {int (card (\<oo>\<cc> G X)) - int (card X) | X. X \<subseteq> Vs G} =
       Max {int (card (\<oo>\<cc> G X)) - int (card X) | X. X \<subseteq> Vs G \<and> 
        int (card (\<oo>\<cc> G X)) - int (card X) \<ge> 0}"
proof(rule linorder_class.Max_eq_if, goal_cases)
  case 3
  then show ?case 
  proof(rule ballI, goal_cases)
    case (1 a)
    then obtain X where "a = int (card (\<oo>\<cc> G X)) - int (card X)" "X \<subseteq> Vs G"
      by auto
    then show ?case 
    proof(cases "card X \<le> card (\<oo>\<cc> G X)", goal_cases)
      case 1
      then show ?thesis 
        by auto
    next
      case 2
      thus ?case
        by(auto intro!: exI[of _ "int (card (\<oo>\<cc> G {}))"] exI[of _ "{}"])
  qed
 qed 
qed (auto simp add: assms(1))

lemma card_odd_comp_leq_card_Vs_G:
  assumes "finite (Vs G)"
  shows "card (\<oo>\<cc> G (Vs G)) \<le> card (Vs G)"
proof(rule order.trans[OF _ number_comps_below_vertex_card, where E1 = G], goal_cases)
  case 1
  then show ?case
    using assms
    by(auto intro!: card_mono finite_verts_finite_no_comps 
              dest: finite_Vs_then_finite
              elim: odd_comps_in_diff_are_componentsOb)
next
  case 2
  then show ?case 
    by (simp add: assms finite_Vs_then_finite)
qed (simp add: assms)

lemma berge_max_nat_swap:
  assumes "finite (Vs G)"
  shows "Max {int (card (\<oo>\<cc> G X)) - int (card X) | X. X \<subseteq> Vs G} =
        Max {card (\<oo>\<cc> G X) - card X | X. X \<subseteq> Vs G}"
proof-
  have finite1: "finite {int (card (\<oo>\<cc> G X)) - int (card X) | X. X \<subseteq> Vs G}"
  and finite2: "finite {card (\<oo>\<cc> G X) - card X | X. X \<subseteq> Vs G}"
    using assms by auto
  have nempty:"{int (card (\<oo>\<cc> G X)) - int (card X) | X. X \<subseteq> Vs G} \<noteq> {}"
       "{card (\<oo>\<cc> G X) - card X | X. X \<subseteq> Vs G} \<noteq> {}"
    by auto
  obtain i X where i:"i \<in> {int (card (\<oo>\<cc> G X)) - int (card X) | X. X \<subseteq> Vs G}"
   "i = Max {int (card (\<oo>\<cc> G X)) - int (card X) | X. X \<subseteq> Vs G}" 
    "i = int (card (\<oo>\<cc> G X)) - int (card X)" "X \<subseteq> Vs G"
    using finite1 nempty(1)
      Max_eq_iff[of "{int (card (\<oo>\<cc> G uub)) - int (card uub) |uub. uub \<subseteq> Vs G}"
        "Max {int (card (\<oo>\<cc> G uub)) - int (card uub) |uub. uub \<subseteq> Vs G}"]
    by auto
  have i_geq: "X' \<subseteq> Vs G \<Longrightarrow> int (card (\<oo>\<cc> G X')) - int (card X') \<le> i" for X'
    using Max_ge finite1 i(2) by blast
  obtain n X' where n: "n \<in> {card (\<oo>\<cc> G X) - card X | X. X \<subseteq> Vs G}"
       "n = Max {card (\<oo>\<cc> G X) - card X | X. X \<subseteq> Vs G}"
       "n = card (\<oo>\<cc> G X') - card X'" "X' \<subseteq> Vs G"
    using finite2 nempty(2)
      Max_eq_iff[of "{card (\<oo>\<cc> G uub) - card uub |uub. uub \<subseteq> Vs G}"
        "Max {card (\<oo>\<cc> G uub) - card uub |uub. uub \<subseteq> Vs G}"]
    by auto
  have n_geq: "X' \<subseteq> Vs G \<Longrightarrow> card (\<oo>\<cc> G X') - card X' \<le> n" for X'
    using Max_ge finite2 n(2) by blast
  have i_pos:"i \<ge> 0" 
    using i(3,4) i_geq[of "{}"] by auto
  have "n = i"
  proof(rule ccontr, goal_cases)
    case 1
    hence "n < i \<or> i < n" by auto
    then show ?case 
      using i_pos i(3,4) n(3,4) i_geq[of X']  n_geq[of X'] i_geq[of X]  n_geq[of X]
      by(auto simp add: algebra_simps)
  qed
  thus ?thesis
    using i(2) n(2) by argo
qed

lemma adj_inessentialsin_G: "\<A> G \<subseteq> Vs G"
  by (simp add: Neighbourhood_in_G adj_inessentials_def)

lemma Max_valid:
  assumes "graph_invar G"
  shows "Max {int (card (\<oo>\<cc> G X)) - int (card X) | X. X \<subseteq> Vs G} =
   int (card (\<oo>\<cc> G (\<A> G))) - int (card (\<A> G))"
proof(rule linorder_class.Max_eqI, goal_cases)
  case 1
  then show ?case 
    using assms by simp
next
  case (2 X)
  then show ?case 
    using decomposition_is_berge_maximiser[OF assms] by auto
next
  case 3
  then show ?case
    using adj_inessentialsin_G by force
qed

lemma berge_formula:
  assumes "graph_invar G" 
  assumes \<mu>_def: "\<mu> = Max {int (card (\<oo>\<cc> G X)) - int (card X) | X. X \<subseteq> Vs G}"
  shows   "int (2 * \<nu> G) + \<mu> = card (Vs G)"
  unfolding \<mu>_def Max_valid[OF assms(1)] edmonds_gallai_decomposition_general(4)[OF assms(1)]
  by auto

lemma berge_formula_unfolded:
  assumes "graph_invar G" "X \<subseteq> Vs G"
    "\<And> X'. X' \<subseteq> Vs G \<Longrightarrow> int (card (\<oo>\<cc> G X')) - int (card X') 
                 \<le>  int (card (\<oo>\<cc> G X)) - int (card X) "
  shows   "2 * \<nu> G +  int (card (\<oo>\<cc> G X)) - int (card X) = card (Vs G)"
  using decomposition_is_berge_maximiser[OF assms(1,2)] assms(3)[OF adj_inessentialsin_G] 
  by (simp  add:  berge_formula[OF assms(1) refl, symmetric] Max_valid[OF assms(1)])

lemma berge_formula_nat:
  assumes "graph_invar G" 
  assumes \<mu>_def: "\<mu> = Max {card (\<oo>\<cc> G X) - card X | X. X \<subseteq> Vs G}"
  shows   "2 * \<nu> G + \<mu> = card (Vs G)"
proof-
  have finite:"finite (Vs G)"
    using assms(1) by auto
  show ?thesis
    using berge_formula[OF assms(1) refl]
    by(simp add: \<mu>_def berge_max_nat_swap[OF finite])
qed

lemma Max_valid_nat:
  assumes "graph_invar G"
  shows "Max {card (\<oo>\<cc> G X) - card X | X. X \<subseteq> Vs G} = card (\<oo>\<cc> G (\<A> G)) - card (\<A> G)"
proof -
  have f1: "card (\<oo>\<cc> G (\<A> G)) - card (\<A> G) \<in> {card (\<oo>\<cc> G A) - card A |A. A \<subseteq> Vs G}"
    using adj_inessentialsin_G by force
  have f2: "{} \<noteq> {card (\<oo>\<cc> G A) - card A |A. A \<subseteq> Vs G}"
    by blast
  have "finite {card (\<oo>\<cc> G A) - card A |A. A \<subseteq> Vs G}"
    by (simp add: assms)
  then have "(\<exists>A. Max {card (\<oo>\<cc> G A) - card A |A. A \<subseteq> Vs G} = card (\<oo>\<cc> G A) - card A \<and> A \<subseteq> Vs G) \<and> finite (Vs G) \<and> (\<exists>A. Max {card (\<oo>\<cc> G A) - card A |A. A \<subseteq> Vs G} = card (\<oo>\<cc> G A) - card A \<and> A \<subseteq> Vs G) \<and> finite {card (\<oo>\<cc> G A) - card A |A. A \<subseteq> Vs G} \<and> dblton_graph G"
    using f2 Max_in[of "{card (\<oo>\<cc> G A) - card A |A. A \<subseteq> Vs G}"] assms by simp
  then show ?thesis
    using f1 
   using Max_ge[of "{card (\<oo>\<cc> G uub) - card uub |uub. uub \<subseteq> Vs G}" "card (\<oo>\<cc> G (\<A> G)) - card (\<A> G)"]
      order_antisym[of "Max {card (\<oo>\<cc> G uub) - card uub |uub. uub \<subseteq> Vs G}" "card (\<oo>\<cc> G (\<A> G)) - card (\<A> G)"]
      decomposition_is_berge_maximiser_nat[of G]
   by fastforce
qed

lemma berge_formula_nat_unfolded:
  assumes "graph_invar G" "X \<subseteq> Vs G"
    "\<And> X'. X' \<subseteq> Vs G \<Longrightarrow> card (\<oo>\<cc> G X') -card X' \<le>  card (\<oo>\<cc> G X) - card X"
  shows   "2 * \<nu> G +(card (\<oo>\<cc> G X) - card X) = card (Vs G)"
  using decomposition_is_berge_maximiser_nat[OF assms(1,2)] assms(3)[OF adj_inessentialsin_G] 
  unfolding berge_formula_nat[OF assms(1) refl, symmetric] Max_valid_nat[OF assms(1)]
  by (auto simp add: algebra_simps)
 
end