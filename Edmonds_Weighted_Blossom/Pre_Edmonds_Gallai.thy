theory Pre_Edmonds_Gallai
  imports Blossom.Blossom_Algo_Search
begin

section \<open>A Reduced Version of the Edmonds-Gallai Decomposition\<close>

subsection \<open>Preparations for Quotient: TO BE MOVED\<close>

(*Move connectedness?*)
definition "connected_set_of_vertices X G Y = (\<exists> u v. {u, v} \<in> G \<and> u \<in> X \<and> v \<in> Y)"

notation connected_set_of_vertices ( "_ \<longleftrightarrow>\<^bsub>_\<^esub> _")

lemma connected_sym: "connected_set_of_vertices X G Y \<longleftrightarrow> connected_set_of_vertices Y G X"
  by(auto simp add: connected_set_of_vertices_def)(meson edge_commute)+

abbreviation "disconnected_verts X G Y \<equiv> \<not> connected_set_of_vertices X G Y"

notation disconnected_verts ( "_ \<leftarrow>|\<rightarrow>\<^bsub>_\<^esub> _")

lemma empty_Delta_disconnected:
  "\<lbrakk>X \<inter> Y = {};Delta G X = {}\<rbrakk> \<Longrightarrow> \<not> connected_set_of_vertices X G Y"
  by(auto simp add: connected_set_of_vertices_def Delta_def)

context quot
begin

lemma Delta_s_empty_s_not_in_quot:
  assumes "Delta E s= {}" 
  shows"u \<notin> Vs (quotG E)"
proof-
  have "xc = u"
    if "\<And> x u v. \<lbrakk>u \<in> s; {u, v} \<in> E; x = {u, v}\<rbrakk> \<Longrightarrow> v \<in> s"
       "e \<in> E" "xb \<in> e" "xb \<notin> s" "xc \<in> e" "xc \<in> s"
     for e xb xc
    using that(2)
  proof(elim dblton_graphE[of e], goal_cases)
    case (1 u v)
    then show ?case 
      using that(2,3,4,5,6) that(1)[of v u "{v, u}"] that(1)[of u v "{u, v}"]
      by (auto simp add: insert_commute)
  qed
  thus ?thesis
    using good_quot_map assms(1) 
    by(auto simp add: Delta_def quot_graph_def vs_member)
qed

lemma s_not_in_quot_Delta_s_empty:
  assumes"u \<notin> Vs (quotG E)"
  shows "Delta E s= {}" 
proof(rule ccontr, goal_cases)
  case 1
  then obtain x y where "x \<in> s" "y \<notin> s" "{x, y} \<in> E"
    by(auto elim!: in_DeltaE)
  hence "{y, u} \<in> (quotG E)"
    unfolding quot_graph_def
    using assms edge_in_graph_edge_in_quot edges_are_Vs_2 
    by(auto intro!: bexI[of _ "{y, u}"])
  hence "u \<in> Vs (quotG E)" 
    by auto
  then show ?case 
    using assms by auto
qed

lemma Delta_s_empty_iff_s_not_in_quot:
 "Delta E s = {} \<longleftrightarrow> u \<notin> Vs (quotG E)"
  using Delta_s_empty_s_not_in_quot s_not_in_quot_Delta_s_empty by blast

lemma Delta_s_Delta_compl_s_iff_empty:
  "Delta E s = {} \<longleftrightarrow> Delta E (Vs E - s) = {}"
proof-
  have helper:"v \<in> s"
    if "\<And> x u v. \<lbrakk>u \<in> Vs E; {u, v} \<in> E; x = {u, v}\<rbrakk> \<Longrightarrow> u \<in> s \<or> v \<in> Vs E \<and> v \<notin> s"
    "u \<in> s" "{u, v} \<in> E" for u v
    using that insert_commute[of u v "{}"] edges_are_Vs[of v u E]
    by auto
  show ?thesis
    by(auto simp add: Delta_def insert_commute| rule helper)+
qed

lemma quot_Vs_in_s: "Vs (quotG E) \<supseteq> s"
  using vert_in_graph_iff_in_quot_diff_u good_quot_map(2) by auto

lemma Delta_wth_s_empty_quot_Vs:
 "Delta E (Vs E - s) = {} \<Longrightarrow> Vs (quotG E) = s"
 using Delta_s_Delta_compl_s_iff_empty Delta_s_empty_iff_s_not_in_quot quot_Vs_in_s
  by (auto intro!: in_quotG_neq_u)

lemma Delta_wth_s_nonempty_quot_Vs:
 "Delta E (Vs E - s) \<noteq> {} \<Longrightarrow> Vs (quotG E) = insert u s"
  using quot_Vs_in_s  neq_u_notin_quotG  Delta_s_Delta_compl_s_iff_empty s_not_in_quot_Delta_s_empty 
  by force+

lemma edge_in_s_in_quotG: 
  assumes "e \<subseteq> s" "G \<subseteq> E"
  shows "e \<in> quotG G \<longleftrightarrow> e \<in> G"
proof-
  have helper1: 
    "\<lbrakk>(\<lambda>x. u) ` (ea \<inter> {v. v \<notin> s}) \<subseteq> s; ea \<in> G; ea \<inter> s \<union> (\<lambda>x. u) ` (ea \<inter> {v. v \<notin> s}) \<notin> G\<rbrakk>
      \<Longrightarrow> x = u" for ea x
    using good_quot_map(1) all_not_in_conv[of "ea \<inter> {R. R \<notin> s}"] inf_sup_aci(1)[of s ea] 
          subsetI[of ea s] subsetI[of "{}" "(\<lambda>Q. u) ` bot"] inf.absorb2[of ea s] 
    by auto
  have helper2: 
    "\<lbrakk>(\<lambda>x. u) ` (ea \<inter> {v. v \<notin> s}) \<subseteq> s; ea \<in> G; ea \<inter> s \<union> (\<lambda>x. u) ` (ea \<inter> {v. v \<notin> s}) \<notin> G\<rbrakk>
      \<Longrightarrow> u \<in> ea" for ea 
    using assms(2) subset_edges_G[of G ea] helper1[of ea]
    by force
  have helper3:
    "\<lbrakk>ea \<in> G; ea \<inter> s \<union> (\<lambda>x. u) ` (ea \<inter> {v. v \<notin> s}) \<notin> G;
       u \<notin> (\<lambda>x. u) ` (ea \<inter> {v. v \<notin> s})\<rbrakk> \<Longrightarrow> u \<in> s"
    for ea
    using rev_image_eqI[of u "ea \<inter> {R. R \<notin> s}" u "\<lambda>Q. u"]
      helper2[of ea] 
    by auto
  show ?thesis
    using assms
    by(auto simp add: quot_graph_def intro: helper1 helper2 helper3)
qed

lemma edge_in_s_then_in_quotG:  "\<lbrakk>e \<subseteq> s;  e \<in> E\<rbrakk> \<Longrightarrow> e \<in> quotG E"
and edge_in_s_id_in_quotG:  "\<lbrakk>e \<subseteq> s; e \<in> quotG E\<rbrakk> \<Longrightarrow> e \<in> E"
and edge_in_s_then_in_quot_graph: "\<lbrakk>e \<subseteq> s;  e \<in> E\<rbrakk> \<Longrightarrow> e \<in> quot_graph P E"
  using edge_in_s_in_quotG by auto

lemma edge_in_s_then_in_quotG_subgraph:  "\<lbrakk>e \<subseteq> s; e \<in> G; G \<subseteq> E\<rbrakk> \<Longrightarrow> e \<in> quotG G"
and edge_in_s_id_in_quotG_subgraph:  "\<lbrakk>e \<subseteq> s; e \<in> quotG G; G \<subseteq> E\<rbrakk> \<Longrightarrow> e \<in> G"
  using edge_in_s_in_quotG by auto

lemma connected_set_of_vertices_quot_iff:
  assumes "X \<subseteq> s" "Y \<subseteq> s"
  shows "X \<longleftrightarrow>\<^bsub>quot_graph P E - {{u}}\<^esub> Y \<longleftrightarrow> X \<longleftrightarrow>\<^bsub>E\<^esub> Y"
  apply (auto simp add: connected_set_of_vertices_def)
  using assms(1,2) edge_in_quot_in_graph_1' apply blast
  using assms(1,2) edge_in_quot_in_graph_1' apply blast
  subgoal for ua v
    using assms
    apply(auto intro!: exI[of _ ua, OF exI[of _ v]] )
    by (metis (lifting) Diff_iff edge_in_s_in_quotG empty_subsetI insert_subset subset_eq)
  done

lemma in_quotG_subset_E: 
  "\<lbrakk>e \<in> quotG G; G \<subseteq> E; 
    \<And> ua va. \<lbrakk>e = {ua, va}; ua \<noteq> va; {ua, va} \<subseteq> s; e \<in> G; e \<noteq> {u}; P ` {ua, va} = e\<rbrakk> \<Longrightarrow> Q;
     \<And> va ua. \<lbrakk>e = {u, va}; va \<in> s; ua \<notin> s; {ua, va} \<in> G; ua \<noteq> va; e \<noteq> {u}; P ` {ua, va} = e\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
proof(goal_cases)
  case 1
  then obtain e' where e':  "e' \<in> E" "e = P ` e'" "e \<noteq> {u}"  "e' \<in> G"
    by(auto simp add: quot_graph_def)
  then obtain ua va where uava: "e' = {ua, va}" "ua \<noteq> va"
    by (auto elim!: dblton_graphE)
  show ?case
  proof(cases "{ua, va} \<subseteq> s")
    case True
    hence "e = e'"
      by (simp add: e'(2) uava(1))
    then show ?thesis 
      using True uava e'(4)
      by(auto intro!: 1(3)[of ua va])
  next
    case False
    then obtain ua va where uava: "e' = {ua, va}" "ua \<noteq> va" "ua \<notin> s" "va \<in> s"
      using e'(2,3) uava(1) by auto
    then show ?thesis 
      using e' by(auto intro!: 1(4)[of va ua])
  qed
qed

lemma in_quotGE: 
  "\<lbrakk>e \<in> quotG E; \<And> ua va. \<lbrakk>e = {ua, va}; ua \<noteq> va; {ua, va} \<subseteq> s; e \<in> E; e \<noteq> {u}; P ` {ua, va} = e\<rbrakk> \<Longrightarrow> Q;
     \<And> va ua. \<lbrakk>e = {u, va}; va \<in> s; ua \<notin> s; {ua, va} \<in> E; ua \<noteq> va; e \<noteq> {u}; P ` {ua, va} = e\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
proof(goal_cases)
  case 1
  then obtain e' where e':  "e' \<in> E" "e = P ` e'" "e \<noteq> {u}"
    by(auto simp add: quot_graph_def)
  then obtain ua va where uava: "e' = {ua, va}" "ua \<noteq> va"
    by (auto elim!: dblton_graphE)
  show ?case
  proof(cases "{ua, va} \<subseteq> s")
    case True
    hence "e = e'"
      by (simp add: e'(2) uava(1))
    then show ?thesis 
      using True uava e'(1)
      by(auto intro!: 1(2)[of ua va])
  next
    case False
    then obtain ua va where uava: "e' = {ua, va}" "ua \<noteq> va" "ua \<notin> s" "va \<in> s"
      using e'(2,3) uava(1) by auto
    then show ?thesis 
      using e' by(auto intro!: 1(3)[of va ua])
  qed
qed

lemma in_quot_graphE: 
  "\<lbrakk>e \<in> quot_graph P E; \<And> ua va. \<lbrakk>e = {ua, va}; ua \<noteq> va; {ua, va} \<subseteq> s; e \<in> E; e \<noteq> {u}; P ` {ua, va} = e\<rbrakk> \<Longrightarrow> Q;
     \<And> va ua. \<lbrakk>e = {u, va}; va \<in> s; ua \<notin> s; {ua, va} \<in> E; ua \<noteq> va; e \<noteq> {u}; P ` {ua, va} = e\<rbrakk> \<Longrightarrow> Q;
     \<And> ua va. \<lbrakk>e = {u}; {ua, va} \<inter> s = {}; {ua, va} \<in> E; P ` {ua, va} = e\<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
proof(goal_cases)
  case 1
  then obtain e' where e':  "e' \<in> E" "e = P ` e'" 
    by(auto simp add: quot_graph_def)
  then obtain ua va where uava: "e' = {ua, va}" "ua \<noteq> va"
    by (auto elim!: dblton_graphE)
  show ?case
  proof(cases "{ua, va} \<subseteq> s")
    case True
    hence "e = e'"
      by (simp add: e'(2) uava(1))
    then show ?thesis 
      using True uava e'(1)
      by(auto intro!: 1(2)[of ua va])
  next
    case False
    note false = this
    show ?thesis
    proof(cases "{ua, va} \<inter> s = {}")
      case True
      hence "e = {u}"
        by (simp add: e'(2) uava(1))
      then show ?thesis
        using True e'(1) uava(1) 
        by(auto intro!: 1(4)[of ua va])
    next
      case False
      hence e_neq_u: "e \<noteq> {u}" 
        using  e'(2) good_quot_map(1) uava(1) by auto
     obtain ua va where uava: "e' = {ua, va}" "ua \<noteq> va" "ua \<notin> s" "va \<in> s"
      using e'(2) e_neq_u  uava(1) false False by auto
    then show ?thesis 
      using e' e_neq_u by(auto intro!: 1(3)[of va ua])
  qed
qed
qed

lemma connected_set_of_vertices_quot_iff_u:
  assumes "u \<in> X" "Y \<subseteq> s" 
  shows "X \<longleftrightarrow>\<^bsub>quotG E\<^esub> Y \<longleftrightarrow> X - {u} \<union> (Vs E - s) \<longleftrightarrow>\<^bsub>E\<^esub> Y"
proof(rule, goal_cases)
  case 1
  then obtain ua va where "{ua, va} \<in> quotG E" "ua \<in> X" "va \<in> Y"
    by(auto simp add: connected_set_of_vertices_def)
  then show ?case 
  proof(elim in_quotGE, goal_cases)
    case (1 uaa vaa)
    then obtain uaa vaa where  "uaa \<in> X - {u}" "vaa \<in> Y" "{uaa, vaa} \<in> E"
      using good_quot_map(1) by(auto simp add: doubleton_eq_iff)
    then show ?case 
      by(auto simp add: connected_set_of_vertices_def)
  next
    case (2 y x)
    hence unfolds: "ua = u" "va = y"
      using assms(2) good_quot_map(1)
      by(auto simp add: doubleton_eq_iff)
    note 2 = 2[simplified unfolds]
    hence "x \<in> Vs E - s"
      by blast
    thus ?thesis
      using 2
      by(auto intro!: exI[of _ x, OF exI[of _ y]] 
            simp add: connected_set_of_vertices_def)
  qed
next
  case 2
  then obtain x y where xy: "{x, y} \<in> E" "x \<in> X - {u} \<union> (Vs E - s)" "y \<in> Y"
    by(auto simp add: connected_set_of_vertices_def)
  then show ?case 
  proof(cases "x \<in> (Vs E - s)", goal_cases)
    case 1
    have "{y, u} \<in> quotG E"
      using assms(2) xy(3)  "1"(4) 
      by(intro edge_in_graph_edge_in_quot[where w = x])
        (auto simp add: insert_commute xy(1))
    then show ?case
      using assms(1) 1(3)
      by(auto intro!: exI[of _ u, OF exI[of _ y]]  
          simp add: connected_set_of_vertices_def insert_commute)
  next
    case 2
    hence x_in_s:"x \<in> s"
      by blast
    hence "{x, y} \<in> quotG E"
      using 2 assms(2) 
      by (intro edge_in_s_then_in_quotG) auto
    then show ?case 
      using 2
      by(auto simp add: connected_set_of_vertices_def)
  qed
qed

lemma u_in_X_Neighbourhood_expanded:
  assumes "u \<in> X"
  shows "Neighbourhood (quotG E) X = Neighbourhood E (X - {u} \<union> (Vs E - s))"
proof(rule, all \<open>rule, elim in_NeighbourhoodE\<close>, goal_cases)
  case (1 x y)
  then show ?case 
  proof(elim in_quotGE, goal_cases)
    case (1 ua va)
    then show ?case 
       using good_quot_map(1)
       by(auto intro: in_NeighbourhoodI[of ua va]  in_NeighbourhoodI[of va ua] 
            simp add: doubleton_eq_iff in_NeighbourhoodI)
  next
    case (2 va ua)
    hence "u \<in> Vs (quotG E)"
      using "1"(1) by auto
    thus ?case
      using 2 assms 
      by (auto simp add: doubleton_eq_iff  edges_are_Vs in_NeighbourhoodI)
  qed
next
  case (2 x y)
    then show ?case 
      using  good_quot_map(1) assms(1) apply auto
      apply (smt (verit, ccfv_threshold) edge_in_graph_edge_in_quot edge_in_s_then_in_quotG empty_subsetI
          in_NeighbourhoodI insert_commute insert_subset)
      by (metis (lifting) doubleton_eq_iff edge_in_graph_edge_in_quot in_NeighbourhoodI)
  qed

lemma u_not_in_subgraph_same_subgraph:
  assumes "u \<notin> X"  "X \<subseteq> Vs (quotG E)" "G \<subseteq> E"
  shows "(quotG G) \<lbrakk>X\<rbrakk> = G \<lbrakk>X\<rbrakk>"
proof(rule, all \<open>rule, elim in_graph_inter_VsE\<close>, goal_cases)
  case (1 e)
  thus ?case
  proof(elim in_quotG_subset_E[OF _ assms(3)], goal_cases)
    case (1 ua va)
    then show ?case
      by(auto intro!: in_graph_inter_VsI)
  next
    case (2 va ua)
    then show ?case 
      using assms by auto
  qed
next
  case (2 e)
  then obtain x y where xy: "e = {x, y}" "x \<noteq> y" "{x, y} \<in> G"
    using assms(3) by force
  hence "e \<subseteq> s" 
    using 2  assms(1,2) neq_u_notin_quotG by auto
  then show ?case
  proof(intro  in_graph_inter_VsI, goal_cases)
    case 1
    then show ?case
      using 2 assms(1) 
      by(auto intro!: bexI[of _ e] simp add: quot_graph_def)
  qed (simp add: 2)
qed

end

subsection \<open>Even Vertices and Blossoms\<close>

definition 
  "even_vert G M v = (\<exists> p. odd (length p)\<and>
     alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p) \<and> 
     hd p \<notin> Vs M \<and> last p = v \<and> distinct p \<and> (path G p \<or> length p = 1))"

lemma  even_vertI: 
  "\<lbrakk>odd (length p); alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p);
    hd p \<notin> Vs M; last p = v; distinct p; path G p \<or> length p = 1\<rbrakk> \<Longrightarrow> even_vert G M v"
 and even_vertE: 
  "even_vert G M v \<Longrightarrow> 
   (\<And>p. \<lbrakk> odd (length p); alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p); 
          hd p \<notin> Vs M; last p = v; distinct p; path G p \<or> length p = 1\<rbrakk> \<Longrightarrow> R) \<Longrightarrow> R"
 and even_vertD:
  "even_vert G M v \<Longrightarrow> \<exists>p. odd (length p) \<and> alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p) \<and> 
                           hd p \<notin> Vs M \<and> last p = v \<and> distinct p \<and> (path G p \<or> length p = 1)"
  unfolding even_vert_def by auto

definition "even_verts G M = {u | u. even_vert G M u}"

definition "even_alt_path G M s p t =
         ((path G p \<or> length p = 1) \<and> alt_path M p \<and> 
          hd p = s \<and> last p = t \<and>
          odd (length p) \<and> s \<notin> Vs M \<and> distinct p)"

lemma even_alt_pathE:
"\<lbrakk>even_alt_path G M s p t;
  (\<lbrakk>path G p \<or> length p = 1; alt_path M p; p \<noteq> []; hd p = s; last p = t;
    odd (length p); s \<notin> Vs M; distinct p \<rbrakk> \<Longrightarrow> P)\<rbrakk> \<Longrightarrow> P"
and even_alt_pathI:
"(\<lbrakk>path G p \<or> length p = 1; alt_path M p;  hd p = s; last p = t;
    odd (length p); s \<notin> Vs M; distinct p \<rbrakk> \<Longrightarrow> even_alt_path G M s p t) "
  by(cases p)(auto simp add: even_alt_path_def)

lemma even_vert_even_alt_path:
  "even_vert G M v \<longleftrightarrow> (\<exists> u p. (even_alt_path G M u p v))"
proof(rule, all \<open> elim even_vertE | elim exE, elim even_alt_pathE\<close>, goal_cases)
  case (1 p)
  then show ?case
    by(auto intro!: even_alt_pathI exI)
next
  case (2 u p)
  then show ?case 
    by(cases p rule: rev_cases)(auto intro!: even_vertI)
qed

lemma blossom_verts_are_even:
  assumes  "blossom G M stem C" 
  shows "set C \<subseteq> even_verts G M \<inter> Vs G"
proof(rule, goal_cases)
  case (1 x)
  note assms_rev = flower_reverse_blossom[OF assms(1)]
  note blossomD_rev = blossomD[OF assms_rev]
  note match_blossomD_rev = match_blossomD[OF blossomD(2)]
  note blossomD = blossomD[OF assms(1)]
  note match_blossomD = match_blossomD[OF blossomD(2)]

  obtain i where i: "C ! i = x" "i + 1 < length C"
    using 1 match_blossomD(3) 
     by(cases "x = last C", all \<open>cases C rule: rev_cases\<close>)
       (force elim!:list_cases2_both_sides simp add: odd_cycle_def in_set_conv_nth nth_append)+
   then obtain C1 C2 where C1C2: "C = C1 @[x]@C2" "C2 \<noteq> []" "length C1 = i"
     using id_take_nth_drop[of i C] by auto

   show ?case
   proof(cases "even i")
     case True
     moreover have "odd (length (stem @ C1 @ [x]))"
       using  C1C2(3) True  match_blossomD(5) edges_of_path_length'[of "stem @ [hd C]"]
       by auto
     moreover have "alt_path M (stem @ C1 @ [x])"
       using match_blossomD(1)
       by(simp add: C1C2(1) alt_path_prefix)
     moreover have "hd (stem @ C1 @ [x]) \<notin> Vs M" 
       using match_blossomD(4) 
       by (auto simp add: C1C2(1) hd_append[of "_ @ _" "_ # _", simplified])
     moreover have "distinct (stem @ C1 @ [x])" 
       using match_blossomD(2)
       by(auto simp add: C1C2(1) butlast_append C1C2(2))
     moreover have "path G (stem @ C1 @ [x]) \<or> length (stem @ C1 @ [x]) = 1"
       using C1C2(1) blossomD(1) path_pref[of G "(stem @ C1) @ [x]" C2] by auto
     moreover have "x \<in> Vs G" 
       using "1" local.blossomD(1) mem_path_Vs by fastforce
     ultimately show ?thesis 
       by(auto intro!: even_vertI[where p = "stem@C1 @[x]"] simp add: even_verts_def)
   next
     case False
     hence  C1C2_rev: "rev C = rev C2 @[x]@ rev C1" "C1 \<noteq> []" "even (length C2)"
       using C1C2 False match_blossomD(3) odd_cycle_even_verts by force+
     moreover have "odd (length (stem @ rev C2 @ [x]))"
       using  C1C2_rev(3) match_blossomD(5) edges_of_path_length'[of "stem @ [hd C]"]
       by auto
     moreover have "alt_path M (stem @ rev C2 @ [x])" 
       using calculation(1) blossomD_rev(2)
         Graph_Quotient.match_blossomD(1)[of M stem "(rev C2 @ [x]) @ rev C1"]
         alt_path_prefix[of M "stem @ rev C2 @ [x]" "rev C1"]
       by auto
     moreover have "hd (stem @ rev C2 @ [x]) \<notin> Vs M" 
       using match_blossomD(3,4) C1C2(2) calculation(1) hd_rev[of C] 
         odd_cycleD(3)[of C] hd_append2[of stem C] hd_append2[of stem "rev C2 @ [x]"]
       by fastforce
     moreover have "distinct (stem @ rev C2 @ [x])"
       using calculation(2) C1C2(1) List.butlast_rev[of "C1 @ x # C2"] assms_rev  
         Graph_Quotient.match_blossomD(2)[of M stem "rev (C1 @ x # C2)"]
       by auto
     moreover have "path G (stem @ rev C2 @ [x]) \<or> length (stem @ rev C2 @ [x]) = 1"
       using blossomD_rev(1) calculation(1) path_pref[of G "stem @ rev C2 @ [x]" "rev C1"]
       by auto
     moreover have "x \<in> Vs G" 
       using "1" local.blossomD(1) mem_path_Vs by fastforce
     ultimately show ?thesis 
       by(auto intro!: even_vertI[where p = "stem@ rev C2 @[x]"] 
             simp add: even_verts_def)
   qed
 qed

lemma blossom_verts_even_alt_path:
  assumes  "blossom G M stem C" "x \<in> set C"
  shows "\<exists> p s. even_alt_path G M s p x"
  using blossom_verts_are_even[OF assms(1)] assms(2)
  by(auto simp add: even_verts_def even_vert_def even_alt_path_def)


context quot
begin

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
    by (auto intro!: matching_augmenting_pathI alt_list_append_3 alt_list_singleton
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
        using match_blossom match_blossomD(3)  match_blossom_alt_cycle 
              distinct_tl  match_blossom path_suff  aupath_old  M_props(1,2) quot(1) 
       by (intro refine)fastforce+
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

theorem even_vertex_blossom_contraction:
  assumes  "blossom E M stem C" "even_vert E M x" "x \<in> Vs E"
           "max_card_matching E M"
           "s = (Vs E) - set C" "u \<notin>  Vs E"  "u' \<notin> Vs E" "u' \<noteq> u" 
     shows "even_vert (quotG E) (quotG M) (P x)"
proof-
  obtain start p where start_p: "even_alt_path E M start p x"
    using assms(2) by(auto simp add: even_vert_even_alt_path)
  have iffy:"P x = (if x \<notin> Vs E then x else if x \<notin> s then u else x)"
    using assms(3) by auto
  have "x \<noteq> u"
    using assms(3,6) by auto
  then obtain start' p' where
     "even_alt_path (quotG E) (quotG M) start' p' (P x)"
    using reachbale_by_even_alt_path_contraction[OF assms(1) start_p(1) assms(4,5,6,7,8)iffy ]
    by auto
  thus ?thesis
    by(auto intro!: exI simp add: even_vert_even_alt_path)
qed

theorem even_vertices_blossom_contraction:
  assumes  "blossom E M stem C" 
           "max_card_matching E M"
           "s = (Vs E) - set C" "u \<notin>  Vs E"  "u' \<notin> Vs E" "u' \<noteq> u" 
     shows "even_verts (quotG E) (quotG M) \<supseteq> P ` (even_verts E M \<inter> Vs E) "
proof-
  have "even_vert (quotG E) (quotG M) x" 
    if "x \<in> s" "x \<in> Vs E" "even_vert E M x" for x
  proof-
      note again_even =
       even_vertex_blossom_contraction[OF assms(1) _ _ assms(2,3,4,5,6), of x, simplified if_P[OF that(1)]]
      show ?thesis 
        using that assms(3) 
        by (intro again_even)
    qed
    moreover have "even_vert (quotG E) (quotG M) u" if
           "x \<in> Vs E" "x \<notin> s" "even_vert E M x" for x
  proof-
      note again_even =
       even_vertex_blossom_contraction[OF assms(1) _ _ assms(2,3,4,5,6), of x, simplified if_not_P[OF that(2)]]
      show ?thesis 
        using that assms
        by (intro again_even) auto
    qed
  ultimately show ?thesis
    by(auto simp add: even_verts_def)
qed
end

subsection \<open>Blossoms and the Decomposition\<close>

definition "pre_edmonds_gallai G M \<D> = 
  (disjoint \<D> \<and> \<Union> \<D> \<subseteq> Vs G \<and> (\<forall> X \<in> \<D>. X \<noteq> {}) \<and> 
    (\<forall> X Y. X \<in> \<D> \<and> Y \<in> \<D> \<and> X \<noteq> Y \<longrightarrow> (X \<leftarrow>|\<rightarrow>\<^bsub>G\<^esub> Y)) \<and>
  card \<D> > card (Neighbourhood G (\<Union> \<D>)) \<and>
  (\<forall> X x. X \<in> \<D> \<and>  x \<in> X \<longrightarrow> (\<exists> M. graph_matching (G \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x})) \<and>
   (\<forall> v \<in> Vs G. even_vert G M v \<longrightarrow> v \<in> \<Union> \<D>))"

lemma pre_edmonds_gallaiI:
  "\<lbrakk> disjoint \<D>; 
     \<Union> \<D> \<subseteq> Vs G; 
     (\<And>X. X \<in> \<D> \<Longrightarrow> X \<noteq> {}); 
     (\<And>X Y. \<lbrakk>X \<in> \<D>; Y \<in> \<D>; X \<noteq> Y\<rbrakk> \<Longrightarrow> X \<leftarrow>|\<rightarrow>\<^bsub>G\<^esub> Y); 
     card \<D> > card (Neighbourhood G (\<Union> \<D>));
     (\<And>X x. \<lbrakk>X \<in> \<D>; x \<in> X\<rbrakk> \<Longrightarrow> \<exists>M. graph_matching (G \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x});
     (\<And>v. \<lbrakk>v \<in> Vs G; even_vert G M v\<rbrakk> \<Longrightarrow> v \<in> \<Union> \<D>) \<rbrakk> 
  \<Longrightarrow> pre_edmonds_gallai G M \<D>"
  unfolding pre_edmonds_gallai_def by auto

lemma pre_edmonds_gallaiE:
  "\<lbrakk>pre_edmonds_gallai G M \<D>;
    \<lbrakk> disjoint \<D>; 
     \<Union> \<D> \<subseteq> Vs G; 
     (\<And>X. X \<in> \<D> \<Longrightarrow> X \<noteq> {}); 
     (\<And>X Y. \<lbrakk>X \<in> \<D>; Y \<in> \<D>; X \<noteq> Y\<rbrakk> \<Longrightarrow> X \<leftarrow>|\<rightarrow>\<^bsub>G\<^esub> Y); 
     card \<D> > card (Neighbourhood G (\<Union> \<D>));
     (\<And>X x. \<lbrakk>X \<in> \<D>; x \<in> X\<rbrakk> \<Longrightarrow> \<exists>M. graph_matching (G \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x});
     (\<And>v. \<lbrakk>v \<in> Vs G; even_vert G M v\<rbrakk> \<Longrightarrow> v \<in> \<Union> \<D>) \<rbrakk> \<Longrightarrow> P\<rbrakk>  
    \<Longrightarrow> P"
  unfolding pre_edmonds_gallai_def by auto

lemma pre_edmonds_gallaiD:
 "pre_edmonds_gallai G M \<D> \<Longrightarrow> disjoint \<D>"
 "pre_edmonds_gallai G M \<D> \<Longrightarrow> \<Union> \<D> \<subseteq> Vs G"    
 "\<lbrakk>pre_edmonds_gallai G M \<D>;  X \<in> \<D>\<rbrakk> \<Longrightarrow> X \<noteq> {}"
 "\<lbrakk>pre_edmonds_gallai G M \<D>; X \<in> \<D>; Y \<in> \<D>; X \<noteq> Y\<rbrakk> \<Longrightarrow> X \<leftarrow>|\<rightarrow>\<^bsub>G\<^esub> Y"
 "pre_edmonds_gallai G M \<D> \<Longrightarrow> card \<D> > card (Neighbourhood G (\<Union> \<D>))"
 "\<lbrakk>pre_edmonds_gallai G M \<D>; X \<in> \<D>; x \<in> X\<rbrakk> \<Longrightarrow> \<exists>M. graph_matching (G \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x}"
 "\<lbrakk>pre_edmonds_gallai G M \<D>; v \<in> Vs G; even_vert G M v\<rbrakk> \<Longrightarrow> v \<in> \<Union> \<D>"
  unfolding pre_edmonds_gallai_def by auto

lemma odd_cycle_graph_near_perfect_matching:
  assumes "dblton_graph G" "odd_cycle p" "set p = Vs G" "distinct (butlast p)" "path G p"
  shows "\<exists> M. graph_matching G M \<and> Vs M = set p - {hd p}"
proof-
  define M where "M = {edges_of_path (butlast p) ! i | i. 0 \<le> i \<and> i + 1 <length (butlast p) \<and> odd i}"
  have path_butlast: "path G (butlast p)" 
    using assms(2,5) odd_cycle_nempty[of "[]"] append_butlast_last_id[of p]
      path_pref[of G "butlast p" "[last p]"]
    by fastforce
  show ?thesis
  proof(rule exI[of _ M], goal_cases)
    case 1
    then show ?case
    proof(rule, goal_cases)
      case 1
      then show ?case
      proof(rule graph_matchingI, goal_cases)
        case 1
        then show ?case
          using assms(4)
          by(auto intro!: odd_edges_of_distinct_path_are_matching[of "butlast _", simplified]
                simp add: M_def)
      next
        case 2
        then show ?case
          unfolding M_def
        proof(rule, goal_cases)
          case (1 e)
          then obtain i where "e = edges_of_path (butlast p) ! i"
            "0 \<le> i" "i + 1 < length (butlast p)" "odd i"
            by auto
          hence "e \<in> set (edges_of_path (butlast p))"
            by (simp add: edges_of_path_length)
          moreover have " set (edges_of_path (butlast p)) \<subseteq>  set (edges_of_path p)"
            using assms(2) edges_of_path_append_subset_2[of "butlast p" "[last p]"]
                 append_butlast_last_id[of p]
            by fastforce
          moreover have " set (edges_of_path p) \<subseteq> G"
            by (simp add: assms(5) path_edges_subset)
          ultimately show ?case
            by auto
        qed
      qed
    next
      case 2
      have len_rw:"{edges_of_path (butlast p) ! i |i. 0 \<le> i \<and> i + 1 < length (butlast p) \<and> odd i} =
            {edges_of_path (butlast p) ! i |i. i < length (butlast p) - 1 \<and> odd i}"
        by auto
      have Vs_M_rw: "Vs M = set (butlast (tl p))"
        unfolding M_def len_rw verts_of_odd_edges[of "butlast p"]
        by (auto simp add: assms(2) odd_cycle_even_verts odd_cycle_nempty butlast_tl)
      have p_unfold: "p = hd p # butlast (tl p) @[last p]"
        using assms(2) odd_cycleD(2) odd_cycle_nempty
        by(cases p rule: list_cases3) fastforce+
      hence "hd p \<notin> set (butlast (tl p))" 
        using assms(4) snoc_eq_iff_butlast[of "hd p # butlast (tl p)"
                 "last p" "(hd p # butlast (tl p)) @ [last p]"]
             by simp
     thus ?case
        unfolding Vs_M_rw
        by(subst (2) p_unfold)(auto simp add: assms(2) odd_cycleD(3))
    qed
  qed
qed

lemma odd_cycle_graph_factor_critical:
  assumes "dblton_graph G" "odd_cycle p" "set p = Vs G" "distinct (butlast p)"
          "path G p" "x \<in> Vs G"
    shows "\<exists> M. graph_matching G M \<and> Vs M = Vs G - {x}"
proof(cases "x = hd p")
  case True
  then show ?thesis 
    using odd_cycle_graph_near_perfect_matching[OF assms(1,2,3,4,5)] assms(3) 
    by auto
next
  case False
  obtain p1 p2 where p1p2: "p = [hd p]@p1@[x]@p2@[hd p]"
    using False assms(2,3,6) odd_cycleD(3)[of p] split_list_last[of x] 
    by(cases p rule: list_cases_hd_and_last)(force simp add: assms(2) odd_cycle_nempty)+
  have same_length: "length ([x] @ p2 @ [hd p] @ p1 @ [x]) = length p"
    by(subst (2) p1p2) auto
  have new_oc:"odd_cycle ([x] @ p2 @ [hd p] @ p1 @ [x])"
    unfolding odd_cycle_def edges_of_path_length same_length
    by (auto simp add: assms(2) odd_cycleD odd_cycle_nempty odd_cycle_even_verts)
  have distinct_new_oc:"distinct (butlast ([x] @ p2 @ [hd p] @ p1 @ [x]))" 
    using  assms(4) 
    by(subst (asm) p1p2)(auto simp add: butlast_snoc[of "_ @ _ # _", simplified] False)
  have new_path:"path G ([x] @ p2 @ [hd p] @ p1 @ [x])"
    using p1p2 assms(5)
    by(auto intro!: path_concat_2[of G "[x]@p2@[hd p]" "[hd p] @ p1 @ [x]", simplified]
                    path_pref[of G "[hd p]@p1@[x]" "p2@[hd p]", simplified]
                    path_suff[of G "[hd p]@p1" "[x]@p2@[hd p]", simplified])
  have set_Vs:"set ([x] @ p2 @ [hd p] @ p1 @ [x]) = Vs G"
    using assms(2,3) p1p2 by(cases p)(auto simp add: assms(6)  odd_cycle_nempty)
  hence "insert (hd p) (insert x (set p2 \<union> set p1)) =  Vs G"
    by auto
  thus ?thesis
    using odd_cycle_graph_near_perfect_matching[OF
             assms(1) new_oc set_Vs distinct_new_oc new_path, simplified]
    by simp
qed

context quot
begin

lemma pre_emonds_gallai_lonely_blossom:
  assumes assumptions: "pre_edmonds_gallai (quotG E) (quotG M) \<D>"
          "Delta E (set C) = {}"  "s = Vs E - set C" "blossom E M stem C"
           "max_card_matching E M" "u \<notin> Vs E" "u' \<notin> Vs E" "u' \<noteq> u"
  shows  "pre_edmonds_gallai E M (insert (set C) \<D>)"
proof-
  have assms:  "pre_edmonds_gallai (quotG E) (quotG M) \<D>"
          "Delta E (set C) = {}"  "distinct (butlast C)"  "odd_cycle C"
          "s = Vs E - set C" "path E C"
    using assms(1-4) distinct_append match_blossomD(2,3) path_suff' by auto
  have quot_Vs_are:"Vs (quot_graph P E - {{u}}) = s"
    using assms(2,5,6) subset_path_Vs[of E C] double_diff[of "set C" "Vs E" "Vs E"]
    by (intro Delta_wth_s_empty_quot_Vs) auto
  note pre_edmonds_gallaiD = pre_edmonds_gallaiD[OF assms(1), simplified quot_Vs_are]
  have p_in_E:"set C \<subseteq> Vs E"
    by (simp add: assms(6) subset_path_Vs)
  have goal1: "disjoint (insert (set C) \<D>)"
    using assms(5) pre_edmonds_gallaiD(1,2) 
    by(auto intro!: disjointI simp add: disjoint_def)
  have goal2: "\<Union> (insert (set C) \<D>) \<subseteq> Vs E"
    using p_in_E good_quot_map(2) pre_edmonds_gallaiD(2) by auto
  have goal3: "X \<in> insert (set C) \<D> \<Longrightarrow> X \<noteq> {}" for X
    using assms(4) pre_edmonds_gallaiD(3) odd_cycle_nempty by auto

  have goal4_helper: "X \<leftarrow>|\<rightarrow>\<^bsub> E \<^esub> Y"
    if "X \<in> \<D>" "Y \<in> \<D>" "X \<noteq> Y" for X Y
    using local.pre_edmonds_gallaiD(2,4) that 
    by (subst connected_set_of_vertices_quot_iff[symmetric]) auto
  have goal4: "\<lbrakk>X \<in> insert (set C) \<D>; Y \<in> insert (set C) \<D>\<rbrakk> \<Longrightarrow> X \<noteq> Y \<Longrightarrow> X \<leftarrow>|\<rightarrow>\<^bsub>E\<^esub> Y" for X Y
  proof(elim insertE, goal_cases)
    case 2
    then show ?case 
      using disjointD goal1 assms(2) 
      by (intro empty_Delta_disconnected) auto
  next
    case 3
    then show ?case 
      using disjointD goal1 assms(2) 
      by (subst connected_sym, intro empty_Delta_disconnected) auto
  next
    case 4
    then show ?case 
      using goal4_helper by simp
  qed simp

  have u_not_in_D:"u \<notin> \<Union> \<D>" 
    by (metis good_quot_map(1) local.pre_edmonds_gallaiD(2) subsetD)
  have finite_D: "finite \<D>" 
    by (metis finite_UnionD finite_insert goal2 graph infinite_super)

  have goal5: "card (Neighbourhood E (\<Union> (insert (set C) \<D>))) < card (insert (set C) \<D>)"
  proof-

    have rw1: "Neighbourhood (quotG E) (\<Union> \<D>) = 
           Neighbourhood (quotG E) (insert u (\<Union> \<D>))"
      using good_quot_map(1) quot_Vs_are 
      by (intro Neighbourhood_of_one_more_same_if_nin_Vs[symmetric]) blast
    have rw2: "... = Neighbourhood E (\<Union> (insert (set C) \<D>))"
      apply(subst u_in_X_Neighbourhood_expanded)
      using u_not_in_D assms(5) p_in_E 
      by (intro insertI1  arg_cong[where f = "Neighbourhood E"])+ auto
   show ?thesis
     using pre_edmonds_gallaiD(5) finite_D  card_insert_le[of \<D> "set C"]
     unfolding rw1 rw2 by auto
 qed

  have Vs_E_on_p_are_p:"Vs (E \<lbrakk>set C\<rbrakk>) = set C"
    using assms(4,6) 
    by(intro Vs_of_graph_inter_path)(auto simp add: odd_cycle_def)
  have length_p_geq_2: "2 \<le> length C"
    using assms(4) odd_cycle_length_verts_ge_4 by fastforce

  have "\<lbrakk>X \<in> \<D>; x \<in> X\<rbrakk> \<Longrightarrow> \<exists>M. graph_matching ( E \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x}" for X x
    using pre_edmonds_gallaiD(6)[of X x] u_not_in_D  local.pre_edmonds_gallaiD(2) quot_Vs_are
    by(subst (asm) u_not_in_subgraph_same_subgraph) auto
  moreover have "x \<in> set C \<Longrightarrow> \<exists>M. graph_matching ( E \<lbrakk>set C\<rbrakk>) M \<and> Vs M = set C - {x}" for x
  proof(goal_cases)
    case 1
    have "\<exists>M. graph_matching (E \<lbrakk>set C\<rbrakk>) M \<and> Vs M = Vs (E \<lbrakk>set C\<rbrakk>) - {x}"
      apply(rule odd_cycle_graph_factor_critical[of "E \<lbrakk>set C\<rbrakk>" C x])
      using p_in_E  1 length_p_geq_2
      by (auto intro!: path_on_graph_inter_path
             simp add: dblton_E assms(3,4,6) graph graph_invar_graph_inter_Vs Vs_E_on_p_are_p)
    then show ?case 
      unfolding Vs_E_on_p_are_p by simp
  qed
  ultimately have goal6:
    "\<lbrakk>X \<in> insert (set C) \<D>; x \<in> X\<rbrakk> \<Longrightarrow> \<exists>M. graph_matching ( E \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x}" for X x
    by auto

  have goal7: "\<lbrakk>v \<in> Vs E; even_vert E M v\<rbrakk> \<Longrightarrow> v \<in> \<Union> (insert (set C) \<D>)" for v
  proof(cases "v \<in> set C", goal_cases)
    case 1
    then show ?thesis
      by auto
  next
    case 2
    hence v_still_there:"P v = v"
      using assumptions(3) by auto
    hence "even_vert (quotG E) (quotG M) v"
      using even_vertex_blossom_contraction[OF assumptions(4) 2(2,1) assumptions(5,3,6-8)]
      by simp
    moreover have "v \<in> Vs (quotG E)"
      using "2"(1) v_still_there assumptions(6) quot_Vs_are by presburger
    ultimately show ?thesis
      using pre_edmonds_gallaiD(7) quot_Vs_are by force
  qed
  
  show ?thesis
    by(intro pre_edmonds_gallaiI goal1 goal2 goal3 goal4 goal5 goal6 goal7) auto
qed

lemma pre_emonds_gallai_connected_blossom_obtain_D:
  assumes assumptions: "pre_edmonds_gallai (quotG E) (quotG M) \<D>"
          "Delta E (set C) \<noteq> {}"  "s = Vs E - set C" "blossom E M stem C"
          "max_card_matching E M" "u \<notin> Vs E" "u' \<notin> Vs E" "u' \<noteq> u"
  obtains D where "D \<in> \<D>" "u \<in> D"
proof(goal_cases)
  case 1
  note one = this

  obtain x where x: "x \<in> set C" 
    using assumptions(2) by(auto elim!: in_DeltaE)
  hence x_even: "even_vert E M x" and x_E: "x \<in> Vs E"
    using blossom_verts_are_even[OF assms(4)] 
    by(auto simp add: even_verts_def)
  have Delta_s_nempty:"Delta E s \<noteq> {}"
    unfolding Delta_s_Delta_compl_s_iff_empty
    using assumptions(2,3,4) subset_path_Vs[OF path_suff', of stem C]
    by (auto simp add: double_diff)
  have "P x = u"
    by (simp add: assumptions(3) x)
  hence "even_vert (quotG E) (quotG M) u"
    using even_vertex_blossom_contraction[OF assms(4) x_even x_E assms(5,3,6,7,8)]
    by auto
  moreover have "u \<in> Vs (quotG E)" 
    using assumptions(2) Delta_s_nempty
    by(auto dest!: s_not_in_quot_Delta_s_empty)
  ultimately obtain D where "D \<in> \<D>" "u \<in> D"
    using pre_edmonds_gallaiD(7)[OF assms(1), of u] 
    by auto
  thus thesis
    using 1 by auto
qed

lemma pre_emonds_gallai_connected_blossom:
  fixes D
  assumes assumptions: "pre_edmonds_gallai (quotG E) (quotG M) \<D>"
          "Delta E (set C) \<noteq> {}"  "s = Vs E - set C" "blossom E M stem C"
          "max_card_matching E M" "u \<notin> Vs E" "u' \<notin> Vs E" "u' \<noteq> u"
          "D \<in> \<D>" "u \<in> D"
    shows "pre_edmonds_gallai E M (\<D> - {D} \<union> {D - {u} \<union> set C})"
proof-
  have C_props: "C \<noteq> []" "length C \<ge> 2" "length C \<ge> 3"  "length C \<ge> 1"
    using assumptions(4)
    by (auto dest!: match_blossomD(3) simp add: odd_cycle_def  odd_cycle_nempty )

  note pre_edmonds_gallaiD = pre_edmonds_gallaiD[OF assms(1)]
  have Vs_without_s_is_C:"Vs E - s =  set C" 
    using  assumptions(3,4) subset_path_Vs[OF path_suff', of stem C]
    by(auto simp add: double_diff)
  have Vs_quotG_is: "Vs (quotG E) = insert u s"
    using assms(2)
    by(intro Delta_wth_s_nonempty_quot_Vs)(auto simp add: Vs_without_s_is_C)
  have C_inter_quot_empty: "set C \<inter> Vs  (quotG E) = {}"
    using Vs_quotG_is Vs_without_s_is_C assumptions(6) by auto

  have goal1: "disjoint (\<D> - {D} \<union> {D - {u} \<union> set C})"
  proof(rule disjointI, elim UnE, goal_cases)
    case (1 a b)
    then show ?case 
      using pre_edmonds_gallaiD(1) 
      by (auto simp add: disjoint_def)
  next
    case (2 X Y)
    hence "X \<inter> D = {}"
      using assumptions(9) pre_edmonds_gallaiD(1)
      by(auto simp add: disjoint_def)
    then show ?case
      using "2"(2,3) local.pre_edmonds_gallaiD(2) C_inter_quot_empty
      by auto
  next
    case (3 X Y)
    hence "Y \<inter> D = {}"
      using assumptions(9) pre_edmonds_gallaiD(1)
      by(auto simp add: disjoint_def)
    then show ?case
      using "3"(2,3) local.pre_edmonds_gallaiD(2) C_inter_quot_empty
      by auto
  qed simp

  have in_D_but_not_in_E_is_u:"\<lbrakk>x \<in> X; X \<in> \<D>; x \<notin> Vs E\<rbrakk> \<Longrightarrow> x = u" for x X
    using assumptions(3) local.pre_edmonds_gallaiD(2) neq_u_notin_quotG by blast
  have in_X_has_u_is_D: "\<lbrakk>u \<in> X; X \<in> \<D>\<rbrakk> \<Longrightarrow> X = D" for X 
    using  assumptions(10,9) local.pre_edmonds_gallaiD(1)
    by(auto simp add: disjoint_def)
  have in_d_but_not_in_E_is_u:"\<lbrakk>x \<in> D; x \<notin> Vs E\<rbrakk> \<Longrightarrow> x = u" for x
    by (simp add: assumptions(9) in_D_but_not_in_E_is_u)

  have goal2: "\<Union> (\<D> - {D} \<union> {D - {u} \<union> set C}) \<subseteq> Vs E"
    using pre_edmonds_gallaiD(2) in_D_but_not_in_E_is_u in_X_has_u_is_D 
    by(auto dest: in_d_but_not_in_E_is_u 
        simp add: Vs_without_s_is_C[symmetric])

  have goal3: "X \<in> \<D> - {D} \<union> {D - {u} \<union> set C} \<Longrightarrow> X \<noteq> {}" for X
    using C_props(1) pre_edmonds_gallaiD(3) by auto

  have X_neq_D_in_s: "X \<in> \<D> - {D} \<Longrightarrow> X \<subseteq> s" for X
    using  in_X_has_u_is_D pre_edmonds_gallaiD(2)
    by(auto simp add: Vs_quotG_is)

  have goal4: 
     "\<lbrakk>X \<in> \<D> - {D} \<union> {D - {u} \<union> set C}; Y \<in> \<D> - {D} \<union> {D - {u} \<union> set C}; X \<noteq> Y\<rbrakk> \<Longrightarrow> X \<leftarrow>|\<rightarrow>\<^bsub>E\<^esub> Y"
     for X Y
  proof(elim UnE, goal_cases)
    case 1
    then show ?case 
      using pre_edmonds_gallaiD(4)[of X Y] X_neq_D_in_s 
      by (subst (asm) connected_set_of_vertices_quot_iff) auto
  next
    case 2
    hence "D \<leftarrow>|\<rightarrow>\<^bsub>quot_graph P E - {{u}}\<^esub> X" 
      using assumptions(9) local.pre_edmonds_gallaiD(4) by force
    then show ?case 
      unfolding connected_sym[of X]
      using "2"(2,3) X_neq_D_in_s Vs_without_s_is_C 
      by(subst (asm) connected_set_of_vertices_quot_iff_u)
        (auto simp add: assumptions(10))
  next
    case 3
    hence "D \<leftarrow>|\<rightarrow>\<^bsub>quot_graph P E - {{u}}\<^esub> Y" 
      using assumptions(9) local.pre_edmonds_gallaiD(4) by force
    then show ?case 
      using "3"(2,3) X_neq_D_in_s Vs_without_s_is_C 
      by(subst (asm) connected_set_of_vertices_quot_iff_u)
        (auto simp add: assumptions(10))
  qed simp
  have rw_Union: "\<Union> \<D> - {u} \<union> (Vs E - s) = \<Union> (\<D> - {D} \<union> {D - {u} \<union> set C})"
    using Vs_without_s_is_C in_X_has_u_is_D assumptions(3,6,9) 
    by auto
  have rw_card: "card (\<D> - {D} \<union> {D - {u} \<union> set C}) = card \<D>"
    using X_neq_D_in_s assumptions(3,9) good_quot_map(2) 
    by (intro card_replace) auto
  have goal5: "card (Neighbourhood E (\<Union> (\<D> - {D} \<union> {D - {u} \<union> set C})))
              < card (\<D> - {D} \<union> {D - {u} \<union> set C})"
    using pre_edmonds_gallaiD(5) assumptions(10,9) rw_Union rw_card
    by (subst (asm) u_in_X_Neighbourhood_expanded) auto

  have dblton_quotE:"dblton_graph (quotG E)"
    by (simp add: doubleton_quot)
  have path_C: "path E C" 
    using assumptions(4) path_suff' by blast
  have more_C_props: "odd_cycle C" "set C = Vs ( E \<lbrakk>set C\<rbrakk>)" "path ( E \<lbrakk>set C\<rbrakk>) C"
    using match_blossomD(3) assumptions(4) C_props(2) path_C
    by(intro Vs_of_graph_inter_path[symmetric]  path_on_graph_inter_path | force)+
  hence distinct_C: "distinct (butlast C)"
    using assumptions(4) match_blossomD(2) by force
  have goal6:
    "\<lbrakk>X \<in> \<D> - {D} \<union> {D - {u} \<union> set C}; x \<in> X\<rbrakk> 
       \<Longrightarrow> \<exists>M. graph_matching ( E \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x}" for X x
  proof(elim UnE, goal_cases)
    case 1
    have quotG_X_rw: "(quot_graph P E - {{u}}) \<lbrakk>X\<rbrakk> =  E \<lbrakk>X\<rbrakk>"
      using "1"(2) X_neq_D_in_s good_quot_map(1) pre_edmonds_gallaiD(2) 
      by (intro u_not_in_subgraph_same_subgraph[of X]) auto
    show ?case
      using pre_edmonds_gallaiD(6)[of X x] 1
      by(auto simp add: quotG_X_rw)
  next
    case 2
    have X_is: "X = D - {u} \<union> set C" 
      using 2 by auto
    hence x_in:"x \<in> D - {u} \<union> set C"
      using 2 by auto
    then show ?case 
      unfolding X_is
    proof(elim UnE, goal_cases)
      case 1
      obtain Md where M: "graph_matching ((quotG E) \<lbrakk>D\<rbrakk>) Md" "Vs Md = D - {x}"
        using "1" assumptions(9) local.pre_edmonds_gallaiD(6) by force
      have Md_matches_u: "u \<in> Vs Md"
        using "1" M(2) assumptions(10) by blast
      have dblton_Md: "dblton_graph Md" 
        using M(1) dblton_quotE dblton_graph_Vs_inter by blast
      obtain up where up: "{u, up} \<in> Md" "u \<noteq> up"
        using dblton_Md Md_matches_u 
        by(auto elim!: Undirected_Set_Graphs.dblton_graphE 
             simp add: vs_member insert_commute)+
      have Md_without_u_edge_Vs_inter: "Md - {{u, up}} \<subseteq> (quotG E) \<lbrakk>D - {u}\<rbrakk>"
        using M(1) graph_inter_Vs_subset(1)  M(1,2) up(1)
              remove_matching_edge_Vs[of Md "{u, up}"]
        by (intro is_part_of_graph_inter_Vs) force+
      have quotG_D_without_u:"(quotG E) \<lbrakk>D - {u}\<rbrakk> = E \<lbrakk>D - {u}\<rbrakk>"
        using assumptions(9) local.pre_edmonds_gallaiD(2) 
        by(intro u_not_in_subgraph_same_subgraph) auto
      have Md_without_matching: "graph_matching (E \<lbrakk>D - {u}\<rbrakk>) (Md - {{u, up}})"
        using M(1) Md_without_u_edge_Vs_inter matching_delete quotG_D_without_u by blast
      have u_up_in_quot:"{u, up} \<in> quotG E"
        using M(1) in_graph_inter_VsE subset_eq up(1) by blast
      moreover have up_in_s:"up \<in> s" 
        using Vs_quotG_is edges_are_Vs_2 u_up_in_quot by blast
      ultimately obtain uc where uc: "{uc, up} \<in> E" "uc \<in> set C" 
        using edge_in_quotG_2'_doubleton[of up E] assumptions(3)
        by (auto  simp add: insert_commute)
      have "\<exists>M. graph_matching ( E \<lbrakk>set C\<rbrakk>) M \<and> Vs M = Vs ( E \<lbrakk>set C\<rbrakk>) - {uc}"
        using more_C_props distinct_C uc(2) 
        by (intro odd_cycle_graph_factor_critical[of "E \<lbrakk>set C\<rbrakk>" "C" uc])
           (auto simp add: dblton_E dblton_graph_Vs_inter)
      then obtain Mc where Mc: "graph_matching ( E \<lbrakk>set C\<rbrakk>) Mc" "Vs Mc = set C - {uc}"
        using more_C_props(2) by auto
      have Vs_Md_witht_up_is:"Vs (Md - {{u, up}}) = Vs Md - {u, up}"
        by (simp add: M(1) remove_matching_edge_Vs up(1))
      have C_inter_D_empty:"set C \<inter> D = {}"
        using C_inter_quot_empty assumptions(9) local.pre_edmonds_gallaiD(2) by auto
      have "matching (Md - {{u, up}} \<union> {{uc, up}} \<union> Mc)"
      proof(rule matching_vertex_disj_union, goal_cases)
        case 1
        then show ?case 
      proof(rule matching_vertex_disj_union, goal_cases)
        case 1
        then show ?case 
          using Md_without_matching by blast
      next
        case 2
        then show ?case 
          by (simp add: matching_singleton)
      next
        case 3
        then show ?case 
          using C_inter_D_empty uc(2)
          by(auto simp add: Vs_Md_witht_up_is Vs_of_edge M(2))
      qed
      next
        case 2
        then show ?case
          by (simp add: Mc(1))
      next
        case 3
        then show ?case
          using Vs_without_s_is_C up_in_s C_inter_D_empty 
          by(auto simp add: Vs_Md_witht_up_is M(2) vs_union vs_insert Mc(2))
      qed
      moreover have "Md - {{u, up}} \<union> {{uc, up}} \<union> Mc \<subseteq> E \<lbrakk>D - {u} \<union> set C\<rbrakk>"
      proof(rule is_part_of_graph_inter_Vs, goal_cases)
        case 1
        then show ?case 
          using Mc(1) Md_without_matching graph_inter_Vs_subset(1) uc(1) by fastforce
      next
        case 2
        thus ?case
        unfolding vs_union Mc(2) Vs_of_edge Vs_Md_witht_up_is M(2)
        using M(2) edges_are_Vs_2 up(1,2)  uc(2) 
        by fastforce
    qed
    ultimately have "graph_matching ( E \<lbrakk>D - {u} \<union> set C\<rbrakk>) (Md - {{u, up}} \<union> {{uc, up}} \<union> Mc)"
      by simp
    moreover have "Vs (Md - {{u, up}} \<union> {{uc, up}} \<union> Mc) = 
                   D - {u} \<union> set C - {x}"
      unfolding vs_union Mc(2) Vs_of_edge Vs_Md_witht_up_is M(2)
      using  uc(2) up(1,2) M(2) edges_are_Vs_2 "1" C_inter_D_empty 
      by fastforce
    ultimately show ?case 
      by auto
    next
      case 2
      obtain Md where M: "graph_matching ((quotG E) \<lbrakk>D\<rbrakk>) Md" "Vs Md = D - {u}"
        using assumptions(10,9) local.pre_edmonds_gallaiD(6) by blast
      have dblton_Md: "dblton_graph Md" 
        using M(1) dblton_quotE dblton_graph_Vs_inter by blast
      have Md_without_u_edge_Vs_inter: "Md \<subseteq> (quotG E) \<lbrakk>D - {u}\<rbrakk>"
        using M(1) graph_inter_Vs_subset(1)  M(1,2)
        by (intro is_part_of_graph_inter_Vs) force+
      have quotG_D_without_u:"(quotG E) \<lbrakk>D - {u}\<rbrakk> = E \<lbrakk>D - {u}\<rbrakk>"
        using assumptions(9) local.pre_edmonds_gallaiD(2) 
        by(intro u_not_in_subgraph_same_subgraph) auto
      have Md_without_matching: "graph_matching (E \<lbrakk>D - {u}\<rbrakk>) Md"
        using M(1) Md_without_u_edge_Vs_inter matching_delete quotG_D_without_u by blast
      have "\<exists>M. graph_matching ( E \<lbrakk>set C\<rbrakk>) M \<and> Vs M = Vs ( E \<lbrakk>set C\<rbrakk>) - {x}"
        using more_C_props distinct_C 2 
        by (intro odd_cycle_graph_factor_critical[of "E \<lbrakk>set C\<rbrakk>" "C" x])
           (auto simp add: dblton_E dblton_graph_Vs_inter)
      then obtain Mc where Mc: "graph_matching ( E \<lbrakk>set C\<rbrakk>) Mc" "Vs Mc = set C - {x}"
        using more_C_props(2) by auto
      have "matching (Md \<union> Mc)"
      proof(rule matching_vertex_disj_union, goal_cases)
        case 1
        then show ?case 
          by (simp add: M(1))
      next
        case 2
        then show ?case
          by (simp add: Mc(1))
      next
        case 3
        then show ?case
          using C_inter_quot_empty assumptions(9) local.pre_edmonds_gallaiD(2) 
          by (auto simp add: M(2) Mc(2))
      qed
      moreover have "Md \<union> Mc \<subseteq> E \<lbrakk>D - {u} \<union> set C\<rbrakk>"
      proof(rule is_part_of_graph_inter_Vs, goal_cases)
        case 1
        then show ?case
          using Mc(1) Md_without_matching graph_inter_Vs_subset(1) by blast
      next
        case 2
        thus ?case
        unfolding vs_union Mc(2) Vs_of_edge  M(2)
        using M(2) edges_are_Vs_2
        by fastforce
    qed
    ultimately have "graph_matching ( E \<lbrakk>D - {u} \<union> set C\<rbrakk>) (Md \<union> Mc)"
      by simp
    moreover have "Vs (Md  \<union> Mc) = 
                   D - {u} \<union> set C - {x}"
      using "2" C_inter_quot_empty assumptions(9) pre_edmonds_gallaiD(2)
      by (auto simp add: vs_union Mc(2) Vs_of_edge  M(2))
    ultimately show ?case 
      by auto
    qed
  qed

  have goal7: "\<lbrakk>v \<in> Vs E; even_vert E M v\<rbrakk> \<Longrightarrow> v \<in> \<Union> (\<D> - {D} \<union> {D - {u} \<union> set C})" for v
  proof(cases "v \<in> set C", goal_cases)
    case 2
    hence v_still_there:"P v = v"
      using assumptions(3) by auto
    hence "even_vert (quotG E) (quotG M) v"
      using even_vertex_blossom_contraction[OF assumptions(4) 2(2,1) assumptions(5,3,6-8)]
      by simp
    moreover have v_inquotVs:"v \<in> Vs (quotG E)"
      using "2"(1) v_still_there assumptions(6) Vs_quotG_is by fastforce
    ultimately have v_in_DU: "v \<in> \<Union> \<D>"
      using pre_edmonds_gallaiD(7) Vs_quotG_is by force
    then obtain X where X: "X \<in> \<D>" "v \<in> X"
      by auto
    show ?case
    proof(cases "X = D")
      case True
      hence "v \<noteq> u"
        using "2"(1) assumptions(6) by blast
      then show ?thesis 
        using X by auto
    next
      case False
      then show ?thesis
        using X by auto
    qed
  qed simp

  show ?thesis
    by(intro pre_edmonds_gallaiI goal1 goal2 goal3 goal4 goal5 goal6 goal7) auto
qed

lemma pre_emonds_gallai_perfect_after_contraction:
  assumes assumptions: "s = Vs E - set C" "blossom E M stem C"
          "graph_matching E M" "Vs (quotG M) = Vs (quotG E)"
    shows "pre_edmonds_gallai E M {set C}"
proof-

  have goal1: "disjoint {set C}"
    by(auto simp add: disjoint_def)
  have goal2: "\<Union> {set C} \<subseteq> Vs E"
    using assumptions(2) subset_path_Vs by fastforce
  have goal3: "X \<in> {set C} \<Longrightarrow> X \<noteq> {}" for X
    using assumptions(2) match_blossomD(3) odd_cycle_nempty by blast
  have goal4: "\<lbrakk>X \<in> {set C}; Y \<in> {set C}; X \<noteq> Y\<rbrakk> \<Longrightarrow> X \<leftarrow>|\<rightarrow>\<^bsub>E\<^esub> Y" for X Y
    by auto
  have not_in_M_is_in_C:"\<lbrakk>v \<in> Vs E; v \<notin> Vs M\<rbrakk> \<Longrightarrow> v \<in> set C" for v
  proof(rule ccontr, goal_cases)
    case 1
    then obtain v' where "{v, v'} \<in> E"
      by(auto simp add: vs_member' insert_commute)
    then obtain v'' where "{v, v''} \<in> quotG E" 
      using "1"(1,2,3) quot_Vs_in_s assumptions(1,3,4)  vert_in_graph_iff_in_quot_diff_u[of v M]
      by auto
    hence v_inquotM:"v \<in> Vs (quotG M)"
      by (simp add: assumptions(4) edges_are_Vs)
    then obtain v2 where "{v, v2} \<in> quotG M"
      using assumptions(3,4) doubleton_quot[of M] graph_invar_quotG 
        graph_invar_no_edge_no_vertex[of "quot_graph P M - {{u}}" v]
      by auto
    then obtain v2' where "{v, v2'} \<in> M"
      using "1"(1,2,3) v_inquotM assumptions(1,3) vert_in_graph_iff_in_quot_diff_u
      by blast
    then show ?case 
      using 1 by auto
  qed

  have u_not_in_quotM: "u \<notin> Vs (quotG M)"
  proof(rule ccontr, goal_cases)
    case 1
    then obtain x where "{u, x} \<in> quotG M"
      using assumptions(3,4) graph_invar_quotG doubleton_quot[of M]
        graph_invar_no_edge_no_vertex[of "quot_graph P M - {{u}}" u]
      by auto
    hence stem_nempty: "stem \<noteq> []"
      using "1" assumptions(1,2,3) match_blossom_def not_in_quot_matching_not_in_matching_2 odd_cycleD(3)
      by fastforce
    hence length_stem: "length stem \<ge> 2"
      using stem_even[OF assms(2)]
      by(cases stem rule: list_cases3) auto
    have s0_not_in_C: "stem ! 0 \<notin> set C" 
      using match_blossomD(2,3)[of M stem C] assms(2) length_stem
      by(cases stem rule: list_cases3, all \<open>cases C rule: list_cases_hd_and_last\<close>)
        (auto simp add: odd_cycle_def)
    have s0_neq_u: "stem ! 0 \<noteq> u"
      using stem_nempty assumptions(1,2) good_quot_map(1) mem_path_Vs' s0_not_in_C by auto
    have "(stem ! 0) \<notin> Vs (quotG M)"
    proof(rule ccontr, goal_cases)
      case 1
      then obtain y where y: "{stem ! 0, y} \<in> quotG M"
        using assumptions(3,4) graph_invar_quotG doubleton_quot[of M]
          graph_invar_no_edge_no_vertex[of "quot_graph P M - {{u}}" "stem ! 0"]
        by auto
      have "\<exists> y'. {stem ! 0, y'} \<in> M"
      proof(cases "y = u")
        case True
        then show ?thesis
          using assumptions(3) y doubleton_eq_iff[of u "stem ! 0" "stem ! 0" u]
            in_quotG_neq_u[of "stem ! 0" M] edge_in_quotG_2'_doubleton[of "stem ! 0" M]
            edges_are_Vs_2[of u "stem ! 0" "quot_graph P M - {{u}}"]
          by auto
      next
        case False
        hence "{stem ! 0, y} \<in>  M"
         using s0_neq_u assumptions(3) y u_nin_edge_in_quot[of "{stem ! 0, y}" M]
            edge_in_quot_in_graph_1'[of "{stem ! 0, y}" M] 
         by auto
        then show ?thesis 
          by auto
      qed
      hence "stem ! 0 \<in> Vs M"
        by auto
      thus False
        using stem_nempty assumptions(2) 
         by(cases stem)(auto dest!: match_blossomD(4))
    qed
    moreover have "(stem ! 0) \<in> Vs (quotG E)"
      using assumptions(1,2) mem_path_Vs quot_Vs_in_s s0_not_in_C stem_nempty by fastforce
    ultimately show False
      using assumptions(4) by blast
  qed
  have Neihgbourhood_C_empty:"Neighbourhood E (\<Union> {set C}) = {}" 
    proof(rule ccontr, goal_cases)
      case 1
      then obtain x y where xy: "x \<in> set C" "y \<notin> set C" "{x, y} \<in> E"
        by(auto simp add: Neighbourhood_def)
      hence "{y, u} \<in> quotG E"
        using assumptions(1) 
        by(intro edge_in_graph_edge_in_quot)(auto simp add: insert_commute)
      hence u_in_quot: "u \<in> Vs (quotG E)"
        by auto
      hence "u \<in> Vs (quotG M)"
        using assumptions(4) by blast
      thus False
        using u_not_in_quotM by simp
    qed
    hence goal5: "card (Neighbourhood E (\<Union> {set C})) < card {set C}"
      by auto

  have lengthC: "length C \<ge> 2" 
    using assms(2)
    by(auto dest!: match_blossomD(3) simp add: odd_cycle_def)
  have pathC: "path E C" 
    using assumptions(2) path_suff by auto

  have goal6: "\<lbrakk>X \<in> {set C}; x \<in> X\<rbrakk> \<Longrightarrow> \<exists>M. graph_matching ( E \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x}" for X x
  proof(goal_cases)
    case 1
    have Vs_E_non_C_rw:"Vs (E \<lbrakk>set C\<rbrakk>) = set C" 
      by (simp add: Vs_of_graph_inter_path lengthC pathC)
    have "\<exists>M. graph_matching ( E \<lbrakk>set C\<rbrakk>) M \<and> Vs M = Vs ( E \<lbrakk>set C\<rbrakk>) - {x}"
      using assumptions(2) 1
      by(intro odd_cycle_graph_factor_critical[of "E \<lbrakk>set C\<rbrakk>" C x])
        (auto dest: match_blossomD
          simp add: dblton_E dblton_graph_Vs_inter Vs_E_non_C_rw lengthC
                    pathC path_on_graph_inter_path)
    thus ?case 
      using 1 by (auto simp add: Vs_E_non_C_rw)
  qed

  have goal7: "\<lbrakk>v \<in> Vs E; even_vert E M v\<rbrakk> \<Longrightarrow> v \<in> \<Union> {set C}" for v
  proof(goal_cases)
    case 1
    then obtain p where "hd p \<notin> Vs M" "last p = v" "path E p \<or> length p = 1" "odd (length p)"
      by(auto simp add: even_vert_def)
    hence p: "hd p \<notin> Vs M" "last p = v" "path E p" "p \<noteq> []"
      using 1 by(all \<open>cases p rule: list_cases3\<close>) (auto simp add: path1)
    hence "hd p \<in> set C"
      using"1"(1)  mem_path_Vs[of E p "hd p"] not_in_M_is_in_C[of "hd p"]
      by auto
    hence "v \<in> set C" 
      using  Neihgbourhood_C_empty empty_Neighbourhood_path_contained[of p E "set C"]  p(2,3,4)
      by(cases p rule: rev_cases) auto
    then show ?case 
      by auto
  qed

  show ?thesis
    by(intro pre_edmonds_gallaiI goal1 goal2 goal3 goal4 goal5 goal6 goal7 | assumption)+
qed

subsection \<open>Computation with the Blossom Algorihtm\<close>
subsubsection \<open>Alternating Search\<close>
end

datatype 'v alt_search_res =  Two_Paths "'v list" "'v list" | PEDG "'v set set"

context compute_alt_path
begin


function (domintros) compute_alt_path_or_pedg:: "'F \<Rightarrow> 'a alt_search_res" where
  "compute_alt_path_or_pedg F = 
    (if if1_cond F then
       let
         (v1,v2,v3) = sel_if1 F;
          F' = extend_forest_even_unclassified F v1 v2 v3;
         return = compute_alt_path_or_pedg F'
       in
         return
     else if if2_cond F then
        let
          (v1,v2) = sel_if2 F; 
          return = Two_Paths (get_path F v1) (get_path F v2)
        in
          return
     else
       let
          return = PEDG {{v} | v. v \<in> vset_to_set (evens F)}
       in
         return)"
  by pat_completeness auto

lemma compute_alt_path_or_pedg_same_dom:
  shows "compute_alt_path_or_pedg_dom F \<longleftrightarrow> compute_alt_path_dom F"
proof(rule, goal_cases)
  case 1
  then show ?case 
    by(induction rule: compute_alt_path_or_pedg.pinduct)
      (auto intro: compute_alt_path.domintros)
next
  case 2
  then show ?case
    by(induction rule: compute_alt_path.pinduct)
      (auto intro: compute_alt_path_or_pedg.domintros)
qed

lemmas compute_alt_path_or_pedg_psimps' =
   compute_alt_path_or_pedg.psimps[simplified compute_alt_path_or_pedg_same_dom]

lemma compute_alt_path_or_pedg_same:
  assumes "compute_alt_path_dom F"
  shows "compute_alt_path_or_pedg F = Two_Paths p1 p2 \<longleftrightarrow> compute_alt_path F = Some (p1, p2)"
  using assms
proof(induction rule: compute_alt_path.pinduct, goal_cases)
  case (1 F)
  thus ?case
    by(auto simp add: compute_alt_path_or_pedg.psimps[of F] compute_alt_path.psimps[of F] 
                      compute_alt_path_or_pedg_same_dom 
               split: if_split prod.split)
qed

lemma compute_alt_path_or_pedg_same':
  assumes "compute_alt_path_dom F"
  shows "(\<exists> D. compute_alt_path_or_pedg F = PEDG D) \<longleftrightarrow> compute_alt_path F = None"
proof(cases "compute_alt_path F", goal_cases)
  case 1
  then show ?case 
    using compute_alt_path_or_pedg_same[OF assms]
    by (cases "compute_alt_path_or_pedg F") auto
next
  case (2 a)
  then show ?case
  proof(cases a, goal_cases)
    case (1 p1 p2)
    then show ?case 
      using compute_alt_path_or_pedg_same[OF assms, of p1 p2]
      by auto
  qed
qed

lemma compute_alt_path_or_pedg_if1:
  assumes "compute_alt_path_dom F" 
    "if1_cond F"
    "(v1, v2, v3) = sel_if1 F"
    "F' = extend_forest_even_unclassified F v1 v2 v3"
  shows "compute_alt_path_or_pedg F = compute_alt_path_or_pedg F'"
  using assms
  by (auto simp add: compute_alt_path_or_pedg.psimps compute_alt_path_or_pedg_same_dom
      Let_def split: if_splits prod.splits)

lemma what_if_search_fails_pedg:
  assumes "compute_alt_path_or_pedg F = PEDG \<D>"
   and     init: "finite \<lbrace>F\<rbrace>" "\<lbrace>F\<rbrace> \<subseteq> G" 
   and invars: "forest_invar M F" "aevens F \<subseteq> Vs G"
 shows "\<exists> F'. \<not> if1_cond F' \<and> \<not> if2_cond F' \<and> forest_invar M F' \<and> aroots F' = aroots F
               \<and> \<D> = {{v} | v. v \<in> vset_to_set (evens F')} \<and> aevens F' \<subseteq> Vs G \<and> \<lbrace> F' \<rbrace> \<subseteq> G"
  using assms(1) invars init(2)
proof(induction F arbitrary: \<D> rule: compute_alt_path_pinduct_2)
  case 1
  then show ?case
    by(intro compute_alt_path_dom init invars)
next
  case (2 F)
  note IH = this
  show ?case
  proof(cases "if1_cond F")
    case True
    obtain v1 v2 v3 where sel: "(v1,v2,v3) = sel_if1 F" "if1 F v1 v2 v3"
      using if1_cond_props''''[OF True] by metis
    hence  v1v2: "{v1, v2} \<in> G - \<lbrace>F\<rbrace>" "{v2, v3} \<in> M"  "v1 \<in> aevens F" "v2 \<notin> FVs F"
        using if1_props by auto
      then have v1_v2_P:"{v1, v2} \<in> G" "{v1, v2} \<notin> \<lbrace>F\<rbrace>"
        by simp+
      define F' where "F' = extend_forest_even_unclassified F v1 v2 v3"

      have precd:"forest_extension_precond F M v1 v2 v3"
        by (simp add: 2(4) \<open>if1 F v1 v2 v3\<close> if_1_forest_extension_precond)
      note F'_props = forest_extend[OF precd, folded F'_def]
      show ?thesis
        using IH(3,5,6) matching(2) v1v2(2) v1_v2_P(1)
        by(auto intro!: IH(2)[OF True sel(1) F'_def] 
              simp add: F'_props(5)[symmetric]
                        compute_alt_path_or_pedg_if1[OF IH(1) True sel(1) F'_def] F'_props(1-3))+
  next
    case False
    note false = this
    show ?thesis
    proof(cases "if2_cond F")
      case True
      hence False
        using IH(3) false
        by(subst (asm) compute_alt_path_or_pedg_psimps'[OF IH(1)], cases "sel_if2 F")
          (auto dest!:  if2_cond_props'''') 
      thus ?thesis
        by simp
  next
    case False
    thus ?thesis
      using false IH(1,3,4,5,6)
      by(auto intro!: exI[of _ F] exI[of _ F] simp add: compute_alt_path_or_pedg_psimps')
  qed
qed
qed

lemma finial_forest_evens'_Neighbourhood:
  assumes "\<not> if1_cond F" "\<not> if2_cond F" "forest_invar M F" "Vs G - Vs M \<subseteq> aevens F" "\<lbrace>F\<rbrace> \<subseteq> G"
  shows "Neighbourhood G (aevens F) = aodds F"
proof(rule, all \<open> rule, (elim in_NeighbourhoodE)?\<close>, goal_cases)
  case (1 x y)
  then show ?case 
  proof(cases "{x, y} \<in> \<lbrace> F \<rbrace>", goal_cases)
    case 1
    then show ?case 
      using  assms(3) higher_forest_properties(3)[of M F y x]
      by (auto simp add: insert_commute)
  next
    case 2
    then show ?case
    proof(cases "x \<in> FVs F", goal_cases)
      case 1
      then show ?case 
        using assms(3) evens_and_odds(3) by auto
    next
      case 2
      then show ?case
      proof(cases "\<exists>v3. {x, v3} \<in> M", goal_cases)
        case 1
        then show ?case 
         using assms(1) by(auto simp add: if1_cond_def)
      next
        case 2
        moreover hence "x \<in> Vs G - Vs M"
         using matching(2) 
         by (auto simp add:  graph_abs.vs_member'[OF  graph_abs_subset] insert_commute)
       ultimately have False
         using assms(4) by auto
       thus ?case
         by simp
     qed
   qed 
 qed
next
  case (2 x)
  hence "x \<in> Vs \<lbrace>F\<rbrace>"
    using evens_and_odds(3,4)[OF assms(3)] roots(2)[OF assms(3)]
    by auto
  then obtain e where e: "e \<in> \<lbrace>F\<rbrace>" "x \<in> e" 
    by(auto elim!: vs_member_elim)
  obtain y where y: "{x, y} \<in> \<lbrace>F\<rbrace>" "x \<noteq> y"
    apply(rule Undirected_Set_Graphs.dblton_graphE[OF dblton[OF assms(3)] e(1)])
    using e 
    by (auto simp add: insert_commute)+
  hence "y \<in> aevens F" 
    using "2"  higher_forest_properties(3)[OF assms(3), of y x]
    by(auto simp add: insert_commute)
  moreover have "x \<notin> aevens F"
    using "2" assms(3) evens_and_odds(4) by blast
  moreover have "{x, y} \<in> G"
    using assms(5) y(1) by blast
  ultimately show ?case 
    by(auto intro!: in_NeighbourhoodI simp add: insert_commute)
qed

lemma termination_conditions_pedg:
  assumes "\<not> if1_cond F" "\<not> if2_cond F" "forest_invar M F" "Vs G - Vs M \<subseteq> aevens F" 
          "aevens F \<subseteq> Vs G" "\<lbrace> F \<rbrace> \<subseteq> G" "aroots F \<noteq> {}"
    shows "pre_edmonds_gallai G M {{v} |v. v \<in> aevens F}"
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
  have goal6: "card (Neighbourhood G (\<Union> {{v} |v. v \<in> aevens F})) < card {{v} |v. v \<in> aevens F}"
  proof-
    have rw1: "\<Union> {{v} |v. v \<in> aevens F} = aevens F" 
      by auto
    have rw2: "card {{v} |v. v \<in> aevens F} = card (aevens F)"
      by(subst card_image[of "\<lambda> v. {v}" "aevens F", symmetric])
        (auto intro!: inj_onI arg_cong[where f = card])
    show ?thesis
      unfolding rw1 rw2 finial_forest_evens'_Neighbourhood[OF assms(1,2,3,4,6)]
      using roots(2)[OF assms(3)] assms(5)
      by (subst higher_forest_properties(1)[OF assms(3)])
         (auto intro!:  finite_subset[of "aroots F" "Vs G"]  
             simp add: card_gt_0_iff assms(7) finite_Vs)
  qed
  have goal7: "\<lbrakk>X \<in> {{v} |v. v \<in> aevens F}; x \<in> X\<rbrakk>
        \<Longrightarrow> \<exists>M. graph_matching ( G \<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x}" for x X
    by(auto intro!: exI[of _ "{}"])
  have goal8: "\<lbrakk>v \<in> Vs G; even_vert G M v\<rbrakk> \<Longrightarrow> v \<in> \<Union> {{v} |v. v \<in> aevens F}" for v
  proof(goal_cases)
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
  thus ?thesis
    using p_props(4) by blast
qed
 
  show ?thesis
    by(assumption | rule pre_edmonds_gallaiI  goal1 goal2 goal3 goal5 goal6 goal7 goal8)+
qed

lemma compute_alt_path_or_pedg_from_tree_2:
  assumes invars: "forest_invar M F" 
  and ret: "compute_alt_path_or_pedg F = PEDG \<D>"
  and init: "finite \<lbrace>F\<rbrace>" "\<lbrace>F\<rbrace> \<subseteq> G" "aevens F \<subseteq> Vs G"
  and unmatcheds_even: "Vs G - Vs M \<subseteq> aroots F" "Vs G - Vs M \<noteq> {}"
shows "\<nexists>p. matching_augmenting_path M p \<and> path G p \<and> distinct p" (is ?thesis1)
      "pre_edmonds_gallai G M \<D>" (is ?thesis2)
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
  have aroots_F': "aroots F' \<noteq> {}"
    using F'(4) unmatcheds_even(1,2) by force
  show ?thesis2           
    using termination_conditions_pedg[OF  F'(1,2,3) Vs_with_M_in_aevens F'(6,7) aroots_F'] F'(5)
    by simp
qed

definition "compute_pedg =
  (case compute_alt_path_or_pedg (empty_forest unmatcheds) of 
    PEDG \<D> \<Rightarrow> \<D>)"

lemma init_evens_in_G:"aevens (empty_forest unmatcheds) \<subseteq> Vs G"
  by (simp add: empty_forest(1) unmatcheds(2))

lemma initial_dom: "compute_alt_path_dom (empty_forest unmatcheds)"
  by (simp add: compute_alt_path_dom empty_forest(4) init_props(1))

lemma compute_pedg_correct:
  "\<lbrakk>compute_alt_path (empty_forest unmatcheds) = None; Vs G - Vs M \<noteq> {}\<rbrakk> \<Longrightarrow>
     pre_edmonds_gallai G M compute_pedg"
  by(rule compute_alt_path_or_pedg_from_tree_2(2)[OF 
            init_props(1) _ init_props(2,3)  init_evens_in_G init_props(4)])
    (auto simp add: compute_pedg_def compute_alt_path_or_pedg_same initial_dom 
             split: alt_search_res.split)

end

subsubsection \<open>Blossom Contraction and Reexpansion\<close>

locale find_aug_path_pedg =
find_aug_path where sel = sel
for sel::"'a set \<Rightarrow> 'a"+
fixes pedg_search::"'a set set \<Rightarrow> 'a set set \<Rightarrow> 'a set set"
and sel_from_sets::"('a set \<Rightarrow> bool) \<Rightarrow> 'a set set \<Rightarrow> 'a set"
assumes pedg_search_sound: 
 "\<lbrakk>graph_invar G; matching M; M \<subseteq> G; blos_search G M = None; Vs G - Vs M \<noteq> {}\<rbrakk>
     \<Longrightarrow> pre_edmonds_gallai G M (pedg_search G M)" 
assumes sel_from_sets:
  "\<And> \<D> P. \<lbrakk>finite \<D>; \<exists> D \<in> \<D>. P D\<rbrakk> \<Longrightarrow> sel_from_sets P \<D> \<in> \<D>"
  "\<And> \<D> P. \<lbrakk>finite \<D>; \<exists> D \<in> \<D>. P D\<rbrakk> \<Longrightarrow> P (sel_from_sets P \<D>)"
begin

function (domintros) find_pedg where
  "find_pedg G M = 
     (case blos_search G M of Some match_blossom_res \<Rightarrow>
        (case match_blossom_res of Blossom stem cyc \<Rightarrow>
            (let u = create_vert (Vs G);
                 s = Vs G - (set cyc);
                 quotG = quot.quotG s u
              in (if Vs (quotG G) = Vs (quotG M)
                 then {set cyc}
                 else 
                 (let \<D> = find_pedg (quotG G) (quotG M)
                 in if Delta G (set cyc) = {}
                    then insert  (set cyc) \<D>
                    else let D = sel_from_sets (\<lambda> D. u \<in> D) \<D>;
                             \<D>' = \<D> - {D} \<union> {D - {u} \<union>  (set cyc)}
                         in \<D>'))))
      | _ \<Rightarrow> pedg_search G M)"
  by pat_completeness auto

thm find_aug_path_dom
lemma find_pedg_dom:
  assumes  "matching M" "M \<subseteq> E" "graph_invar E" 
  shows "find_pedg_dom (E,M)"
  using assms
proof(induction "find_aug_path_meas E" arbitrary: E M rule: less_induct)
  case less
  have "find_pedg_dom
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
      by(intro find_pedg.domintros) auto
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

lemmas pre_emonds_gallai_perfect_after_contraction=
  quot.pre_emonds_gallai_perfect_after_contraction

lemmas pre_emonds_gallai_connected_blossom_obtain_D = 
  quot.pre_emonds_gallai_connected_blossom_obtain_D

lemmas pre_emonds_gallai_connected_blossom =
  quot.pre_emonds_gallai_connected_blossom
end

lemma find_pedg_correct:
  assumes  "graph_invar E" "max_card_matching E M" "Vs E - Vs M \<noteq> {}"
  shows "pre_edmonds_gallai E M (find_pedg E M)"
  using assms
proof(induction rule:  find_pedg.pinduct[OF find_pedg_dom, of M E], goal_cases)
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
    unfolding find_pedg.psimps[OF IH(1)]
  proof(cases "blos_search G M", goal_cases)
    case 1
    then show ?case
      using IH(4,5) max_card_matchingDs(2)
      by(auto intro!: pedg_search_sound simp add: IH(3) max_card_matching_subgraphD)
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
    show ?case
      unfolding 2 res_def option.case  match_blossom_res.case
    proof(cases "Vs (quotG G) = Vs (quotG M)", goal_cases)
      case 1
      then show ?case
        unfolding Let_def
      proof(subst (3) if_P, goal_cases)
        case 1
        then show ?case 
          unfolding quotG_def s_def u_def
          by simp
      next
        case 2
        thus ?case
          by(intro pre_emonds_gallai_perfect_after_contraction[OF 
                    s_string_in_G IH(3) s_def a_blossom graph_matching_M])
            (simp add: quot_fold)
      qed
    next
      case 2
      note not_perfect = this
      
    define \<D> where  "\<D> = find_pedg (quotG G) (quotG M)"

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
     have IH_applied: "pre_edmonds_gallai (quotG G) (quotG M) \<D>"
       unfolding \<D>_def
     proof(rule IH(2)[OF two res_def u_def s_def], goal_cases)
       case 1
       then show ?case 
         using graph_invar_quotG IH(3) quotG_def s_string_in_G u_def 
         by presburger
     next
       case 4
       then show ?case 
         using IH(4)
         using max_card_matching_equiv_blossom_contraction[OF s_string_in_G IH(3) a_blossom
                 graph_matching_M s_def, simplified quot_fold]
         by (simp add: u'_props(1))
     next
       case 2
       then show ?case
         using  not_perfect by simp
     next
       case 3
       thus ?case
         using IH(3) graph_invar_quotG quotG_def s_string_in_G u_def by presburger
     next
       case 5
       thus ?case 
         using Vs_quot_M_in_quot_Vs not_perfect by blast
     qed 
     have grapn_invar_quot: "graph_invar (quotG G)"
       using IH(3) graph_invar_quotG quotG_def s_string_in_G u_def by presburger
    show ?case 
    proof(cases "Delta G (set cyc) = {}", goal_cases)
      case 1
      have "pre_edmonds_gallai G M (insert (set cyc) \<D>)"
        using IH_applied IH(4) u'_props 
        by (intro pre_emonds_gallai_lonely_blossom[OF s_string_in_G IH(3) _ 1 _ a_blossom],
            unfold  quot_fold)
            (auto simp add: s_def)
      thus ?case
        unfolding Let_def quot_fold[simplified s_def]
        by (simp add: "1" \<D>_def not_perfect)
    next
      case 2
      define D where "D = sel_from_sets ((\<in>) u) \<D>" 

      note obtainD1 =
           pre_emonds_gallai_connected_blossom_obtain_D[OF s_string_in_G IH(3) _ 2 _ a_blossom,
              simplified quot_fold[simplified s_def]]
      note obtainD2 =obtainD1[OF IH_applied s_def IH(4) u'_props]
      moreover have finite_\<D>: "finite \<D>" 
        using IH_applied
        by(auto dest!: pre_edmonds_gallaiD(2)
             simp add: finite_UnionD finite_subset grapn_invar_quot)
      ultimately have D_props: "D \<in> \<D>" "create_vert (Vs G) \<in> D"
        using sel_from_sets[of \<D> "(\<in>) u"]
        by(auto simp add: D_def u_def)
      note new_pedg1 =
           pre_emonds_gallai_connected_blossom[OF s_string_in_G IH(3) _ 2 _ a_blossom,
              simplified quot_fold[simplified s_def]]
      note new_pedg2 = new_pedg1[OF IH_applied s_def IH(4) u'_props D_props, folded u_def]
      thus ?case
        unfolding Let_def quot_fold[simplified s_def]
        by (simp add: "2" D_def \<D>_def not_perfect u_def)
    qed
  qed
qed
qed

end
end