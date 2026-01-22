theory Naive_Primal_Dual
  imports Directed_Set_Graphs.More_Arith "HOL-Data_Structures.Set_Specs"
    "HOL-Data_Structures.Map_Specs"  Directed_Set_Graphs.More_Logic
    Primal_Dual_Bipartite_Matching.Matching_LP
    Undirected_Set_Graphs.Directed_Undirected
begin

section \<open>The Algorithm Resulting from Shrijver\<close>

subsection \<open>Preparation, to be moved\<close>

no_translations
  "_Collect p P"      <= "{p. P}"
  "_Collect p P"      <= "{p|xs. P}"
  "_CollectIn p A P"  <= "{p : A. P}"

(*TODO MOVE*)

lemma common_denominator:
  assumes "finite (A::rat set)"
  shows "\<exists> (d::nat). d > 0 \<and>( \<forall> x \<in> A. \<exists> i::int. real_of_rat x = (real_of_int i) / (real d))"
  using assms
proof(induction rule: finite_induct)
  case empty
  then show ?case by auto
next
  case (insert y A)
  then obtain d1 where d:"\<And> x. x\<in>A \<Longrightarrow> \<exists>i. real_of_rat x = real_of_int i / real d1" "d1 > 0"
    by auto
  obtain d2 i where d2_i:"real_of_rat y = real_of_int i / real d2" "d2 > 0"
    using Rats_eq_int_div_nat by fastforce
  have prop1:"real_of_int i / real d2 = real_of_int (i * (lcm d1 d2 div d2)) / real (lcm d1 d2)"
    using d(2) by(simp add: real_of_nat_div)
  have prop2:"0 < lcm d1 d2"
    using d(2) d2_i(2) lcm_pos_nat by presburger
  have prop3:"real_of_rat x = real_of_int i / real d1 \<Longrightarrow>
           real_of_int i / real d1 =
           real_of_int (i * (lcm d1 d2 div d1)) / real (lcm d1 d2)" for x i
    using d2_i(2) by(simp add: real_of_nat_div)
  show ?case 
    by(auto intro!: exI[of _ "lcm d1 d2"] prop2
        exI[of "\<lambda> ia. real_of_int _ / real d1 = real_of_int ia / real (lcm d1 d2)"
          "_ * int (lcm d1 d2 div d1)"] prop3
        intro: exI[of _ "i * int (lcm d1 d2 div d2)"] prop1
        simp add: d2_i algebra_simps dest!: d(1))
qed

subsection \<open>Implementing the Algorithm\<close>

datatype ('m, 'vset) match_or_witness_set = match 'm | witness 'vset 'vset

locale naive_primal_dual_spec = 
  vset: Set2 vset_empty vset_delete vset_isin vset_set vset_invar vset_insert  vset_union vset_inter  vset_diff+
  p_map: Map p_empty p_update p_delete p_lookup p_invar 
  for vset_empty vset_insert vset_delete vset_isin and vset_set::"'vset \<Rightarrow> 'v set" and vset_invar 
    vset_inter vset_union vset_diff
    and p_empty p_update p_delete and p_lookup::"'pmap \<Rightarrow> 'v \<Rightarrow> real option" and p_invar +
  fixes G::"'v set set"
    and   G_impl::"'m"
    and   g_to_set::"'m \<Rightarrow> 'v set set"
    and   g_isin::"'v \<Rightarrow> 'v \<Rightarrow> 'm \<Rightarrow> bool"
    and   g_invar::"'m \<Rightarrow> bool"
    and   g_insert::"'v \<Rightarrow> 'v \<Rightarrow> 'm \<Rightarrow> 'm"
    and   g_empty::"'m"
    and   g_iterate_p::"'m \<Rightarrow> (('v \<times> 'v) \<Rightarrow> 'pmap \<Rightarrow> 'pmap) \<Rightarrow> 'pmap \<Rightarrow> 'pmap"
    and   g_iterate_real::"'m \<Rightarrow> (('v \<times> 'v) \<Rightarrow>ereal \<Rightarrow> ereal) \<Rightarrow> ereal \<Rightarrow> ereal"
    and   g_iterate_g::"'m \<Rightarrow> (('v \<times> 'v) \<Rightarrow> 'm \<Rightarrow> 'm) \<Rightarrow> 'm \<Rightarrow> 'm"
    and   vset_iterate_real::"'vset\<Rightarrow> ('v \<Rightarrow>ereal \<Rightarrow> ereal) \<Rightarrow> ereal \<Rightarrow> ereal"
    and   vset_iterate_vset::"'vset \<Rightarrow> ('v \<Rightarrow> 'vset \<Rightarrow> 'vset) \<Rightarrow> 'vset \<Rightarrow> 'vset"
    and   vset_iterate_pmap::"'vset \<Rightarrow> ('v \<Rightarrow> 'pmap \<Rightarrow> 'pmap) \<Rightarrow> 'pmap \<Rightarrow> 'pmap"
    and   find_matching_or_witness::"'m \<Rightarrow> 'vset \<Rightarrow> ('m, 'vset) match_or_witness_set"
    and   lefts::'vset
    and   rights::'vset
    and   weight::"'v \<Rightarrow> 'v \<Rightarrow> real"
begin

definition "lefts_and_rights = vset_union lefts rights"

definition "init_potential = g_iterate_p G_impl
     (\<lambda>  (u, v) pmap. if vset_isin lefts u \<and> 
                        abstract_real_map (p_lookup pmap) u < weight u v 
                     then p_update u (weight u v) pmap
                     else if vset_isin lefts v \<and> 
                        abstract_real_map (p_lookup pmap) v < weight u v 
                     then p_update v (weight u v) pmap
                     else pmap)
                 p_empty"

definition "edge_slack pot x y = 
    - weight x y 
     + abstract_real_map (p_lookup pot) x
     + abstract_real_map (p_lookup pot) y"

lemma edge_slack_cong:
  "\<lbrakk>weight x y = weight x' y'; 
    abstract_real_map (p_lookup pot) x = abstract_real_map (p_lookup pot) x';
    abstract_real_map (p_lookup pot) y = abstract_real_map (p_lookup pot) y'\<rbrakk>
    \<Longrightarrow> edge_slack pot x y = edge_slack pot x' y'"
  "\<lbrakk>weight x y = weight x' y';
    abstract_real_map (p_lookup pot) y = abstract_real_map (p_lookup pot) x';
    abstract_real_map (p_lookup pot) x = abstract_real_map (p_lookup pot) y'\<rbrakk>
    \<Longrightarrow> edge_slack pot x y = edge_slack pot x' y'"
  by(auto simp add: edge_slack_def)

definition "build_tight_graph pmap =
   g_iterate_g G_impl 
         (\<lambda>  (u, v) tights. if (edge_slack pmap u v = 0) then g_insert u v tights else tights) 
              g_empty"

definition "find_\<epsilon> pmap S = 
     min (g_iterate_real G_impl 
            (\<lambda> (u, v) val . let sl =  edge_slack pmap u v in
                        (if sl \<noteq> 0 \<and> ereal sl < val \<and> (vset_isin S u \<or> vset_isin S v)
                         then ereal sl 
                         else val)) 
          PInfty) 
        (vset_iterate_real S (\<lambda> u val . let pu = abstract_real_map (p_lookup pmap) u in 
                                (if ereal pu < val then ereal pu else val)) PInfty)" 

definition "find_bads pmap =
  vset_iterate_vset lefts_and_rights
        (\<lambda> v S. if abstract_real_map (p_lookup pmap) v > 0 then vset_insert v S else S) vset_empty"

function (domintros) naive_primal_dual::"'pmap \<Rightarrow> 'm " where
  "naive_primal_dual pmap = 
(let tights = build_tight_graph pmap;
     bads = find_bads pmap
 in case ( find_matching_or_witness tights bads) of
    (match M) \<Rightarrow> M
    | witness S NS \<Rightarrow>
      let \<epsilon> = real_of_ereal (find_\<epsilon> pmap S);
          pmap' = vset_iterate_pmap S
                  (\<lambda> v p. p_update v (abstract_real_map (p_lookup pmap) v - \<epsilon>) p) pmap;
          pmap'' = vset_iterate_pmap NS
                  (\<lambda> v p. p_update v (abstract_real_map (p_lookup pmap) v + \<epsilon>) p) pmap'
      in naive_primal_dual pmap'')"
  by pat_completeness auto

definition 
  "naive_primal_dual_call pmap = 
(let tights = build_tight_graph pmap;
     bads = find_bads pmap
 in case ( find_matching_or_witness tights bads) of
    (match M) \<Rightarrow> undefined
    | witness S NS \<Rightarrow>
      let \<epsilon> = real_of_ereal (find_\<epsilon> pmap S);
          pmap' = vset_iterate_pmap S
                  (\<lambda> v p. p_update v (abstract_real_map (p_lookup pmap) v - \<epsilon>) p) pmap;
          pmap'' = vset_iterate_pmap NS
                  (\<lambda> v p. p_update v (abstract_real_map (p_lookup pmap) v + \<epsilon>) p) pmap'
      in pmap'')"

definition 
  "naive_primal_dual_ret pmap = 
(let tights = build_tight_graph pmap;
     bads = find_bads pmap
 in case ( find_matching_or_witness tights bads) of
    (match M) \<Rightarrow> M
    | witness S NS \<Rightarrow>undefined)"

partial_function (tailrec) naive_primal_dual_impl::"'pmap \<Rightarrow> 'm" where
  "naive_primal_dual_impl pmap = 
(let tights = build_tight_graph pmap;
     bads = find_bads pmap
 in case ( find_matching_or_witness tights bads) of
    (match M) \<Rightarrow> M
    | witness S NS \<Rightarrow>
      let \<epsilon> = real_of_ereal (find_\<epsilon> pmap S);
          pmap' = vset_iterate_pmap S
                  (\<lambda> v p. p_update v (abstract_real_map (p_lookup pmap) v - \<epsilon>) p) pmap;
          pmap'' = vset_iterate_pmap NS
                  (\<lambda> v p. p_update v (abstract_real_map (p_lookup pmap) v + \<epsilon>) p) pmap'
      in naive_primal_dual_impl pmap'')"

lemma naive_primal_dual_impl_same:
  assumes "naive_primal_dual_dom pmap"
  shows   "naive_primal_dual_impl pmap = naive_primal_dual pmap"
  by(induction rule: naive_primal_dual.pinduct[OF assms(1)],
     subst naive_primal_dual.psimps)
    (auto split: match_or_witness_set.split simp add: naive_primal_dual_impl.simps)

definition "naive_primal_dual_ret_cond pmap = 
(let tights = build_tight_graph pmap;
     bads = find_bads pmap
 in case ( find_matching_or_witness tights bads) of
    (match M) \<Rightarrow> True
    | witness S NS \<Rightarrow> False)"

lemma naive_primal_dual_ret_condI:
  "\<And> tights bads M. 
     \<lbrakk>tights = build_tight_graph pmap; bads = find_bads pmap;
      find_matching_or_witness tights bads = match M\<rbrakk>
     \<Longrightarrow> naive_primal_dual_ret_cond pmap"
  and naive_primal_dual_ret_condE:
  "naive_primal_dual_ret_cond pmap\<Longrightarrow> 
   (\<And> tights bads M. 
       \<lbrakk>tights = build_tight_graph pmap;  bads = find_bads pmap;
        find_matching_or_witness tights bads = match M\<rbrakk> \<Longrightarrow> P) 
   \<Longrightarrow> P"
  by(auto simp add:  naive_primal_dual_ret_cond_def split: match_or_witness_set.splits)

definition "naive_primal_dual_call_cond pmap = 
(let tights = build_tight_graph pmap;
     bads = find_bads pmap
 in case ( find_matching_or_witness tights bads) of
    (match M) \<Rightarrow> False
    | witness S NS \<Rightarrow> True)"

lemma naive_primal_dual_call_condI:
  "\<And> tights bads S NS. 
       \<lbrakk>tights = build_tight_graph pmap; bads = find_bads pmap;
        find_matching_or_witness tights bads =  witness S NS\<rbrakk>
       \<Longrightarrow> naive_primal_dual_call_cond pmap"
  and naive_primal_dual_call_condE:
  "naive_primal_dual_call_cond pmap\<Longrightarrow> 
   (\<And> tights bads S NS. 
        \<lbrakk>tights = build_tight_graph pmap; bads = find_bads pmap;
         find_matching_or_witness tights bads = witness S NS\<rbrakk> \<Longrightarrow> P) 
   \<Longrightarrow> P"
  by(auto simp add:  naive_primal_dual_call_cond_def split: match_or_witness_set.splits)

lemma naive_primal_dual_cases:
  assumes "naive_primal_dual_ret_cond pmap \<Longrightarrow> P"
          "naive_primal_dual_call_cond pmap \<Longrightarrow> P"
  shows P
  by(cases "naive_primal_dual_ret_cond pmap")
    (auto intro: assms 
      simp add: naive_primal_dual_ret_cond_def naive_primal_dual_call_cond_def 
      split: match_or_witness_set.splits)

lemma naive_primal_dom_call:
  "\<lbrakk>naive_primal_dual_dom (naive_primal_dual_call pmap); naive_primal_dual_call_cond pmap\<rbrakk>
    \<Longrightarrow> naive_primal_dual_dom pmap"
  by(rule naive_primal_dual.domintros)
    (auto elim!: naive_primal_dual_call_condE 
      simp add: naive_primal_dual_call_def Let_def)

lemma naive_primal_dom_ret:
  "naive_primal_dual_ret_cond pmap \<Longrightarrow> naive_primal_dual_dom pmap"
  by(rule naive_primal_dual.domintros)
    (auto elim!: naive_primal_dual_ret_condE simp add: Let_def)

lemma naive_primal_dual_simps:
  "naive_primal_dual_ret_cond pmap \<Longrightarrow> naive_primal_dual pmap = naive_primal_dual_ret pmap"
  "\<lbrakk>naive_primal_dual_call_cond pmap; naive_primal_dual_dom pmap\<rbrakk>
    \<Longrightarrow> naive_primal_dual pmap = naive_primal_dual (naive_primal_dual_call pmap)"
proof(goal_cases)
  case 1
  thus ?case
    by(subst naive_primal_dual.psimps)
      (auto intro!: naive_primal_dom_ret simp add: naive_primal_dual_ret_def
        elim: naive_primal_dual_ret_condE)
next
  case 2
  thus ?case
    by(subst naive_primal_dual.psimps)
      (auto simp add: naive_primal_dual_call_def Let_def elim!:  naive_primal_dual_call_condE)
qed

end

subsection \<open>Locale for Proofs\<close>

locale naive_primal_dual_reasoning =
  naive_primal_dual_spec +
  assumes G_props: "g_invar G_impl"  "g_to_set G_impl = G"
    "bipartite G (vset_set lefts) (vset_set rights)"
    "vset_invar lefts" "vset_invar rights"
    "finite (vset_set lefts)" "finite (vset_set rights)"
    and g_basic_operations: "g_invar g_empty"
    "\<And> x y G. g_invar G \<Longrightarrow> {x, y} \<in> g_to_set G \<longleftrightarrow> g_isin x y G"
    "\<And> x y G. g_invar G \<Longrightarrow> g_invar (g_insert x y G)"
    "\<And> x y G. g_invar G \<Longrightarrow> g_to_set (g_insert x y G) = insert {x, y} (g_to_set G)"
    "g_to_set g_empty = {}"
    and g_iterations: "\<And> G pmap f. g_invar G \<Longrightarrow> \<exists> es. pair_list_distinct es 
                                        \<and> set_of_pair ` (set es) = g_to_set G \<and>
                                        g_iterate_p G f pmap = foldr f es pmap"
    "\<And> G r f. g_invar G \<Longrightarrow> \<exists> es. pair_list_distinct es 
                                        \<and> set_of_pair ` (set es) = g_to_set G \<and>
                                        g_iterate_real G f r = foldr f es r"
    "\<And> G G' f. g_invar G \<Longrightarrow> \<exists> es. pair_list_distinct es 
                                        \<and> set_of_pair ` (set es) = g_to_set G \<and>
                                        g_iterate_g G f G' = foldr f es G'"
    and vset_iterations: "\<And> V f r. vset_invar V \<Longrightarrow> \<exists> vs. distinct vs \<and> set vs = vset_set V
                                        \<and> vset_iterate_real V f r = foldr f vs r"
    "\<And> V f V'. vset_invar V \<Longrightarrow> \<exists> vs. distinct vs \<and> set vs = vset_set V
                                        \<and> vset_iterate_vset V f V' = foldr f vs V'"
    "\<And> V f pmap. vset_invar V \<Longrightarrow> \<exists> vs. distinct vs \<and> set vs = vset_set V
                                        \<and> vset_iterate_pmap V f pmap = foldr f vs pmap "
    and pos_weights: "\<And> u v. {u, v} \<in> G \<Longrightarrow> weight u v \<ge> 0"
    and sym_weights: "\<And> u v. {u, v} \<in> G \<Longrightarrow> weight u v = weight v u"
    and find_matching_or_witness:
    "\<And> E A B R M. 
      \<lbrakk>bipartite (g_to_set E) A B; g_invar E; vset_invar R; find_matching_or_witness E R = match M\<rbrakk>
       \<Longrightarrow> graph_matching (g_to_set E) (g_to_set M) \<and> vset_set R \<subseteq> Vs (g_to_set M) \<and> g_invar M"
    "\<And> E A B R S NS. 
      \<lbrakk>bipartite (g_to_set E) A B; g_invar E; vset_invar R;
       find_matching_or_witness E R = witness S NS\<rbrakk>
       \<Longrightarrow> vset_set S \<subseteq> vset_set R \<and> vset_invar S \<and> vset_invar NS \<and> 
           (vset_set S \<subseteq> A \<or> vset_set S \<subseteq> B) \<and> card (vset_set NS) < card (vset_set S) \<and>
           vset_set NS = Neighbourhood (g_to_set E) (vset_set S)"
begin

lemma finiteG: "finite G"
proof-
  obtain es where "set_of_pair ` set es = g_to_set G_impl"
    using g_iterations(1)[OF G_props(1)] by blast
  thus ?thesis
    by(auto simp add: G_props(2))
qed

lemma finite_vset: 
  assumes "vset_invar S" 
  shows "finite (vset_set S)"
proof-
  obtain vs where "vset_set S = set vs"
    using vset_iterations(1) [OF assms(1)] by blast
  thus ?thesis 
    by simp
qed

definition "L = vset_set lefts"
definition "R = vset_set rights"
definition "LR = L \<union> R"

lemma basic_graph_props: 
  "Vs G \<subseteq> LR" "LR = L \<union> R" "L \<inter> R = {}" "bipartite G L R"
  "\<lbrakk>x \<in> L; {x, y} \<in> G\<rbrakk> \<Longrightarrow> y \<in> R"
  "\<lbrakk>y \<in> R; {x, y} \<in> G\<rbrakk> \<Longrightarrow> x \<in> L"
  "\<lbrakk>x \<in> R; y \<in> R; {x, y} \<in> G\<rbrakk> \<Longrightarrow> False"
  "\<lbrakk>x \<in> L; y \<in> L; {x, y} \<in> G\<rbrakk> \<Longrightarrow> False"
  "\<lbrakk>x \<notin> L; x \<in> Vs G\<rbrakk> \<Longrightarrow> x \<in> R"
  "\<lbrakk>x \<notin> R; x \<in> Vs G\<rbrakk> \<Longrightarrow> x \<in> L"
  "finite L" "finite R" "finite LR"
  using G_props(3,5,7,6) 
  by(force simp add: LR_def L_def R_def bipartite_def Vs_def)+

lemmas vertices_isin = vset.set_isin[OF G_props(4)]
lemmas in_lefts_in_L= vset.set_isin[OF G_props(4), folded L_def]

lemma graph_invar_G: "graph_invar G"
  using basic_graph_props(4) finiteG
  by(auto intro!: finite_bipartite_graph_invar)

lemma in_G_sym_slack: 
  "{u, v} \<in> G \<Longrightarrow> edge_slack p u v = edge_slack p v u"
  by(auto simp add: edge_slack_def intro!:  sym_weights)

definition "pair_weight e =  weight (fst e) (snd e)"

lemma pair_weight_fold: "weight u v = pair_weight (u, v)"
  by(auto simp add: pair_weight_def)

subsection \<open>Properties of Auxiliary Functions\<close>

lemma init_potential_props:
  "p_invar init_potential"
  "abstract_real_map (p_lookup init_potential) =
   (\<lambda> v. if v \<in> L then Max (insert 0 {weight v u | u. {u, v} \<in> G}) else 0)"
  "dom (p_lookup init_potential) \<subseteq> L"
proof-
  define it where "it = (\<lambda> (u, v) pmap.
           if vset_isin lefts u \<and> abstract_real_map (p_lookup pmap) u < weight u v
           then p_update u (weight u v) pmap
           else if vset_isin lefts v \<and> abstract_real_map (p_lookup pmap) v < weight u v
           then p_update v (weight u v) pmap
           else pmap)"
  obtain es where es_prop:"pair_list_distinct es"
    "set_of_pair ` set es = g_to_set G_impl" 
    "g_iterate_p G_impl it p_empty = foldr it es p_empty"
    using g_iterations(1)[OF G_props(1)] by blast
  have p_invar_after_its: "p_invar p \<Longrightarrow> p_invar (foldr it es p)" for es p
    by(induction es)
      (auto simp add: it_def split: prod.split intro: p_map.invar_update)
  have  es_in_G:"set_of_pair ` set es \<subseteq> G" 
    by (simp add: G_props(2) es_prop(2))
  have abstract_real_map_after_its_is:
    "abstract_real_map (p_lookup (foldr it es p_empty)) =
    (\<lambda> v. if v \<in> L then Max (insert 0 {weight v u | u. (u, v) \<in> set es \<or> (v, u) \<in> set es}) else 0)" 
  if "pair_list_distinct es" "set_of_pair ` set es \<subseteq> G"
    using that
  proof(induction es)
    case Nil
    then show ?case 
      by(auto simp add: p_map.map_empty abstract_real_map_empty)
  next
    case (Cons e es)
    have iprem: "pair_list_distinct es" "set_of_pair ` set es \<subseteq> G"
      using Cons(2,3) by auto
    have es_weight_sym: "(u, v) \<in> set (e#es) \<Longrightarrow> weight u v = weight v u" for u v
      using Cons.prems(2)
      by(auto intro!: sym_weights simp add: image_subset_iff  set_of_pair_applied_to_pair)
    have Max_is: " Max ({0} \<union> {weight v u |  u. (u, v) \<in> set (e # es) \<or>
                                                (v, u) \<in> set (e # es)}) = 
                 (if fst e = v \<or> snd e = v then max (weight (fst e) (snd e)) 
                     (Max ({0} \<union> {weight v u |  u. (u, v) \<in> set es \<or> (v, u) \<in> set es}))
                 else Max ({0} \<union> {weight v u |  u. (u, v) \<in> set es \<or> (v, u) \<in> set es}))" for v
    proof(subst linorder_class.Max_insert[symmetric], goal_cases)
      case 1 
      show ?case
        by(rule finite_union_singleton[OF 
                   finite_subset[of _ "pair_weight ` (set es \<union> prod.swap ` set es)"]])
          (auto simp add: pair_weight_fold)
    qed(auto intro!: arg_cong[of _ _ Max ] 
              intro: exI[of _ "snd e"]
           simp add: split_pairs  es_weight_sym)
    show ?case  
    proof(subst foldr.simps, subst o_apply, subst it_def, goal_cases)
      case 1
      show ?case
      using Cons(3) basic_graph_props(1,2,3) sym_weights Max_is
      by(auto split: prod.split if_split
          intro!: ext
          simp add: p_map.map_update[OF p_invar_after_its, OF p_map.invar_empty]
          abstract_real_map_fun_upd Cons(1)[OF iprem]   vertices_isin[folded L_def]
          set_of_pair_applied_to_pair 
          dest: basic_graph_props(7,8))
    qed
  qed
  have es_weight_sym: "(u, v) \<in> set (es) \<Longrightarrow> weight u v = weight v u" for u v
    using  es_prop(2)
    by(auto intro!: sym_weights 
             dest!: imageI[of "(u, v)" "set es" set_of_pair]
          simp add: set_of_pair_applied_to_pair G_props(2) rev_image_eqI)
  have same_weights:
    "{weight v u |u. (u, v) \<in> set es \<or> (v, u) \<in> set es} = {weight v u |u. {u, v} \<in> G}" for v
    using es_prop(2)[simplified G_props(2), symmetric] es_weight_sym
    by (auto simp add: set_of_pair_def doubleton_eq_iff)
  have dom_prop: "dom (p_lookup (foldr it es p_empty)) \<subseteq> ((fst ` set es) \<union> (snd ` set es)) \<inter> L"
    using p_map.map_update[OF p_invar_after_its, OF p_map.invar_empty] 
    by(induction es)(auto simp add:  it_def in_lefts_in_L p_map.map_empty split: if_split prod.split)
  show "p_invar init_potential"
    "abstract_real_map (p_lookup init_potential) =
         (\<lambda> v. if v \<in> L then Max (insert 0 {weight v u | u. {u, v} \<in> G}) else 0)"
    "dom (p_lookup init_potential) \<subseteq> L"
    using same_weights  dom_prop 
    by (auto simp add: p_invar_after_its p_map.invar_empty
        abstract_real_map_after_its_is[OF  es_prop(1)  es_in_G]
        init_potential_def[folded it_def] es_prop(3))
qed

lemma build_tight_graph_props:
  "g_invar (build_tight_graph pmap)"
  "g_to_set (build_tight_graph pmap) = {{u, v} | u v. {u, v} \<in> G \<and> edge_slack pmap u v = 0}"
proof-
  define it where 
    "it = (\<lambda>(u, v) tights. if edge_slack pmap u v = 0 then g_insert u v tights else tights)"
  obtain es where es_prop:"pair_list_distinct es"
    "set_of_pair ` set es = g_to_set G_impl" "g_iterate_g G_impl it g_empty = foldr it es g_empty"
    using g_iterations(3)[OF G_props(1), of it g_empty] by auto
  have g_invar:"g_invar (foldr it es g_empty)" for es
    by(induction es)(auto simp add: it_def g_basic_operations(1,3))
  have g_set_is:
    "g_to_set (foldr it es g_empty) = {{u, v} | u v. (u, v) \<in> set es \<and> edge_slack pmap u v = 0}"
    by(induction es)
      (auto simp add: g_basic_operations(5) if_distrib g_basic_operations(4)[OF g_invar]
        cong[OF cong[OF it_def refl] refl, of _ "foldr _ _ _"]
        split: if_split
        | subst (asm) (11) if_split[of _ "edge_slack pmap _ _ = 0"])+
  show "g_invar (build_tight_graph pmap)"
    "g_to_set (build_tight_graph pmap) = {{u, v} | u v. {u, v} \<in> G \<and> edge_slack pmap u v = 0}"
    using g_invar g_set_is es_prop(2) in_G_sym_slack
    by (auto simp add:  build_tight_graph_def it_def[symmetric] es_prop(3) G_props(2) set_of_pair_def )
       (subst (asm) doubleton_eq_iff | 
        fastforce intro!: exI[of "\<lambda> x. \<exists> y. {a, b } = {x, y} \<and> (x, y) \<in> set es 
                                           \<and> edge_slack pmap x y = 0" for a b,
          OF exI])+
qed

lemma find_epsilon_props:
  assumes "vset_invar S"
  shows "find_\<epsilon> pmap S = 
         Min (insert PInfty ({edge_slack pmap u v | u v. 
                  vset_isin S u \<and> {u, v} \<in> G \<and> edge_slack pmap u v \<noteq> 0} 
              \<union> {abstract_real_map (p_lookup pmap) v | v. vset_isin S v}))"
proof-
  define it_e where "it_e = (\<lambda>(u, v) val.
         let sl = edge_slack pmap u v
         in if sl \<noteq> 0 \<and> ereal sl < val \<and> (vset_isin S u \<or> vset_isin S v) then ereal sl else val)"
  define it_v where "it_v = (\<lambda>u val.
         let pu = abstract_real_map (p_lookup pmap) u in if ereal pu < val then ereal pu else val)"
  obtain es where es_prop:"pair_list_distinct es"
    "set_of_pair ` set es = g_to_set G_impl" 
    "g_iterate_real G_impl it_e PInfty = foldr it_e es PInfty"
    using g_iterations(2)[OF G_props(1)] by blast
  obtain vs where vs_prop: "distinct vs" "set vs = vset_set S" 
                           "vset_iterate_real S it_v PInfty = foldr it_v vs PInfty"
    using vset_iterations(1)[OF assms(1), of it_v PInfty] by auto
  have helper1: False 
    if "ereal (edge_slack pmap b a) \<notin> (\<lambda>x. ereal (edge_slack pmap (fst x) (snd x))) ` set es"
       "(a, b) \<in> set es" for a b
    using that
    apply(subst (asm) edge_slack_cong(2)[of b a a b, OF _ refl refl])
    using sym_weights[of a b] imageI  set_of_pair_applied_to_pair[of a b] 
      es_prop(2)[simplified G_props(2)] 
    by fastforce force
  have finites2: "finite ({ereal (edge_slack pmap u v) |u v.
                        vset_isin S u \<and> {u, v} \<in> set_of_pair ` set es \<and> edge_slack pmap u v \<noteq> 0})"
    using  helper1
    by(intro finite_subset[of _ "(\<lambda> (u, v). ereal (edge_slack pmap u v)) ` set (es)",
           OF _ finite_imageI], 
       auto simp add: set_of_pair_def doubleton_eq_iff case_prod_beta 
               intro: edge_slack_cong) force+
  have min_edges:
   "foldr it_e es PInfty = Min (insert PInfty {ereal (edge_slack pmap u v) |u v.
           vset_isin S u \<and> {u, v} \<in> set_of_pair ` set es \<and> 0 \<noteq> edge_slack pmap u v})"
    using sym_weights  es_prop(1) 
    unfolding es_prop(2)[simplified G_props(2), symmetric]
  proof(induction es)
    case (Cons e es)
    obtain x y where e_split:"e = (x, y)" by (cases e) auto
    have helper1: False
      if "ereal (edge_slack pmap b a) \<notin> (\<lambda>x. ereal (edge_slack pmap (fst x) (snd x))) ` set es"
         "(a, b) \<in> set es" for a b
      using that 
      apply(subst (asm) edge_slack_cong(2)[of b a a b, OF _ refl refl])
      using Cons.prems(1)[of a b] imageI  set_of_pair_applied_to_pair[of a b] 
      by fastforce force
    have finites: "finite {ereal (edge_slack pmap u v) |u v. vset_isin S u \<and>
      ({u, v} = set_of_pair e \<or> {u, v} \<in> set_of_pair ` set es) \<and>  edge_slack pmap u v \<noteq> 0}"   
      using Cons(2)[of x y] helper1 (*takes some time*)
      by (intro finite_subset[of _ "(\<lambda> (u, v). ereal (edge_slack pmap u v)) ` set (e#es)", 
            OF _ finite_imageI],
          auto simp add: e_split set_of_pair_def doubleton_eq_iff case_prod_beta 
          intro: edge_slack_cong) force+
    have finites2: "finite ({ereal (edge_slack pmap u v) |u v.
                       vset_isin S u \<and> {u, v} \<in> set_of_pair ` set es \<and> edge_slack pmap u v \<noteq> 0})"
      using  helper1
      by(intro finite_subset[of _ "(\<lambda> (u, v). ereal (edge_slack pmap u v)) ` set (es)",
            OF _ finite_imageI],
         auto simp add: e_split set_of_pair_def doubleton_eq_iff case_prod_beta 
                 intro: edge_slack_cong) force+
    have xy_same_slack: "edge_slack pmap x y = edge_slack pmap y x"
      using Cons.prems(1)[of x y] 
      by(auto intro!: edge_slack_cong(2) simp add:  e_split set_of_pair_applied_to_pair)
    have in_e_same_slack: 
      "(a, b) \<in> set es \<Longrightarrow> edge_slack pmap a b = edge_slack pmap b a"
      "(b, a) \<in> set es \<Longrightarrow> edge_slack pmap a b = edge_slack pmap b a"
      "(a, b) \<in> set es \<Longrightarrow> weight a b = weight b a"
      "(b, a) \<in> set es \<Longrightarrow> weight a b = weight b a" for a b            
      using Cons.prems(1)[of a b] 
      by(auto intro: edge_slack_cong simp add:  set_of_pair_def)
    have IH_applied: "foldr it_e es PInfty =
     Min ({PInfty} \<union>  {ereal (edge_slack pmap u v) |u v.
                        vset_isin S u \<and> {u, v} \<in> set_of_pair ` set es \<and> 0 \<noteq> edge_slack pmap u v})"
      using Cons(2,3)
      by(auto intro!: Cons(1)[simplified])
    show ?case 
      apply(subst foldr.simps, subst o_apply, subst it_e_def, subst e_split, subst prod.case)
    proof(subst linorder_class.eq_Min_iff, goal_cases)
      case 1
      then show ?case 
        by (auto simp add: e_split finites[simplified e_split] Let_def)
    next
      case 2
      then show ?case 
        by(auto simp add: e_split finites[simplified e_split] Let_def)
    next
      case 3
      have helper: "foldr it_e es \<infinity> = \<infinity>" 
        if"\<forall>u. vset_isin S u \<longrightarrow>
             (\<forall>v. foldr it_e es \<infinity> = ereal (edge_slack pmap u v) \<longrightarrow>
             {u, v} \<noteq> set_of_pair (x, y) \<and> {u, v} \<notin> set_of_pair ` set es \<or>
             edge_slack pmap u v = 0)"
          "\<not> ereal (edge_slack pmap x y) < foldr it_e es \<infinity> 
              \<or> edge_slack pmap x y = 0 \<or> (\<not> vset_isin S x \<and> \<not> vset_isin S y)"
        using that IH_applied[simplified] Min_in[OF finite.insertI[OF finites2], of \<infinity>, simplified]  
        by auto
      show ?case 
      proof(rule, goal_cases)
        case 1
        then show ?case 
          using helper
          by(auto intro: exI[of "\<lambda> u. \<exists>v. _ x y = _ u v \<and> _ u v", OF exI, of _ _ x y, OF conjI]
               simp add: set_of_pair_applied_to_pair doubleton_eq_iff Let_def
                         xy_same_slack  in_e_same_slack  e_split finites[simplified e_split])
      next
        case 2
        have helper1: 
          "{u, v} = set_of_pair e \<Longrightarrow> edge_slack pmap x y \<le> edge_slack pmap u v" for u v
          using IH_applied[simplified] xy_same_slack
          by(auto simp add: e_split set_of_pair_applied_to_pair doubleton_eq_iff)
        have prop1: "\<lbrakk>(a, b) \<in> set es; vset_isin S a; edge_slack pmap a b \<noteq> 0\<rbrakk>
                      \<Longrightarrow> foldr it_e es \<infinity> \<le>  edge_slack pmap a b" for a b
          using Min.bounded_iff[OF finite.insertI[OF finites2],
                                    of \<infinity>, simplified, of "foldr it_e es \<infinity>"]
                image_eqI[of "{a, b}" set_of_pair "(a, b)" "set es", 
                                 simplified set_of_pair_applied_to_pair]
          by(auto simp add: IH_applied[simplified])
        have prop2: "\<lbrakk>(b, a) \<in> set es; vset_isin S a; edge_slack pmap a b \<noteq> 0\<rbrakk>
                       \<Longrightarrow> foldr it_e es \<infinity> \<le>  edge_slack pmap a b" for a b
          using Min.bounded_iff[OF finite.insertI[OF finites2],
                                   of \<infinity>, simplified, of "foldr it_e es \<infinity>"]
                image_eqI[of "{b, a}" set_of_pair "(b, a)" "set es", 
                                   simplified set_of_pair_applied_to_pair]
          by(fastforce simp add: IH_applied[simplified] )
        have helper2: "edge_slack pmap x y \<le> edge_slack pmap u v" 
          if "ereal (edge_slack pmap x y) < foldr it_e es \<infinity>" "vset_isin S u"
             "edge_slack pmap u v \<noteq> 0" "{u, v} = set_of_pair (a, b)" "(a, b) \<in> set es" 
          for a b u v
          using that
          by(auto simp add: set_of_pair_def doubleton_eq_iff ereal_less_eq(3)[symmetric]
                  simp del: ereal_less_eq(3)
                     intro: order.trans[OF _ prop2, of _ a b] order.trans[OF _ prop1, of _ a b])
        have helper3: "\<lbrakk>edge_slack pmap u v \<noteq> 0; {u, v} = set_of_pair e; edge_slack pmap x y = 0\<rbrakk>
                         \<Longrightarrow> foldr it_e es \<infinity> \<le> ereal (edge_slack pmap u v)" for u v
          by(auto simp add: doubleton_eq_iff e_split set_of_pair_applied_to_pair xy_same_slack)
        have helper4: "\<lbrakk>vset_isin S u; {u, v} = set_of_pair e; \<not> vset_isin S x; \<not> vset_isin S y\<rbrakk>
                        \<Longrightarrow> foldr it_e es \<infinity> \<le> ereal (edge_slack pmap u v)" for u v
          by(auto simp add: doubleton_eq_iff e_split set_of_pair_applied_to_pair xy_same_slack)
        have helper5: "\<lbrakk>vset_isin S u;  edge_slack pmap u v \<noteq> 0; {u, v} = set_of_pair (a, b);
                        (a, b) \<in> set es\<rbrakk> 
                        \<Longrightarrow> foldr it_e es \<infinity> \<le> ereal (edge_slack pmap u v)" for u v a b
          by(auto simp add: prop1 prop2 doubleton_eq_iff set_of_pair_applied_to_pair )
        have helper6: "\<lbrakk>{u, v} = set_of_pair e; \<not> ereal (edge_slack pmap x y) < foldr it_e es \<infinity>\<rbrakk> 
                        \<Longrightarrow> foldr it_e es \<infinity> \<le> ereal (edge_slack pmap u v)" for u v
          by(auto dest!: helper1 intro: leI le_ereal_le)
        show ?case
          using helper2
          by(auto simp add: Let_def intro: helper1 helper2 helper3 helper4 helper5 helper6)
      qed
    qed
  qed simp
  have vs_min_is:
    "foldr it_v vs PInfty = 
     Min (insert PInfty {ereal (abstract_real_map (p_lookup pmap) v) |v. v \<in> set vs})"
  proof(induction vs)
    case (Cons v vs)
    have min_is:
      "Min ({\<infinity>} \<union> {ereal (abstract_real_map (p_lookup pmap) va) |va. va = v \<or> va \<in> set vs})
        = min  (ereal (abstract_real_map (p_lookup pmap) v)) 
         (Min ({\<infinity>} \<union> {ereal (abstract_real_map (p_lookup pmap) va) |va.  va \<in> set vs}))"
      by(subst linorder_class.Min_insert[symmetric])
        (force intro!: arg_cong[of _ _ Min])+
    have less_Min:
      "Min ({\<infinity>} \<union> {ereal (abstract_real_map (p_lookup pmap) v) |v. v \<in> set vs})
       \<le> ereal (abstract_real_map (p_lookup pmap) v)" 
      if "abstract_real_map (p_lookup pmap) v \<ge> abstract_real_map (p_lookup pmap) va"
         "va \<in> set vs"  for va
      using that(2) 
      by(auto intro!: order.trans[OF _  that(1)[simplified ereal_less_eq(3)[symmetric]]]
          linorder_class.Min.coboundedI)
    show ?case 
      apply(simp add: Cons[simplified])
      apply(subst it_v_def)
      using min_is less_Min   linorder_not_le
      by(subst Orderings.min_absorb2 | auto simp add: Let_def split: if_split)+
  qed simp
  show ?thesis
    using vs_prop(2)[symmetric] finites2
    by(unfold find_\<epsilon>_def it_e_def[symmetric] it_v_def[symmetric] es_prop(3) vs_prop(3)
        es_prop(2)[simplified G_props(2), symmetric] min_edges vs_prop(2)[symmetric]
        vs_min_is)
      (auto simp add: linorder_class.Min_Un[symmetric] 
                      vset.set_isin[OF assms(1)] vs_prop(2)[symmetric])
qed

lemma lefts_and_rights_props:
  "vset_invar lefts_and_rights"
  "vset_set lefts_and_rights = LR"
  by(auto simp add: lefts_and_rights_def  G_props(4,5) vset.invar_union
      vset.set_union LR_def L_def R_def)

lemma find_bads_props:
  "vset_invar (find_bads pmap)"
  "vset_set (find_bads pmap) = {v | v. v \<in> LR \<and> abstract_real_map (p_lookup pmap) v > 0}"
proof-
  define it where 
     "it = (\<lambda>v S. if 0 < abstract_real_map (p_lookup pmap) v then vset_insert v S else S)"
  obtain vs where vs: "distinct vs" "set vs = vset_set lefts_and_rights"
    "vset_iterate_vset lefts_and_rights it vset_empty = foldr it vs vset_empty"
    using  vset_iterations(2)[OF lefts_and_rights_props(1), of it vset_empty] by auto
  have vset_invar: "vset_invar (foldr it vs vset_empty)" for vs
    by(induction vs)
      (auto simp add: it_def vset.invar_empty vset.invar_insert)
  have set_is:
    "vset_set (foldr it vs vset_empty) = 
     {v |v. v \<in> set vs \<and> 0 < abstract_real_map (p_lookup pmap) v}"
  proof(induction vs)
    case Nil
    then show ?case 
      by(simp add: vset.set_empty)
  next 
    case (Cons v vs)
    show ?case
      using Cons 
      by(subst foldr.simps, subst o_apply, subst it_def)
        (auto simp add: vset.set_insert[OF vset_invar])
  qed
  show "vset_invar (find_bads pmap)"
       "vset_set (find_bads pmap) = {v | v. v \<in> LR \<and> abstract_real_map (p_lookup pmap) v > 0}"
    by (auto simp add: vset_invar find_bads_def it_def[symmetric] vs(2,3) set_is 
                       lefts_and_rights_props(2))
qed

abbreviation "potential pmap \<equiv> (abstract_real_map (p_lookup pmap))"

lemma Collect_vset_set:
  "vset_invar S \<Longrightarrow> Collect (vset_isin S) = vset_set S"
  using vset.set_isin by auto

definition "w = (\<lambda> e. weight (pick_one e) (pick_another e))"

lemma w_weight_cong: "{u, v} \<in> G \<Longrightarrow> w {u, v} = weight u v"
  using basic_graph_props(6,8) [of u v]
    doubleton_eq_iff[of u v "pick_one {u, v}" "pick_another {u, v}"] edges_are_Vs_2[of u v G]
    basic_graph_props(9)[of u]
    pick_one_and_another_props(3)[of "{u, v}"] sym_weights[of u v]
  by(auto simp add: w_def) 

subsection \<open>One Step and Invariants\<close>

lemma naive_primal_dual_one_step:
  assumes "naive_primal_dual_call_cond pmap" "p_invar pmap"
          "feasible_max_dual LR G w (abstract_real_map (p_lookup pmap))"
  shows   "p_invar (naive_primal_dual_call pmap)"
          "feasible_max_dual LR G w (abstract_real_map (p_lookup (naive_primal_dual_call pmap)))"
    and  "\<exists> \<alpha> > 0. sum  (abstract_real_map (p_lookup (naive_primal_dual_call pmap))) LR + \<alpha> =
                    sum (abstract_real_map (p_lookup pmap)) LR
         \<and> (epsilon_multiples \<epsilon> w G \<and> epsilon_multiples \<epsilon> (potential pmap) LR \<longrightarrow>
             epsilon_multiples \<epsilon> id {\<alpha>} 
             \<and> epsilon_multiples \<epsilon> (potential (naive_primal_dual_call pmap)) LR)" (is ?long_thesis)
proof-
  define tights where "tights = build_tight_graph pmap"
  define bads where "bads = find_bads pmap"
  obtain S NS where S_NS_def:"witness S NS = find_matching_or_witness tights bads"
    using assms(1)
    by(auto elim!: naive_primal_dual_call_condE 
        simp add: tights_def bads_def) 
  define \<alpha> where  "\<alpha> = real_of_ereal (find_\<epsilon> pmap S)"
  define pmap' where "pmap' = vset_iterate_pmap S
                  (\<lambda> v p. p_update v (abstract_real_map (p_lookup pmap) v - \<alpha>) p) pmap"
  define pmap'' where "pmap'' = vset_iterate_pmap NS
                  (\<lambda> v p. p_update v (abstract_real_map (p_lookup pmap) v + \<alpha>) p) pmap'"
  have pmap''_is_call:"naive_primal_dual_call pmap = pmap''"
    using  S_NS_def[symmetric]
    by(auto simp add: naive_primal_dual_call_def pmap''_def pmap'_def 
                      \<alpha>_def bads_def tights_def Let_def)
  note tight_graph_props = build_tight_graph_props[of pmap, folded tights_def]
  note find_bad_props = find_bads_props[of pmap, folded bads_def]
  have tights_bipartite: "bipartite (g_to_set tights) L R"
    by(rule bipartite_subgraph)(auto simp add: tight_graph_props(2) basic_graph_props(4))
  have S_NS_props: "vset_set S \<subseteq> vset_set bads" "(vset_set S \<subseteq> L \<or> vset_set S \<subseteq> R)"
    "vset_set NS = Neighbourhood (g_to_set tights) (vset_set S)"
    "card (vset_set NS) < card (vset_set S)"
    " vset_invar S" "vset_invar NS"
    using find_matching_or_witness(2)[OF tights_bipartite tight_graph_props(1) find_bad_props(1)
        S_NS_def[symmetric]]
    by simp+
  have S_NS_in_LR: "vset_set S \<subseteq> L  \<Longrightarrow> vset_set NS \<subseteq> R" 
                   "vset_set S \<subseteq> R  \<Longrightarrow> vset_set NS \<subseteq> L"
  proof(goal_cases)
    case 1
    thus ?case
      using tights_bipartite S_NS_props(3) Neighbourhood_bipartite_left by blast
  next
    case 2
    thus ?case
      using Neighbourhood_bipartite_right S_NS_props(3) tights_bipartite by blast
  qed
  have S_non_empty: "vset_set S \<noteq> {}"
    using S_NS_props(4) by auto
  hence S_non_empty':  "\<exists> x. vset_isin S x"
    by (auto simp add: vset.set_isin[OF S_NS_props(5)])
  have finite_S: "finite (Collect (vset_isin S))" "finite (vset_set S)"
    using S_NS_props(2,5)   vset.set_isin[OF S_NS_props(5)]
    by(auto simp add: finite_subset subset_iff  Collect_vset_set intro!:  finite_vset)
  have eps_eral_is:
  "\<alpha> = real_of_ereal (Min ({PInfty} \<union>
       ({ereal (edge_slack pmap u v) |u v. vset_isin S u \<and> {u, v} \<in> G \<and> edge_slack pmap u v \<noteq> 0} \<union>
       {ereal (potential pmap v) |v. vset_isin S v})))"
    using find_epsilon_props[OF S_NS_props(5)]
    by(simp add: \<alpha>_def)
  have finite_slacks: "finite {edge_slack pmap u v |u v. 
                           vset_isin S u \<and> {u, v} \<in> G \<and> edge_slack pmap u v \<noteq> 0}"
    using finiteG
    by(force intro: finite_subset[of _ "{edge_slack pmap u v |u v. {u, v} \<in> G}"] 
                    finite_pairs_of_finite_set_set
          simp add: image_two_Collect)
  have finite_ys: "finite {(potential pmap v) |v. vset_isin S v}"
    using S_NS_props(2) finite_subset 
    by (auto intro!: finite_imageI 
        simp add: image_Collect[symmetric] vset.set_isin S_NS_props(5) finite_S(2))
  have alpha_is:
   "\<alpha> = Min ({(edge_slack pmap u v) |u v. vset_isin S u \<and> {u, v} \<in> G \<and> edge_slack pmap u v \<noteq> 0} \<union>
             {(potential pmap v) |v. vset_isin S v})"
    using S_non_empty'  finite_S 
    by(auto intro: finite_g_applied_double finite_g_applied_single 
        simp add: finite_slacks finite_ys Collect_double_f_to_single[of ereal]
        Min_bigger[symmetric] Collect_single_f_to_single[of ereal "potential pmap"]
        eps_eral_is Un_commute[of "{PInfty}"] setcompr_eq_image image_Un[symmetric] 
        real_of_ereal_of_Min_or_ereal)
  have alpha_in: 
   "\<alpha> \<in> {(edge_slack pmap u v) |u v. vset_isin S u \<and> {u, v} \<in> G \<and> edge_slack pmap u v \<noteq> 0} \<union>
        {(potential pmap v) |v. vset_isin S v}"
    unfolding alpha_is
    using finite_slacks finite_ys  S_non_empty' 
    by (intro Min_in) force+
  hence alpha_witness: 
    "(\<exists> u v.  vset_isin S u \<and> {u, v} \<in> G \<and> edge_slack pmap u v \<noteq> 0 \<and> \<alpha> = (edge_slack pmap u v))
        \<or> (\<exists> v. \<alpha> = (potential pmap v) \<and> vset_isin S v)"
    by auto
  hence alpha_gtr_0:"\<alpha> > 0"
    using feasible_max_dualD(2)[OF assms(3) _ refl]
      Collect_vset_set S_NS_props(1,5) find_bad_props(2)
    by (force simp add:  w_weight_cong edge_slack_def)
  have alpha_less: 
    "\<lbrakk>vset_isin S u; {u, v} \<in> G; edge_slack pmap u v \<noteq> 0\<rbrakk> \<Longrightarrow> \<alpha> \<le> edge_slack pmap u v"
    "vset_isin S v \<Longrightarrow> \<alpha> \<le> (potential pmap v)"
    for u v
    using finite_slacks finite_ys 
    by(auto intro!: linorder_class.Min.coboundedI simp add: alpha_is)
  obtain vs where vs:"distinct vs" "set vs = vset_set S"
    "vset_iterate_pmap S (\<lambda>v. p_update v (potential pmap v - \<alpha>)) pmap =
       foldr (\<lambda>v. p_update v (potential pmap v - \<alpha>)) vs pmap"
    using vset_iterations(3)[OF S_NS_props(5), of "\<lambda>v. p_update v (potential pmap v - \<alpha>)" pmap]
    by auto
  have p_invar_it:
   "p_invar pmap \<Longrightarrow> p_invar (foldr (\<lambda>v. p_update v (f v + x)) vs pmap)" for x pmap vs f
    by(induction vs)(auto simp add: p_map.invar_update)
  have p_invar_not_in_vs_no_change:
    "\<lbrakk>p_invar pmap; v \<notin> set vs\<rbrakk> \<Longrightarrow>
        potential (foldr (\<lambda>v. p_update v (potential pmap v + x)) vs pmap) v = potential pmap v"
    for x pmap vs v
    by(induction vs)
      (auto simp add: abstract_real_map_fun_upd p_invar_it p_map.map_update)
  have pmap'_is:"potential (foldr (\<lambda>v. p_update v (potential pmap v - \<alpha>)) vs pmap) =
       (\<lambda> v. if v \<in> set vs then potential pmap v - \<alpha> else potential pmap v)"
    using vs(1)
  proof(induction vs)
    case (Cons v vs)
    show ?case
    proof(rule ext, goal_cases)
      case (1 vv)
      show ?case 
        using Cons 
        by(subst foldr.simps, subst o_apply, subst p_map.map_update)
          (auto intro!: p_invar_it[where x = "- \<alpha>", simplified] 
            simp add:  assms(2) abstract_real_map_fun_upd )
    qed
  qed auto
  have p_invar_pmap': "p_invar pmap'"
    using assms(2) minus_real_def p_invar_it pmap'_def vs(3) by presburger
  obtain vs' where vs':"distinct vs'"
    "set vs' = vset_set NS"
    "vset_iterate_pmap NS (\<lambda>v. p_update v (potential pmap v + \<alpha>)) pmap' =
       foldr (\<lambda>v. p_update v (potential pmap v + \<alpha>)) vs' pmap'"
    using vset_iterations(3)[OF S_NS_props(6), of "\<lambda>v. p_update v (potential pmap v + \<alpha>)" pmap']
    by auto
  have pmap''_is:"potential (foldr (\<lambda>v. p_update v (potential pmap v + \<alpha>)) vs' pmap') =
       (\<lambda> v. if v \<in> set vs' then potential pmap v + \<alpha> else potential pmap' v)"
    using vs'(1)
  proof(induction vs')
    case (Cons v vs')
    show ?case
    proof(rule ext, goal_cases)
      case (1 vv)
      show ?case 
        using Cons 
        by(subst foldr.simps, subst o_apply, subst p_map.map_update)
          (auto intro!: p_invar_it
            simp add:  abstract_real_map_fun_upd  p_invar_pmap')
    qed
  qed auto
  show "p_invar (naive_primal_dual_call pmap)" 
    using p_invar_pmap' 
    by(auto intro: p_invar_it simp add:  pmap''_is_call pmap''_def vs'(3))
  have pmap''_effect: "potential pmap'' = 
         (\<lambda> v. if v \<in> vset_set NS then potential pmap v + \<alpha>
               else if v \<in> vset_set S then potential pmap v - \<alpha>
               else potential pmap v)"
    using vs(2) vs'(2)
    by(unfold pmap''_def vs'(3) pmap''_is)(auto simp add: pmap'_def vs(3) pmap'_is)
  show "feasible_max_dual LR G w (potential (naive_primal_dual_call pmap))"
    unfolding pmap''_is_call
  proof(rule feasible_max_dualI, goal_cases)
    case (1 v)
    show ?case 
      using  feasible_max_dualD(1)[OF assms(3) 1] alpha_gtr_0
      by(auto simp add: pmap''_effect S_NS_props(5) vset.set_isin intro!: alpha_less(2))
  next
    case (2 e u v)
    hence "{v, u} \<in> G" "{u, v} \<in> G" by (auto simp add: insert_commute)
    moreover have "u \<in> vset_set S \<Longrightarrow> v \<in> vset_set S \<Longrightarrow> False"
      using "2"(1,2) S_NS_props(2) basic_graph_props(7,8) subsetD by fastforce
    moreover have "u \<in> vset_set S \<Longrightarrow> u \<in> vset_set NS \<Longrightarrow> False" 
      by(auto simp add: S_NS_props(3) self_not_in_Neighbourhood)
    moreover have "potential pmap u + potential pmap v = weight u v \<Longrightarrow>  u \<in> vset_set S \<Longrightarrow>
                   v \<notin> vset_set NS \<Longrightarrow>  False"
      using 2 calculation(3)
      by(auto simp add: S_NS_props(3) tight_graph_props(2)
          edge_slack_def algebra_simps doubleton_eq_iff elim: not_in_NeighbourhoodE)  
    ultimately show ?case 
      using feasible_max_dualD(2)[OF assms(3) 2] feasible_max_dualD(1)[OF assms(3)]
        alpha_less(1)[of u v] w_weight_cong[of u v] alpha_less(1)[of v u] sym_weights[of v u]
        2 tight_graph_props(2) alpha_gtr_0
      by(auto simp add:  pmap''_effect edge_slack_def algebra_simps vset.set_isin[OF S_NS_props(5)]
          vset.set_isin[OF S_NS_props(6)] S_NS_props(3) Neighbourhood_def) fastforce 
  qed (auto intro: feasible_max_dualE[OF assms(3)])
  have LR_split: "LR = vset_set S \<union> vset_set NS \<union> (LR - (vset_set S \<union> vset_set NS))"
    "vset_set S \<inter> vset_set NS = {}"
    "(vset_set S \<union> vset_set NS) \<inter> (LR - (vset_set S \<union> vset_set NS)) = {}"
    using S_NS_in_LR S_NS_props(2)
    by(auto simp add: LR_def S_NS_props(3) self_not_in_Neighbourhood)
  have some_finites: "finite (vset_set S \<union> vset_set NS)"
    "finite (LR - (vset_set S \<union> vset_set NS))"
    "finite (vset_set S)" "finite (vset_set NS)"
    using basic_graph_props(13)
    by (auto simp add: S_NS_props(6) finite_S(2) finite_vset)
  have x_both_in_S_and_NS_False:"x \<in> vset_set S \<Longrightarrow> x \<in> vset_set NS \<Longrightarrow> False" for x
    by (simp add: S_NS_props(3) self_not_in_Neighbourhood)
  have change_sum_S:"sum (potential pmap) (vset_set S) - card (vset_set S) * \<alpha> =
            sum (potential pmap'') (vset_set S)"
    unfolding pmap''_effect
    apply(subst (2) sum_cong[where g = "\<lambda> x. potential pmap x - \<alpha>"])
    by(auto dest!: x_both_in_S_and_NS_False simp add: comm_monoid_add_class.sum.distrib[of _ "\<lambda> x. - \<alpha>", simplified])
  have change_sum_NS:"sum (potential pmap) (vset_set NS) + card (vset_set NS) * \<alpha> =
            sum (potential pmap'') (vset_set NS)"
    by(auto dest!: x_both_in_S_and_NS_False 
        simp add: pmap''_effect comm_monoid_add_class.sum.distrib[of _ "\<lambda> x.  \<alpha>", simplified]) 
  have not_change_other: "sum (potential pmap'') (LR - (vset_set S \<union> vset_set NS)) = 
                            sum (potential pmap) (LR - (vset_set S \<union> vset_set NS))"
    by(auto dest!: x_both_in_S_and_NS_False 
        simp add: pmap''_effect comm_monoid_add_class.sum.distrib[of _ "\<lambda> x.  \<alpha>", simplified]) 
  have sum_change:" sum (potential pmap'') LR =
           sum (potential pmap) LR -(card (vset_set S) - card (vset_set NS)) * \<alpha>"
    apply(subst LR_split(1), subst (2) LR_split(1))
    apply(subst comm_monoid_add_class.sum.union_disjoint[OF some_finites(1,2) LR_split(3)])+
    using alpha_gtr_0 S_NS_props(4) 
    by (auto simp add: comm_monoid_add_class.sum.union_disjoint[OF some_finites(3,4) LR_split(2)] 
        change_sum_S[symmetric] change_sum_NS[symmetric] not_change_other 
        algebra_simps )
  show ?long_thesis
    unfolding pmap''_is_call
  proof(rule exI[of _ "(card (vset_set S) - card (vset_set NS)) * \<alpha>"], goal_cases)
    case 1
    have "0 < real (card (vset_set S) - card (vset_set NS)) * \<alpha>"
      by (simp add: S_NS_props(4) alpha_gtr_0)
    moreover have "sum (potential pmap'') LR + real (card (vset_set S) - card (vset_set NS)) * \<alpha> =
                   sum (potential pmap) LR"
      by(simp add: sum_change)
    moreover have "epsilon_multiples \<epsilon> id {real (card (vset_set S) - card (vset_set NS)) * \<alpha>}"
      and "epsilon_multiples \<epsilon> (potential pmap'') LR"
      if "epsilon_multiples \<epsilon> w G" "epsilon_multiples \<epsilon> (potential pmap) LR"
    proof-
      have epsilon_multiple_alpha: "epsilon_multiples \<epsilon> id {\<alpha>}"
      proof(rule disjE[OF alpha_witness], goal_cases)
        case 1
        then obtain u v where uv: "vset_isin S u" "{u, v} \<in> G" "edge_slack pmap u v \<noteq> 0"
          "\<alpha> = edge_slack pmap u v" by auto
        hence uv_LR:"u \<in> LR" "v \<in> LR"
          using LR_split(1) S_NS_props(5) vset.set_isin basic_graph_props(1) edges_are_Vs_2[OF uv(2)]
          by auto
        have ex_x:"\<exists>x. \<alpha> = \<epsilon> * real x"
          if "\<epsilon> * real xb + \<epsilon> * real xc \<noteq> \<epsilon> * real xa" "\<alpha> + \<epsilon> * real xa = \<epsilon> * real xb + \<epsilon> * real xc"
            "\<alpha> \<le> \<epsilon> * real xb" "0 \<le> \<epsilon> * real xc" "\<epsilon> * real xa \<le> \<epsilon> * real xb + \<epsilon> * real xc" 
          for xa xb xc
          using that
        proof(intro exI[of _ "(xb + xc - xa)"], subst real_of_minus_distrib, goal_cases)
          case 1
          hence e_ps_gtr_0:"\<epsilon> > 0"
            using distrib_left[of \<epsilon> "real xb" "real xc"] 
                  mult_le_cancel_left_pos[of \<epsilon> "real xb" "real xc"]
                  mult_nonpos_nonneg[of \<epsilon> "real xb"]
            by force
          show ?case
            using iffD1[OF mult_le_cancel_left_pos[OF e_ps_gtr_0], of "real xa" "real xb + real xc"]
                  1 distrib_left[of \<epsilon> "real xb" "real xc"] 
            by linarith
        qed(auto simp add: algebra_simps)
        show ?case
          using epsilon_multiplesD[OF that(1) uv(2)] w_weight_cong[OF uv(2)]
            epsilon_multiplesD[OF that(2) uv_LR(1)] epsilon_multiplesD[OF that(2) uv_LR(2)]
            basic_graph_props(1) uv alpha_gtr_0
            alpha_less(1)[OF uv(1-3)] alpha_less(2)[OF uv(1)]
            feasible_max_dualD(1)[OF assms(3) uv_LR(1)]
            feasible_max_dualD(1)[OF assms(3) uv_LR(2)]
            feasible_max_dualD(2)[OF assms(3) uv(2) refl]
          by(auto intro!: epsilon_multiplesI ex_x
                simp add: edge_slack_def algebra_simps)
      next
        case 2
        then obtain v where v: "\<alpha> = potential pmap v" "vset_isin S v" by auto
        hence v_LR: "v \<in> LR"
          using LR_split(1) S_NS_props(5) vset.set_isin by auto
        show ?case
          using epsilon_multiplesD[OF that(1) ]
            epsilon_multiplesD[OF that(2) v_LR] 
            basic_graph_props(1) v 
            alpha_less(2)[OF v(2)]
            feasible_max_dualD(1)[OF assms(3) v_LR]
          by(auto intro!: epsilon_multiplesI
              simp add: edge_slack_def algebra_simps)
      qed
      show "epsilon_multiples \<epsilon> id {real (card (vset_set S) - card (vset_set NS)) * \<alpha>}"
      proof(rule epsilon_multiplesI, goal_cases)
        case (1 x)
        moreover obtain n where "\<alpha> = real n * \<epsilon>"
         using epsilon_multiplesD[OF epsilon_multiple_alpha, simplified, OF refl] by auto
       ultimately show ?case 
         by(auto intro: exI[of _ "(card (vset_set S) - card (vset_set NS)) * n"])
     qed
      show "epsilon_multiples \<epsilon> (potential pmap'') LR"
      proof(rule  epsilon_multiplesI, goal_cases)
        case (1 v)
        have "\<exists>xb. \<epsilon> * real x = \<epsilon> * real xa + \<epsilon> * real xb" 
          if "0 < \<epsilon> * real xa" "\<epsilon> * real xa \<le> \<epsilon> * real x" for x xa
          using that right_diff_distrib[of \<epsilon> "real x" "real xa"] 
          by(auto intro!: exI[of _ "x - xa"] 
                simp add: mult_less_cancel_left_disj zero_less_mult_iff)
        moreover have "\<exists>xb. \<epsilon> * real x + \<epsilon> * real xa = \<epsilon> * real xb" for x xa
          by(auto intro!: exI[of _ "x +xa"] simp add: distrib_left)
        ultimately show ?case 
          using alpha_gtr_0 alpha_less(2)[of v] 
            epsilon_multiplesD(1)[OF that(2) 1] x_both_in_S_and_NS_False[of v]
            epsilon_multiplesD[OF epsilon_multiple_alpha, simplified, OF refl]
          by(auto intro!: epsilon_multiplesI
              simp add: pmap''_effect algebra_simps vset.set_isin[OF S_NS_props(5)])
      qed
    qed
    ultimately show ?case
      by fast
  qed
qed

subsection \<open>Correctness\<close>

lemma naive_primal_dual_ret_cond_correctness:
  assumes "naive_primal_dual_ret_cond pmap" "p_invar pmap"
    "feasible_max_dual LR G w (abstract_real_map (p_lookup pmap))"
  shows "max_weight_matching G w (g_to_set (naive_primal_dual_ret pmap))"
    "min_feasible_max_dual LR G w (potential pmap)"
proof-
  define tights where "tights = build_tight_graph pmap"
  define bads where "bads = find_bads pmap"
  obtain M where M_def:"match M = find_matching_or_witness tights bads"
    using assms(1)
    by(auto elim!: naive_primal_dual_ret_condE 
        simp add: tights_def bads_def)
  have M_is_ret:"naive_primal_dual_ret pmap = M"
    using  M_def[symmetric]
    by(auto simp add: tights_def bads_def naive_primal_dual_ret_def Let_def)
  note tight_graph_props = build_tight_graph_props[of pmap, folded tights_def]
  note find_bad_props = find_bads_props[of pmap, folded bads_def]
  have tights_bipartite: "bipartite (g_to_set tights) L R"
    by(rule bipartite_subgraph)(auto simp add: tight_graph_props(2) basic_graph_props(4))
  have M_props: "graph_matching (g_to_set tights) (g_to_set M)" "vset_set bads \<subseteq> Vs (g_to_set M)" "g_invar M"
    using find_matching_or_witness(1)  tights_bipartite tight_graph_props(1) find_bad_props(1) M_def[symmetric]
    by auto
  have M_matching_G:  "graph_matching G (g_to_set M)"
    by(auto intro!: matching_graph_mono[OF M_props(1)] simp add: tight_graph_props(2))
  have tights_are_tights:"g_to_set tights = tight_subgraph G w (potential pmap)"
    using w_weight_cong
    by(force simp add: tight_graph_props(2) tight_subgraph_def edge_slack_def) 
  have M_in_tight: "g_to_set M \<subseteq> tight_subgraph G w (potential pmap)" 
    using M_props(1) tights_are_tights by auto
  have non_zeros_in_M: "non_zero_vertices LR (potential pmap) \<subseteq> Vs (g_to_set M)"
    using M_props(2)  feasible_max_dualD(1)[OF assms(3)]
    by(force simp add: find_bad_props non_zero_vertices_def)
  show "max_weight_matching G w (g_to_set (naive_primal_dual_ret pmap))"
    "min_feasible_max_dual LR G w (potential pmap)"
    using assms(3) M_matching_G graph_invar_G M_in_tight  non_zeros_in_M
    by(auto intro!: max_weight_if_tight_matching_covers_bads simp add: M_is_ret)
qed

lemma naive_primal_dual_partial_correctness_general:
  assumes "naive_primal_dual_dom pmap" "p_invar pmap"
    "feasible_max_dual LR G w (abstract_real_map (p_lookup pmap))"
  shows  "max_weight_matching G w (g_to_set (naive_primal_dual pmap))"
    "\<exists> pmap. min_feasible_max_dual LR G w (potential pmap)"
  using assms(2-)
proof(all \<open>induction rule: naive_primal_dual.pinduct[OF assms(1)]\<close>, goal_cases)
  case (1 pmap)
  note IH =this
  show ?case 
  proof(cases pmap rule: naive_primal_dual_cases)
    case 1
    show ?thesis 
      using naive_primal_dual_ret_cond_correctness(1)[OF 1 IH(3,4)]
        naive_primal_dual_simps(1)[OF 1]
      by simp
  next
    case 2
    show ?thesis 
    proof(rule naive_primal_dual_call_condE[OF 2], goal_cases)
      case (1 tights bads S NS)
      hence call_is: "naive_primal_dual_call pmap =
       vset_iterate_pmap NS (\<lambda>v. p_update v (potential pmap v + real_of_ereal (find_\<epsilon> pmap S)))
       (vset_iterate_pmap S (\<lambda>v. p_update v (potential pmap v - real_of_ereal (find_\<epsilon> pmap S))) pmap)"
        by(auto simp add: naive_primal_dual_call_def Let_def)
      from 1 show ?case 
        by(auto simp add: naive_primal_dual_simps(2)[OF 2 IH(1)] 2 IH(3,4)
            intro!: IH(2)[OF refl refl _ refl refl] call_is
            naive_primal_dual_one_step(1,2))
    qed
  qed
next
  case (2 pmap)
  note IH =this
  show ?case 
  proof(cases pmap rule: naive_primal_dual_cases)
    case 1
    show ?thesis 
      using naive_primal_dual_ret_cond_correctness[OF 1 IH(3,4)]
        naive_primal_dual_simps(1)[OF 1]
      by auto
  next
    case 2
    show ?thesis 
    proof(rule naive_primal_dual_call_condE[OF 2], goal_cases)
      case (1 tights bads S NS)
      hence call_is: "naive_primal_dual_call pmap =
       vset_iterate_pmap NS (\<lambda>v. p_update v (potential pmap v + real_of_ereal (find_\<epsilon> pmap S)))
       (vset_iterate_pmap S (\<lambda>v. p_update v (potential pmap v - real_of_ereal (find_\<epsilon> pmap S))) pmap)"
        by(auto simp add: naive_primal_dual_call_def Let_def)
      from 1 show ?case 
        by(auto simp add: naive_primal_dual_simps(2)[OF 2 IH(1)] 2 IH(3,4)
            intro!: IH(2)[OF refl refl _ refl refl] call_is
            naive_primal_dual_one_step(1,2))
    qed
  qed
qed 

lemma initial_feasible:
  "feasible_max_dual LR G w (abstract_real_map (p_lookup init_potential))" (is ?thesis1)
  and  initial_epsilon_multiples: "epsilon_multiples \<epsilon> w G \<Longrightarrow> epsilon_multiples \<epsilon> (potential init_potential) LR" (is "?asm \<Longrightarrow> ?thesis2")
proof-
  have finite_for_v: "finite {weight v u |u. {u, v} \<in> G}" for v
    apply(cases "v \<in> Vs G")
    subgoal
      apply(rule finite_subset[of _ "{weight v u |u v. {u, v} \<in> G}"])
      by(auto simp add: Vs_def  image_two_Collect finiteG
          intro!: finite_imageI finite_pairs_of_finite_set_set)
    subgoal
      by(auto simp add: Vs_def setcompr_eq_image intro!: finite_imageI
          finite_subset[of _ "{}"]) 
    done
  show ?thesis1
    unfolding init_potential_props(2)
  proof(rule feasible_max_dualI, goal_cases)
    case (1 v)
    then show ?case 
      by (auto intro!: linorder_class.Max.coboundedI finite_g_applied_double finite_for_v)
  next
    case (2 e u v)
    then show ?case 
      using sym_weights basic_graph_props(10)[of u] basic_graph_props(6)[of u v]  
      by(auto simp add: w_weight_cong insert_commute dest: basic_graph_props(8)
          intro!: linorder_class.Max.coboundedI finite_for_v 
          exI[of "\<lambda> ua. weight u v = weight u ua \<and> {ua, u} \<in> G" v]
          exI[of "\<lambda> ua. weight u v = weight v ua \<and> {ua, v} \<in> G" u])
  qed (auto simp add: basic_graph_props(1,13))
  show "?asm \<Longrightarrow> ?thesis2"
  proof(rule epsilon_multiplesI, goal_cases)
    case (1 v)
    have  "Max ({0} \<union> {weight v u |u. {u, v} \<in> G}) \<in> {0} \<union> {weight v u |u. {u, v} \<in> G}"
      by (rule Max_in)(auto simp add: finite_for_v)
    then obtain u where u_prop: "(potential init_potential v = weight v u \<and> {u, v} \<in> G)
                   \<or> potential init_potential v = 0"
      by(cases "v\<in> L")
        (auto simp add: init_potential_props(2))
    show ?case
      using epsilon_multiplesD[OF 1(1)]  u_prop  w_weight_cong[of v u, symmetric] 
      by (auto simp add: insert_commute)
  qed
qed

lemma naive_primal_dual_partial_correctness:
  assumes "naive_primal_dual_dom init_potential"
  shows  "max_weight_matching G w (g_to_set (naive_primal_dual init_potential))"
    "\<exists> pmap. min_feasible_max_dual LR G w (potential pmap)"
  by(auto intro!: naive_primal_dual_partial_correctness_general assms
      simp add: init_potential_props(1) initial_feasible)

subsection \<open>Termination and Total Correctness\<close>

lemma naive_primal_dual_termination_general:
  assumes   "epsilon_multiples \<epsilon> w G" "p_invar pmap" 
    "feasible_max_dual LR G w (abstract_real_map (p_lookup pmap))"  
    "epsilon_multiples \<epsilon> (potential pmap) LR"
  shows    "naive_primal_dual_dom pmap"
proof-
  obtain n where n_is:"sum (potential pmap) LR = (real n) * \<epsilon>"
    using epsilon_multiples_sum[OF _ assms(4), simplified epsilon_multiples_def, simplified]
      basic_graph_props(13) by blast
  show ?thesis
    using assms(2,3,4) n_is
  proof(induction n arbitrary: pmap rule: less_induct)
    case (less n)
    show ?case
    proof(cases pmap rule: naive_primal_dual_cases)
      case 1
      then show ?thesis 
        by(auto intro: naive_primal_dom_ret)
    next
      case 2
      obtain \<alpha> where alpha_props:"\<alpha> > 0"
        "sum (potential (naive_primal_dual_call pmap)) LR + \<alpha> = sum (potential pmap) LR"
        "epsilon_multiples \<epsilon> id {\<alpha>}"
        "epsilon_multiples \<epsilon> (potential (naive_primal_dual_call pmap)) LR"
        using naive_primal_dual_one_step(3)[OF 2 less(2,3)] assms(1)less(4) by auto
      obtain n1 where n1: "\<alpha> = real n1 * \<epsilon>" 
        using alpha_props(3) epsilon_multiplesD by fastforce
      obtain n2 where n2: "sum (potential pmap) LR = real n2 * \<epsilon>"
        using less(5) epsilon_multiplesD by fastforce
      obtain n3 where n3: "sum (potential (naive_primal_dual_call pmap)) LR = real n3 * \<epsilon>"
        using epsilon_multiples_sum[OF  basic_graph_props(13) alpha_props(4), simplified epsilon_multiples_def, simplified]
        by auto
      have eps_gtr_0: "\<epsilon> > 0" 
        using alpha_props(1) n1 of_nat_less_0_iff zero_less_mult_iff by blast
      have "\<lbrakk> 0 < \<epsilon> * real n1; \<epsilon> * real n1 + \<epsilon> * real n3 = \<epsilon> * real n2; 0 < \<epsilon>\<rbrakk>
             \<Longrightarrow> n3 < n2"
        using  mult_left_mono[of "real n2" "real n3" \<epsilon>] 
        by fastforce
      hence n3_less_n:"n3 < n"
        using n1 n2 n3 alpha_props(1,2) eps_gtr_0 less.prems(4) 
        by(auto simp add: algebra_simps)
      show ?thesis 
        by(auto intro!: naive_primal_dom_call[OF _ 2] less(1)[OF n3_less_n] 
            simp add: naive_primal_dual_one_step(1,2)[OF 2 less(2,3)] alpha_props(4) n3)
    qed
  qed
qed

lemma naive_primal_dual_total_correctness_general:
  assumes"p_invar pmap" "feasible_max_dual LR G w (abstract_real_map (p_lookup pmap))"
    "epsilon_multiples \<epsilon> (potential pmap) LR" "epsilon_multiples \<epsilon> w G" 
  shows  "max_weight_matching G w (g_to_set (naive_primal_dual pmap))"
    "\<exists> pmap. min_feasible_max_dual LR G w (potential pmap)"
  using  assms
  by(auto intro!: naive_primal_dual_partial_correctness_general 
      naive_primal_dual_termination_general)

lemma naive_primal_dual_termination:
  assumes  "epsilon_multiples \<epsilon> w G"
  shows    "naive_primal_dual_dom init_potential"
  using assms
  by(auto intro!: naive_primal_dual_termination_general 
      init_potential_props(1) initial_feasible initial_epsilon_multiples)

lemma naive_primal_dual_total_correctness:
  assumes "epsilon_multiples \<epsilon> w G"
  shows   "max_weight_matching G w (g_to_set (naive_primal_dual init_potential))"
    "\<exists> pmap. min_feasible_max_dual LR G w (potential pmap)"
  using assms naive_primal_dual_partial_correctness naive_primal_dual_termination
  by auto

subsection \<open>Termination for a Specific Case\<close>

context
  fixes \<epsilon>::real
  assumes eps_pos: "\<epsilon> \<ge> 0"
  assumes weights_scaled_rationals:"\<And> u v. {u, v} \<in> G \<Longrightarrow> \<exists> (r::rat). weight u v = (real_of_rat r) * \<epsilon>"
begin

lemma epsilon_multiples: 
  obtains \<epsilon>' where "epsilon_multiples \<epsilon>' w G"
proof(goal_cases)
  case 1
  note one = this
  then show ?case
  proof(cases "G = {}")
    case True
    then show ?thesis 
      by(auto intro!: epsilon_multiplesI one)
  next
    case False
    have main_denom: "\<exists> md::nat. md > 0 \<and> 
             (\<forall>  u v. {u, v} \<in> G  \<longrightarrow> (\<exists> i::int. weight u v = (i / (md::nat)) * \<epsilon>))"
    proof(cases "\<epsilon> = 0")
      case True
      then show ?thesis 
        using weights_scaled_rationals
        by(auto intro!: exI[of _ "Suc 0"])
    next
      case False
      hence "real_of_rat `  { r | u v (r::rat). real_of_rat r = weight u v / \<epsilon> \<and> {u, v} \<in> G} 
                   = {weight u v / \<epsilon> | u v. {u, v} \<in> G}"
        using  weights_scaled_rationals
        by (force simp add: algebra_simps intro!: imageI)
      have finitess: "finite {uu. \<exists>u v r. uu = r \<and> real_of_rat r = weight u v / \<epsilon> \<and> {u, v} \<in> G}"
      proof(rule finite_subset[of _ "{r. \<exists>e . real_of_rat r = w e / \<epsilon> \<and> e \<in> G}"], goal_cases)
        case 1
        thus ?case
          using w_weight_cong by force
      next
        case 2
        show ?case 
        proof(subst bij_betw_finite[of real_of_rat "{r. \<exists>e. real_of_rat r = w e / \<epsilon> \<and> e \<in> G}"
                "{r. \<exists>e.  r = w e / \<epsilon> \<and> e \<in> G}"], goal_cases)
          case 1
          have "\<exists>x. (\<exists>e. real_of_rat x = w e / \<epsilon> \<and> e \<in> G) \<and> w e / \<epsilon> = real_of_rat x" if "e \<in> G" for e
          proof-
            note That = that
            obtain u v where uv: "e = {u, v}" "u \<noteq> v" "u \<in> L" "v \<in> R"
              using bipartite_edgeE[OF That basic_graph_props(4)] by blast
            moreover then obtain r where "weight u v = real_of_rat r * \<epsilon>"
              using That weights_scaled_rationals by auto
            ultimately show ?thesis
              using False That
              by(auto intro!: exI[of _ r] exI[of _ e] simp add: w_weight_cong)
          qed
        then show ?case
          by(auto simp add: bij_betw_def image_def 
                    intro!: inj_onI iffD1[OF of_rat_eq_iff])
        qed (simp add: finiteG)
      qed
      obtain d where d:
        "d>0" "\<And> x. x\<in>{uu. \<exists>u v r. uu = r \<and> real_of_rat r = weight u v / \<epsilon> \<and> {u, v} \<in> G} \<Longrightarrow>
         \<exists>i. real_of_rat x = real_of_int i / real d"
        using common_denominator[of "{ r | u v (r::rat). real_of_rat r = weight u v / \<epsilon> \<and> {u, v} \<in> G}"]
          finitess by auto
      show ?thesis 
      proof(rule exI[of _ d], rule, rule d(1), rule, rule, rule, goal_cases)
        case (1 u v)
        obtain r where r:"weight u v = real_of_rat r * \<epsilon>"
          using weights_scaled_rationals[OF 1] by auto
        obtain i where i:"real_of_rat r = real_of_int i / real d"
          apply(rule exE[OF d(2)[of r]])
          using r 1 False
          by (auto intro!: exI[of "\<lambda> u. \<exists> v. real_of_rat r = weight u v / \<epsilon> \<and> {u, v} \<in> G" u]
              exI[of "\<lambda> v. real_of_rat r = weight u v / \<epsilon> \<and> {u, v} \<in> G" v])
        show ?case 
          using r  i
          by(auto simp add: algebra_simps )  
      qed
    qed
    then obtain md where  main_denom: " md > 0"
      "(\<And> u v.  {u, v} \<in> G  \<Longrightarrow> (\<exists> i::int. weight u v = (i / (md::nat)) * \<epsilon>))"
      by auto
    have "epsilon_multiples (\<epsilon> / real md) w G"
    proof(rule epsilon_multiplesI, goal_cases)
      case (1 e)
      then obtain u v  where e_split:"e = {u, v}"
        using graph_invar_G by blast
      hence w_is_weight: "w {u, v} = weight u v"
        using "1" w_weight_cong by auto
      obtain r where r: "weight u v = (real_of_rat r) * \<epsilon>"
        using "1" e_split weights_scaled_rationals by blast
      obtain i::int where i:"weight u v = (i / (md::nat)) * \<epsilon>"
        using e_split(1) 1 main_denom(2) by blast
      show ?case
      proof(cases "\<epsilon> = 0")
        case True
        then show ?thesis 
          using main_denom(1) 
          by(auto simp add: algebra_simps e_split r w_is_weight)
      next
        case False
        note false = this
        show ?thesis
        proof(cases "\<epsilon> \<ge> 0")
          case True
          moreover have "i \<ge> 0" 
            using i False True pos_weights[of u v] 1 e_split main_denom(1)
            by (auto simp add: algebra_simps zero_le_divide_iff zero_le_mult_iff)
          ultimately show ?thesis
            by(auto intro!: exI[of _ "nat i"] 
                simp add:  w_weight_cong[OF 1[simplified e_split]] e_split i)
        next
          case False
          thus ?thesis
            using eps_pos by auto
        qed
      qed
    qed
    thus "(\<And>\<epsilon>'. epsilon_multiples \<epsilon>' w G \<Longrightarrow> thesis) \<Longrightarrow> G \<noteq> {} \<Longrightarrow> thesis"
      by simp
  qed
qed

lemma naive_primal_dual_termination_rationals:
  "naive_primal_dual_dom init_potential"
  using epsilon_multiples naive_primal_dual_termination by auto

lemma naive_primal_dual_total_correctness_rationals:
  "max_weight_matching G w (g_to_set (naive_primal_dual init_potential))"
  "\<exists> pmap. min_feasible_max_dual LR G w (potential pmap)"
  by (simp add: naive_primal_dual_partial_correctness
      naive_primal_dual_termination_rationals)+
end
end
end