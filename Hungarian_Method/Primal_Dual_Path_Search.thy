theory Primal_Dual_Path_Search
  imports Berge_Lemma.Berge Flow_Theory.Arith_Lemmas "HOL-Data_Structures.Set_Specs"
"HOL-Data_Structures.Map_Specs"
begin

record ('forest, 'seen, 'slack, 'potential,'gimpl) primal_dual_state = 
new_to_left_seen::'seen
forest::'forest
seen::'seen
slack::'slack
potential::'potential
tight_graph::'gimpl

datatype ('v, 'seen, 'forest) path_or_forest = Path "'v list"
  | Forest 'seen 'forest

locale primal_dual_path_search_spec = 
  fixes G::"'v set set"
    and buddy::"'v \<Rightarrow> 'v option"
    and get_path_or_extend_forest:: 
       "'gimpl \<Rightarrow> 'vset \<Rightarrow> 'vset \<Rightarrow>'forest \<Rightarrow> ('v \<Rightarrow> 'v option)
          \<Rightarrow> ('v, 'vset, 'forest) path_or_forest"
   and vset_empty::'vset
   and vset_insert::"'v \<Rightarrow> 'vset \<Rightarrow>'vset"
   and vset_invar::"'vset \<Rightarrow> bool"
   and vset_set::"'vset \<Rightarrow> 'v set"
   and vset_diff::"'vset \<Rightarrow> 'vset \<Rightarrow> 'vset"
   and vset_inter::"'vset \<Rightarrow> 'vset \<Rightarrow> 'vset"
   and g_neighb::"'gimpl \<Rightarrow> 'v \<Rightarrow> 'vset option"
   and g_add_edge::"'gimpl \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'gimpl"
   and g_empty::"'gimpl"
   and forest_abstract::"'forest \<Rightarrow> 'v set set"
   and forest_invar::"'forest \<Rightarrow> bool"
   and empty_forest::"'forest"
   and slack_empty::'slack
   and slack_lookup::"'slack \<Rightarrow> 'v \<Rightarrow> (real \<times> 'vset ) option"
   and slack_upd::"'v \<Rightarrow> (real \<times> 'vset) \<Rightarrow> 'slack \<Rightarrow> 'slack"
   and slack_invar::"'slack \<Rightarrow> bool"
   and potential_upd::"'potential \<Rightarrow> 'v \<Rightarrow> real \<Rightarrow> 'potential"
   and potential_lookup::"'potential \<Rightarrow> 'v \<Rightarrow> real option"
   and potential_invar::"'potential \<Rightarrow> bool"
   and initial_pot::"'potential"
   and edge_costs::"'v \<Rightarrow> 'v \<Rightarrow> real"
   and left::'vset
   and right::'vset
   and right_neighbs::"'v \<Rightarrow> 'vset option"
   (*and iterate_vset_slack::"('v \<Rightarrow> 'slack \<Rightarrow> 'slack) \<Rightarrow> 'vset \<Rightarrow> 'slack \<Rightarrow> 'slack"*)
   and vset_flatten::"'vset \<Rightarrow> 'v list"

begin

definition "right_neighb_abstract v = (case right_neighbs v of None \<Rightarrow> {}
                                       | Some vs \<Rightarrow> vset_set vs)"

lemma reight_neighb_abstract_applied:
 "right_neighbs v = None \<Longrightarrow> right_neighb_abstract v = {}"
 "right_neighbs v =  Some vs \<Longrightarrow> right_neighb_abstract v = vset_set vs"
  by(auto simp add: right_neighb_abstract_def)

definition "edge_slack pot x y = 
    edge_costs x y 
     - abstract_real_map (potential_lookup pot) x
     - abstract_real_map (potential_lookup pot) y"

definition "add_to_pot pot x val = 
           (case potential_lookup pot x of 
             None \<Rightarrow> potential_upd pot x val 
             | Some val' \<Rightarrow> potential_upd pot x (val + val'))"

(*
definition "initial_slack pot = 
   iterate_vset_slack
    (\<lambda> u slacks. case right_neighbs u of None => slacks
               |  Some vs \<Rightarrow> 
      iterate_vset_slack
        (\<lambda> v slacks. case slack_lookup slacks v of 
             None \<Rightarrow> slack_upd slacks v
            (edge_slack pot u v) (vset_insert u vset_empty)
             | Some (svalue, tights) \<Rightarrow>
              (let uvsvalue = edge_slack pot u v in
               (if uvsvalue < svalue then
                  slack_upd slacks v
                  (edge_slack pot u v) (vset_insert u vset_empty)
                else if uvsvalue =  svalue then
                  slack_upd slacks v svalue
                   (vset_insert u tights)
                else slacks)))
                vs slacks)
             left slack_empty"
*)
term arg_max
definition "new_slacks slacks pot new_left = 
   foldr
    (\<lambda> u slacks. case right_neighbs u of None => slacks
               |  Some vs \<Rightarrow> 
      foldr
        (\<lambda> v slacks. case slack_lookup slacks v of 
             None \<Rightarrow> slack_upd  v
            ((edge_slack pot u v), (vset_insert u vset_empty)) slacks
             | Some (svalue, tights) \<Rightarrow>
              (let uvsvalue = edge_slack pot u v in
               (if uvsvalue < svalue then
                  slack_upd v (uvsvalue, (vset_insert u vset_empty))  slacks 
                else if uvsvalue =  svalue then
                  slack_upd  v (svalue, (vset_insert u tights)) slacks
                else slacks)))
                (vset_flatten vs) slacks)
             (vset_flatten new_left) slacks"

definition "abstract_min_slack slck = 
            (\<lambda> v. (case slack_lookup slck v of 
                   None \<Rightarrow> PInfty
                   | Some (sl, vs) \<Rightarrow> sl))"

definition "abstract_min_slack_edges slck = 
            (\<lambda> u. (case slack_lookup slck u of 
                   None \<Rightarrow> {}
                   | Some (sl, vs) \<Rightarrow> {(u, v) | v. v \<in> vset_set vs}))"

definition "new_tights slacks rights= 
            (foldr
            (\<lambda> u (sl, edges). 
                (case slack_lookup slacks u of None \<Rightarrow> (sl, edges)
                | Some (sla, vs) \<Rightarrow>
                  if sla > sl then (sl, edges)
                  else if sla = sl then 
                  (sl, foldr (\<lambda> v edges. (u, v)#edges) (vset_flatten vs) edges)
                  else (sla, foldr (\<lambda> v edges. (u, v)#edges) (vset_flatten vs) [])
            )                  
            ) (vset_flatten rights) (PInfty, []))"

definition "initial_state = 
\<lparr>new_to_left_seen= left,
forest=empty_forest,
seen = left,
slack = slack_empty,
potential = initial_pot,
tight_graph = g_empty\<rparr>"


function (domintros) primal_dual_path_search::
"('forest, 'vset, 'slack, 'potential, 'gimpl) primal_dual_state \<Rightarrow>
('v list \<times> 'potential) option" where
"primal_dual_path_search state =
(let F = forest state; Z = seen state; newZleft = new_to_left_seen state;
     pot = potential state; slacks = slack state;
     new_slack = new_slacks slacks pot newZleft;
     Gt = tight_graph state;
     (\<epsilon>, new_tight_edges) = new_tights new_slack (vset_diff right Z)
in ( if \<epsilon> = PInfty then None
     else (let new_pot1 = foldr (\<lambda> v p. add_to_pot p v (real_of_ereal \<epsilon>)) 
                                 (vset_flatten (vset_inter Z left)) pot;
                 new_pot2 = foldr (\<lambda> v p. add_to_pot p v (- real_of_ereal \<epsilon>)) 
                                 (vset_flatten (vset_inter Z right)) new_pot1;
                 Gt' = foldr (\<lambda> e G. g_add_edge G (fst e) (snd e))
                     new_tight_edges Gt;
               newF = get_path_or_extend_forest Gt' Z newZleft F buddy
           in (case newF of 
                    Path P \<Rightarrow> Some (P, new_pot2)
                  | Forest newZ F' => 
                      let newZleft' = vset_inter (vset_diff newZ Z) left;
                          state' = state \<lparr>new_to_left_seen := newZleft', forest := F', seen := newZ,
                                          slack := new_slack, potential := new_pot2, tight_graph :=Gt' \<rparr>
                       in primal_dual_path_search state'))))"
  by pat_completeness auto


end

locale primal_dual_path_search_reasoning = primal_dual_path_search_spec +
vset_set_specs: Set2 vset_empty vset_delete vset_isin vset_set vset_invar vset_insert
vset_union vset_inter vset_diff +
slack_map: Map slack_empty slack_upd slack_del slack_lookup slack_invar
for vset_delete vset_isin vset_union slack_del
+
assumes vset_flatten: "vset_invar vs \<Longrightarrow> set (vset_flatten vs) = vset_set vs"
                      "vset_invar vs \<Longrightarrow> distinct (vset_flatten vs)"
and    reight_neighbs: "\<And> vs. right_neighbs v = Some vs \<Longrightarrow> vset_invar vs"
begin

lemma abstract_min_slack_upd:
"slack_invar slacks \<Longrightarrow>
   abstract_min_slack (slack_upd v (val, vs) slacks) = 
    (\<lambda> u. if u = v then val else abstract_min_slack slacks u)"
  by(auto intro!: ext 
        simp add: abstract_min_slack_def  slack_map.map_update 
           split: option.split)

lemma abstract_min_slack_edges_upd:
"slack_invar slacks \<Longrightarrow>
   abstract_min_slack_edges (slack_upd v (val, vs) slacks) = 
    (\<lambda> v'. if v' = v then {(v, u) | u. u \<in> vset_set vs} else abstract_min_slack_edges slacks v')"
  apply(auto intro!: ext 
        simp add: abstract_min_slack_edges_def slack_map.map_update  
       simp only: abstract_min_slack_edges_def
           split: option.split if_split)
       apply (simp add: slack_map.map_update)+
   apply (metis (lifting) emptyE option.distinct(1) option.simps(4))
  by (smt (verit, ccfv_threshold) case_prod_conv map_upd_Some_unfold mem_Collect_eq option.simps(5)
      slack_map.map_update)


definition "good_slacks sf A B slcks = 
    ((\<forall> v \<in> B. (abstract_min_slack slcks v = 
          Inf {ereal (sf u v) | u. v \<in> right_neighb_abstract u \<and> u \<in> A}) \<and>
          (abstract_min_slack_edges slcks v = 
          {(v, u) | u. is_arg_min (\<lambda> u. sf u v) (\<lambda> u. v \<in> right_neighb_abstract u \<and> u \<in> A) u}))
     \<and> finite A \<and> finite B)"


lemma good_slacksI:
"(\<And> v. v \<in> B \<Longrightarrow> (abstract_min_slack slcks v = 
          Inf {ereal (sf u v) | u. v \<in> right_neighb_abstract u \<and> u \<in> A})) \<Longrightarrow>
 (\<And> v. v \<in> B \<Longrightarrow>
          (abstract_min_slack_edges slcks v = 
          {(v, u) | u. is_arg_min (\<lambda> u. sf u v) (\<lambda> u. v \<in> right_neighb_abstract u \<and> u \<in> A) u})) 
\<Longrightarrow> finite A \<Longrightarrow> finite B 
\<Longrightarrow> good_slacks sf A B slcks"
and good_slacksI':
"(\<And> v. v \<in> B \<Longrightarrow> (abstract_min_slack slcks v = 
          Inf {ereal (sf u v) | u. v \<in> right_neighb_abstract u \<and> u \<in> A}) \<and>
           (abstract_min_slack_edges slcks v = 
          {(v, u) | u. is_arg_min (\<lambda> u. sf u v) (\<lambda> u. v \<in> right_neighb_abstract u \<and> u \<in> A) u}))
 \<Longrightarrow>finite A \<Longrightarrow> finite B  
\<Longrightarrow> good_slacks sf A B slcks"
and good_slacksE:
"good_slacks sf A B slcks \<Longrightarrow>
 ((\<And> v. v \<in> B \<Longrightarrow> (abstract_min_slack slcks v = 
          Inf {ereal (sf u v) | u. v \<in> right_neighb_abstract u \<and> u \<in> A})) \<Longrightarrow>
 (\<And> v. v \<in> B \<Longrightarrow>
          (abstract_min_slack_edges slcks v = 
          {(v, u) | u. is_arg_min (\<lambda> u. sf u v) (\<lambda> u. v \<in> right_neighb_abstract u \<and> u \<in> A) u})) 
\<Longrightarrow>finite A \<Longrightarrow> finite B \<Longrightarrow> P) \<Longrightarrow> P"
and good_slacksD:
"good_slacks sf A B slcks \<Longrightarrow>
  v \<in> B \<Longrightarrow> abstract_min_slack slcks v = 
          Inf {ereal (sf u v) | u. v \<in> right_neighb_abstract u \<and> u \<in> A}"
"good_slacks sf A B slcks \<Longrightarrow>
  v \<in> B \<Longrightarrow> abstract_min_slack_edges slcks v = 
          {(v, u) | u. is_arg_min (\<lambda> u. sf u v) (\<lambda> u. v \<in> right_neighb_abstract u \<and> u \<in> A) u}"
"good_slacks sf A B slcks \<Longrightarrow> finite A" "good_slacks sf A B slcks \<Longrightarrow> finite B"
  by(auto simp add: good_slacks_def)

definition "good_slacks_general sf A B E slcks = 
    ((\<forall> v \<in> B. (abstract_min_slack slcks v = 
          Inf {ereal (sf u v) | u. (u, v) \<in> E \<and> u \<in> A}) \<and>
          (abstract_min_slack_edges slcks v = 
          {(v, u) | u. is_arg_min (\<lambda> u. sf u v) (\<lambda> u. (u, v) \<in> E \<and> u \<in> A) u}))
     \<and> finite A \<and> finite B \<and> fst ` E \<subseteq> A)"

lemma good_slacks_generalI:
"(\<And> v. v \<in> B \<Longrightarrow> (abstract_min_slack slcks v = 
          Inf {ereal (sf u v) | u. (u, v) \<in> E \<and> u \<in> A})) \<Longrightarrow>
 (\<And> v. v \<in> B \<Longrightarrow>
          (abstract_min_slack_edges slcks v = 
          {(v, u) | u. is_arg_min (\<lambda> u. sf u v) (\<lambda> u. (u, v) \<in> E \<and> u \<in> A) u})) 
\<Longrightarrow> finite A \<Longrightarrow> finite B  \<Longrightarrow> fst ` E \<subseteq> A
\<Longrightarrow> good_slacks_general sf A B E slcks"
and good_slacks_generalI':
"(\<And> v. v \<in> B \<Longrightarrow> (abstract_min_slack slcks v = 
          Inf {ereal (sf u v) | u. (u, v) \<in> E \<and> u \<in> A}) \<and>
           (abstract_min_slack_edges slcks v = 
          {(v, u) | u. is_arg_min (\<lambda> u. sf u v) (\<lambda> u. (u, v) \<in> E \<and> u \<in> A) u}))
 \<Longrightarrow>finite A \<Longrightarrow> finite B  \<Longrightarrow> fst ` E \<subseteq> A
\<Longrightarrow> good_slacks_general sf A B E slcks"
and good_slacks_generalE:
"good_slacks_general sf A B E slcks \<Longrightarrow>
 ((\<And> v. v \<in> B \<Longrightarrow> (abstract_min_slack slcks v = 
          Inf {ereal (sf u v) | u. (u, v) \<in> E \<and> u \<in> A})) \<Longrightarrow>
 (\<And> v. v \<in> B \<Longrightarrow>
          (abstract_min_slack_edges slcks v = 
          {(v, u) | u. is_arg_min (\<lambda> u. sf u v) (\<lambda> u. (u, v) \<in> E \<and> u \<in> A) u})) 
\<Longrightarrow>finite A \<Longrightarrow> finite B \<Longrightarrow> fst ` E \<subseteq> A\<Longrightarrow> P) \<Longrightarrow> P"
and good_slacks_generalD:
"good_slacks_general sf A B E slcks \<Longrightarrow>
  v \<in> B \<Longrightarrow> abstract_min_slack slcks v = 
          Inf {ereal (sf u v) | u. (u, v) \<in> E \<and> u \<in> A}"
"good_slacks_general sf A B E slcks \<Longrightarrow>
  v \<in> B \<Longrightarrow> abstract_min_slack_edges slcks v = 
          {(v, u) | u. is_arg_min (\<lambda> u. sf u v) (\<lambda> u. (u, v) \<in> E \<and> u \<in> A) u}"
"good_slacks_general sf A B E slcks \<Longrightarrow> finite A"
 "good_slacks_general sf A B E slcks \<Longrightarrow> finite B"
"good_slacks_general sf A B E slacks \<Longrightarrow> fst ` E \<subseteq> A"
  by(auto simp add: good_slacks_general_def)

lemma good_slacks_general_extended_lonely_left:
"good_slacks_general sf A B E slcks \<Longrightarrow> \<nexists> b. (a, b) \<in> E \<Longrightarrow>
good_slacks_general sf (insert a A) B E slcks"
  by(auto intro!: good_slacks_generalI arg_cong[of _ _  Inf]
                  arg_cong[of _ _  "\<lambda> x. is_arg_min _ x _"]
         elim!: good_slacks_generalE
      simp add: is_arg_min_def)

lemma good_slacks_good_slacks_general: 
"good_slacks sf A B slcks \<Longrightarrow> 
  good_slacks_general sf A B {(u, v) | u v. v \<in> right_neighb_abstract u \<and> u \<in> A} slcks"
"good_slacks_general sf A B {(u, v) | u v. v \<in> right_neighb_abstract u \<and> u \<in> A} slcks
 \<Longrightarrow> good_slacks sf A B slcks"
"good_slacks sf A B slcks \<longleftrightarrow>
    good_slacks_general sf A B {(u, v) | u v. v \<in> right_neighb_abstract u \<and> u \<in> A} slcks"
  by(auto intro!: good_slacks_generalI  good_slacksI
           elim!: good_slacksE good_slacks_generalE)


(*TODO MOVE*)
lemma P_of_min_E: "P (min (a::real) b) \<Longrightarrow>(a \<le> b \<Longrightarrow> P a \<Longrightarrow> Q) \<Longrightarrow> (a \<ge> b \<Longrightarrow> P b \<Longrightarrow> Q) \<Longrightarrow> Q"
  by(cases "a \<le> b") auto

definition "slack_basic_invar slacks = (slack_invar slacks \<and> 
                 (\<forall> v sl vs. slack_lookup slacks v = Some (sl, vs) \<longrightarrow> vset_invar vs))"

lemma slack_basic_invarE:
"slack_basic_invar slacks \<Longrightarrow>
(slack_invar slacks \<Longrightarrow>
 (\<And> v sl vs. slack_lookup slacks v = Some (sl, vs) \<Longrightarrow> vset_invar vs) \<Longrightarrow> P) \<Longrightarrow> P "
and slack_basic_invarI: "slack_invar slacks \<Longrightarrow>
 (\<And> v sl vs. slack_lookup slacks v = Some (sl, vs) \<Longrightarrow> vset_invar vs) 
\<Longrightarrow>  slack_basic_invar slacks"
and slack_basic_invarD:
"slack_basic_invar slacks \<Longrightarrow> slack_invar slacks"
"slack_basic_invar slacks \<Longrightarrow>  slack_lookup slacks v = Some (sl, vs) \<Longrightarrow> vset_invar vs"
  by(auto simp add: slack_basic_invar_def)

(*TODO MOVE*)
lemma P_of_minI:"((a::('z::linorder)) \<le> b \<Longrightarrow> P a) \<Longrightarrow> (b \<le> a \<Longrightarrow> P b) \<Longrightarrow> P (min a b)"
  by(cases "a \<le> b") auto

lemma new_slack_good_slacks_pres:
  assumes "slack_basic_invar slacks" "vset_invar new_left"
      and "good_slacks (\<lambda> u v. edge_slack pot u v) A B slacks"
          "A \<inter> vset_set new_left = {}"
  shows   "good_slacks (\<lambda> u v. edge_slack pot u v) (A \<union> vset_set new_left)
           B (new_slacks slacks pot new_left)"
          "slack_basic_invar (new_slacks slacks pot new_left)"
          "dom (slack_lookup (new_slacks slacks pot new_left)) = 
           dom (slack_lookup slacks) \<union> \<Union> (right_neighb_abstract ` vset_set new_left)"
proof-
  note new_left_flattened = vset_flatten[OF assms(2)]
  define flat_new_left where "flat_new_left = vset_flatten new_left"
  define inner where "inner  = (\<lambda>u v slacks.
                    case slack_lookup slacks v of
                    None \<Rightarrow> slack_upd v ((edge_slack pot u v), (vset_insert u vset_empty)) slacks
                    | Some (svalue, tights) \<Rightarrow>
                        let uvsvalue = edge_slack pot u v
                        in if uvsvalue < svalue
                           then slack_upd v (uvsvalue, (vset_insert u vset_empty)) slacks
                           else if uvsvalue = svalue
                                then slack_upd v (svalue, (vset_insert u tights)) slacks
                            else slacks)"
  define outer where "outer = (\<lambda>u slacks.
                case right_neighbs u of None \<Rightarrow> slacks
                | Some vs \<Rightarrow> foldr (inner u) (vset_flatten vs) slacks)"
  have effect_inner:"good_slacks_general (edge_slack pot) (insert u A) B (insert (u, v) E)
     (inner u v slacks) \<and>
      slack_basic_invar (inner u v slacks) \<and>
      dom (slack_lookup (inner u v slacks)) =
      insert v (dom (slack_lookup slacks))" 
    if "slack_basic_invar slacks"  "good_slacks_general (edge_slack pot) A B E slacks"
     for u v A B E slacks
    proof(rule conjI[OF _ conjI], goal_cases)
      case 1
      note one = this
      then show ?case 
      proof(rule  good_slacks_generalI', goal_cases)
        case (1 va)
        note one' = this
        show ?case
        proof(cases "va = v")
          case True
          show ?thesis 
        proof(cases "slack_lookup slacks v")
          case None
          have helper1: "(\<And> u. (u, v) \<in> E \<Longrightarrow> u \<notin> A) \<Longrightarrow>
                  ereal (edge_slack pot u v) =
                  min (ereal (edge_slack pot u v))
                   (min (Inf {uu. uu = ereal (edge_slack pot u v) \<and> (u, v) \<in> E})
                   (Inf {ereal (edge_slack pot ua v) |ua. (ua = u \<or> (ua, v) \<in> E) \<and> ua \<in> A}))" 
          apply(rule P_of_minI)
          apply simp
          apply(rule P_of_minI)
          by (auto simp add: Inf_less_iff less_eq_ereal_def)
        show ?thesis 
          using good_slacks_generalD(1,2)[OF that(2) one', symmetric] one' True
          by(auto simp add: inner_def None  (*set_is_on_v*) abstract_min_slack_def
                  abstract_min_slack_edges_def is_arg_min_def   vset_set_specs.set_empty
                  abstract_min_slack_upd[OF slack_basic_invarD(1)[OF that(1)]] True
                  abstract_min_slack_edges_upd[OF slack_basic_invarD(1)[OF that(1)]]
                  vset_set_specs.set_insert[OF vset_set_specs.invar_empty] 
                              slack_map.map_update[OF slack_basic_invarD(1)[OF that(1)]]
                  Inf_eq_PInfty conj_disj_distribL ex_disj_distrib Collect_disj_eq 
                  complete_lattice_class.Inf_union_distrib 
                  intro!: helper1)
      next
        case (Some vs)
        then show ?thesis 
        proof(cases vs, goal_cases)
          case (1 sl vs) (*TODO generalise and move*)
          have inf_ereal_find_inf:"Inf {ereal (edge_slack pot u v) |u. v \<in> right_neighb_abstract u \<and> u \<in> A} = ereal sl
                \<Longrightarrow> \<exists> u. v \<in> right_neighb_abstract u \<and> u \<in> A \<and> sl = (edge_slack pot u v)"
          proof(cases "\<exists> u. v \<in> right_neighb_abstract u \<and> u \<in> A", goal_cases)
            case 1
            have " ereal sl \<in> {ereal (edge_slack pot u v) |u. v \<in> right_neighb_abstract u \<and> u \<in> A}"
              unfolding 1(1)[symmetric]
              apply(subst complete_linorder_class.Min_Inf[symmetric])
              using good_slacks_generalD(3)[OF that(2)] 1(2) 
              by(intro linorder_class.Min_in | simp)+
            thus ?case by auto
          next
            case 2
            hence emp:"{ereal (edge_slack pot u v) |u. v \<in> right_neighb_abstract u \<and> u \<in> A} =  {}" by auto
            show ?case
              using 2(1)[simplified emp] 
              by(simp add: complete_lattice_class.Inf_empty top_ereal_def)
          qed
          have help1: 
        "\<lbrakk>Inf {ereal (edge_slack pot u v) |u. v \<in> right_neighb_abstract u \<and> u \<in> A} =
          ereal (edge_slack pot ua v); v \<in> right_neighb_abstract y;
            edge_slack pot y v < edge_slack pot ua v; y \<in> A \<rbrakk> \<Longrightarrow> False" 
        and help3: 
         " \<lbrakk>Inf {ereal (edge_slack pot u v) |u. v \<in> right_neighb_abstract u \<and> u \<in> A} =
            ereal (edge_slack pot ua v); edge_slack pot u v < edge_slack pot ua v;
            v \<in> right_neighb_abstract y; edge_slack pot y v < edge_slack pot u v;
             y \<in> A ; v \<in> right_neighb_abstract u\<rbrakk> \<Longrightarrow> False"
        for ua y
            by (smt (verit, del_insts) Inf_less_iff less_ereal.simps(1) mem_Collect_eq)+
          have help2:
          "\<lbrakk> {(v, va) |va. va \<in> vset_set vs} =
           {(v, u) |u. v \<in> right_neighb_abstract u \<and> u \<in> A \<and>
           (\<forall>y. y \<in> A \<longrightarrow> v \<in> right_neighb_abstract y \<longrightarrow> \<not> edge_slack pot y v < edge_slack pot u v)};
            v \<in> right_neighb_abstract uaa ;  \<forall>y. v \<in> right_neighb_abstract y \<longrightarrow>
           y \<noteq> u \<and> y \<notin> A \<or> \<not> edge_slack pot y v < edge_slack pot uaa v ; uaa \<in> A ; uaa \<notin> vset_set vs\<rbrakk>
             \<Longrightarrow> uaa = u" for ua uaa
            by (smt (verit) mem_Collect_eq prod.inject) 
          have help4:
            "\<lbrakk>Inf {ereal (edge_slack pot u v) |u. v \<in> right_neighb_abstract u \<and> u \<in> A} =
               ereal (edge_slack pot ua v); edge_slack pot u v < edge_slack pot ua v;
               v \<in> right_neighb_abstract uaa ; \<forall>y. v \<in> right_neighb_abstract y \<longrightarrow>
               y \<noteq> u \<and> y \<notin> A \<or> \<not> edge_slack pot y v < edge_slack pot uaa v;
              uaa \<in> A; v \<in> right_neighb_abstract u \<rbrakk> \<Longrightarrow> uaa = u" for ua uaa
            by (smt (verit, ccfv_SIG) Inf_less_iff less_ereal.simps(1) mem_Collect_eq)
          have help1: 
        "Inf {ereal (edge_slack pot u v) |u. (u, v) \<in> E \<and> u \<in> A} = ereal (edge_slack pot u v) \<Longrightarrow>
          ereal (edge_slack pot u v) =
          Inf {ereal (edge_slack pot ua v) |ua. (ua = u \<or> (ua, v) \<in> E) \<and> (ua = u \<or> ua \<in> A)}" 
            by (smt (verit, del_insts) Inf_less_iff linorder_cases mem_Collect_eq order_less_irrefl)
          have help2: 
           " Inf {ereal (edge_slack pot u v) |u. (u, v) \<in> E \<and> u \<in> A} = ereal (edge_slack pot u v) \<Longrightarrow>
              edge_slack pot y v < edge_slack pot u v \<Longrightarrow> (y, v) \<in> E \<Longrightarrow> y \<in> A \<Longrightarrow> False" for y
            by (smt (verit, ccfv_threshold) Inf_less_iff less_ereal.simps(1) mem_Collect_eq)
          have help3: 
            "{(v, va) |va. va \<in> vset_set vs} =
              {(v, u) |u.
              (u, v) \<in> E \<and>
              u \<in> A \<and> (\<forall>y. y \<in> A \<longrightarrow> (y, v) \<in> E \<longrightarrow> \<not> edge_slack pot y v < edge_slack pot u v)} \<Longrightarrow>
              va \<in> vset_set vs \<Longrightarrow> (va, v) \<notin> E \<Longrightarrow> va = u" for va
            by blast
          have help4:
            " {(v, va) |va. va \<in> vset_set vs} =
             {(v, u) |u.
           (u, v) \<in> E \<and>
             u \<in> A \<and> (\<forall>y. y \<in> A \<longrightarrow> (y, v) \<in> E \<longrightarrow> \<not> edge_slack pot y v < edge_slack pot u v)} \<Longrightarrow>  
             va \<in> vset_set vs \<Longrightarrow> va \<notin> A \<Longrightarrow> va = u" for va
            by blast
          have help5: False
            if a1: "Inf {ereal (edge_slack pot u v) |u. (u, v) \<in> E \<and> u \<in> A} = ereal (edge_slack pot u v)"
        and a2: "{(v, va) |va. va \<in> vset_set vs} = {(v, u) |u. (u, v) \<in> E \<and> u \<in> A \<and> (\<forall>y. y \<in> A \<longrightarrow> (y, v) \<in> E \<longrightarrow> \<not> edge_slack pot y v < edge_slack pot u v)}"
        and a3: "sl = edge_slack pot u v"
        and a4: "vaa \<in> vset_set vs"
        and  a5: "edge_slack pot u v < edge_slack pot vaa v" for vaa
       proof -
        have "\<forall>e E. (Inf E < (e::ereal) \<or> (\<forall>ea. \<not> ea < e \<or> ea \<notin> E)) \<and> ((\<exists>ea<e. ea \<in> E) \<or> \<not> Inf E < e)"
          by (metis (no_types) Inf_less_iff)
        then obtain ee :: "ereal \<Rightarrow> ereal set \<Rightarrow> ereal" and eea :: "ereal \<Rightarrow> ereal set \<Rightarrow> ereal" where
          f6: "\<forall>e E. (Inf E < e \<or> (\<forall>ea. \<not> ea < e \<or> ea \<notin> E)) \<and> (ee e E < e \<and> ee e E \<in> E \<or> \<not> Inf E < e)"
          by moura
        obtain aa :: "ereal \<Rightarrow> 'a" and aaa :: "ereal \<Rightarrow> 'a" where
          f7: "\<forall>e. (aa e \<in> A \<and> (aa e, v) \<in> E \<and> ereal (edge_slack pot (aa e) v) = e \<or> (\<forall>a. e \<noteq> ereal (edge_slack pot a v) \<or> (a, v) \<notin> E \<or> a \<notin> A)) \<and> ((\<exists>a. e = ereal (edge_slack pot a v) \<and> (a, v) \<in> E \<and> a \<in> A) \<or> (\<forall>a. a \<notin> A \<or> (a, v) \<notin> E \<or> ereal (edge_slack pot a v) \<noteq> e))"
          by moura
        have f8: "Inf {ereal (edge_slack pot a v) |a. (a, v) \<in> E \<and> a \<in> A} = ereal sl"
          using a3 a1 by fastforce
        have f9: "ereal sl < ereal (edge_slack pot vaa v)"
          using a5 a3 less_ereal.simps(1) by blast
        have f10: "\<exists>a. (v, vaa) = (v, a) \<and> (a, v) \<in> E \<and> a \<in> A \<and> (\<forall>aa. aa \<in> A \<longrightarrow> (aa, v) \<in> E \<longrightarrow> \<not> edge_slack pot aa v < edge_slack pot a v)"
          using a4 a2 by blast
        have "\<forall>e. (\<exists>a. ee e {ereal (edge_slack pot a v) |a. (a, v) \<in> E \<and> a \<in> A} = ereal (edge_slack pot a v) \<and> (a, v) \<in> E \<and> a \<in> A) \<or> \<not> ereal sl < e"
          using f8 f6 by (smt (z3) mem_Collect_eq)
        then have f11: "\<exists>a. ee (ereal (edge_slack pot vaa v)) {ereal (edge_slack pot a v) |a. (a, v) \<in> E \<and> a \<in> A} = ereal (edge_slack pot a v) \<and> (a, v) \<in> E \<and> a \<in> A"
          using f9 by meson
        have f12: "\<forall>e a ab. aa e \<notin> A \<or> (\<forall>aa. (a, ab) \<noteq> (v, aa) \<or> (aa, v) \<notin> E \<or> aa \<notin> A \<or> (\<exists>a. a \<in> A \<and> (a, v) \<in> E \<and> edge_slack pot a v < edge_slack pot aa v)) \<or> (aa e, v) \<notin> E \<or> (\<forall>a. e \<noteq> ereal (edge_slack pot a v) \<or> (a, v) \<notin> E \<or> a \<notin> A) \<or> (\<forall>aa. (a, ab) \<noteq> (v, aa) \<or> (aa, v) \<notin> E \<or> aa \<notin> A \<or> (\<exists>a. a \<in> A \<and> (a, v) \<in> E \<and> edge_slack pot a v < edge_slack pot aa v)) \<or> \<not> e < ereal (edge_slack pot ab v)"
          by (metis (no_types) less_ereal.simps(1) prod.inject)
        have f13: "(aa (ee (ereal (edge_slack pot vaa v)) {ereal (edge_slack pot a v) |a. (a, v) \<in> E \<and> a \<in> A}), v) \<in> E"
          using f11 f7 by blast
        have "aa (ee (ereal (edge_slack pot vaa v)) {ereal (edge_slack pot a v) |a. (a, v) \<in> E \<and> a \<in> A}) \<in> A"
          using f11 f7 by blast
        then show False
          using f13 f12 f11 f10 f9 f8 f6 by (smt (z3))
      qed
      have help6: " va \<in> vset_set vs \<Longrightarrow>
          edge_slack pot u v < edge_slack pot va v \<Longrightarrow>
          (\<And>vaa. vaa \<in> vset_set vs \<Longrightarrow> edge_slack pot u v < edge_slack pot vaa v \<Longrightarrow> False) \<Longrightarrow> False" for va
        by blast 
      have help7:" Inf {ereal (edge_slack pot u v) |u. (u, v) \<in> E \<and> u \<in> A} = ereal sl \<Longrightarrow>
         edge_slack pot u v < sl \<Longrightarrow>
         ereal (edge_slack pot u v) =
         Inf {ereal (edge_slack pot ua v) |ua. (ua = u \<or> (ua, v) \<in> E) \<and> (ua = u \<or> ua \<in> A)}"
        by (smt (verit, ccfv_threshold) Inf_less_iff less_ereal.simps(1) linorder_cases mem_Collect_eq
            order_less_irrefl)
      have help8: "
         Inf {ereal (edge_slack pot u v) |u. (u, v) \<in> E \<and> u \<in> A} = ereal sl \<Longrightarrow> 
         edge_slack pot u v < sl \<Longrightarrow>
         edge_slack pot y v < edge_slack pot u v \<Longrightarrow> (y, v) \<in> E \<Longrightarrow> y \<in> A \<Longrightarrow> False" for y
        by (smt (verit, best) Inf_less_iff less_ereal.simps(1) mem_Collect_eq)
      have help9: "
          Inf {ereal (edge_slack pot u v) |u. (u, v) \<in> E \<and> u \<in> A} = ereal sl \<Longrightarrow>
          edge_slack pot u v < sl \<Longrightarrow>
          \<forall>y. y \<noteq> u \<and> (y, v) \<notin> E \<or> y \<noteq> u \<and> y \<notin> A \<or> \<not> edge_slack pot y v < edge_slack pot ua v \<Longrightarrow>
          (ua, v) \<in> E \<Longrightarrow> ua \<in> A \<Longrightarrow> ua = u" for ua
         by (smt (verit, best) Inf_less_iff less_ereal.simps(1) mem_Collect_eq)
       have help10: "Inf {ereal (edge_slack pot u v) |u. (u, v) \<in> E \<and> u \<in> A} = ereal sl \<Longrightarrow>
                     \<not> edge_slack pot u v < sl \<Longrightarrow>
              ereal sl = Inf {ereal (edge_slack pot ua v) |ua. (ua = u \<or> (ua, v) \<in> E) \<and> (ua = u \<or> ua \<in> A)}"
         by (smt (z3) Inf_less_iff less_ereal.simps(1) linorder_cases mem_Collect_eq
            order_less_irrefl)
       have help11: "
          Inf {ereal (edge_slack pot u v) |u. (u, v) \<in> E \<and> u \<in> A} = ereal sl \<Longrightarrow>
          \<not> edge_slack pot u v < sl \<Longrightarrow>
          \<forall>y. y \<in> A \<longrightarrow> (y, v) \<in> E \<longrightarrow> \<not> edge_slack pot y v < edge_slack pot ua v \<Longrightarrow>
          edge_slack pot u v < edge_slack pot ua v \<Longrightarrow> False" for ua
         by (smt (verit, ccfv_SIG) Inf_less_iff less_ereal.simps(1) mem_Collect_eq)
       have help12: 
    "Inf {ereal (edge_slack pot u v) |u. (u, v) \<in> E \<and> u \<in> A} = ereal sl \<Longrightarrow>
    edge_slack pot u v \<noteq> sl \<Longrightarrow> \<not> edge_slack pot u v < sl \<Longrightarrow>
    \<forall>y. y \<noteq> u \<and> (y, v) \<notin> E \<or> y \<noteq> u \<and> y \<notin> A \<or> \<not> edge_slack pot y v < edge_slack pot u v \<Longrightarrow>
    (u, v) \<in> E"
         by(smt (verit, best) Inf_less_iff less_ereal.simps(1) mem_Collect_eq)
       have help13:
    "Inf {ereal (edge_slack pot u v) |u. (u, v) \<in> E \<and> u \<in> A} = ereal sl \<Longrightarrow>
      edge_slack pot u v \<noteq> sl \<Longrightarrow>
     \<not> edge_slack pot u v < sl \<Longrightarrow>
      \<forall>y. y \<noteq> u \<and> (y, v) \<notin> E \<or> y \<noteq> u \<and> y \<notin> A \<or> \<not> edge_slack pot y v < edge_slack pot u v \<Longrightarrow> u \<in> A"
         by (smt (verit, best) Inf_less_iff less_ereal.simps(1) mem_Collect_eq)
 
        from 1  show ?case
          using good_slacks_generalD(1,2)[OF that(2), of v, symmetric] one'  inf_ereal_find_inf 
                help3 help5 
          by(auto simp add: inner_def  abstract_min_slack_def
                  abstract_min_slack_edges_def is_arg_min_def  vset_set_specs.set_empty
                  abstract_min_slack_upd[OF slack_basic_invarD(1)[OF that(1)]] True
                  abstract_min_slack_edges_upd[OF slack_basic_invarD(1)[OF that(1)]]
                  vset_set_specs.set_insert[OF vset_set_specs.invar_empty] 
                              slack_map.map_update[OF slack_basic_invarD(1)[OF that(1)]] Let_def
                  vset_set_specs.set_insert[OF slack_basic_invarD(2)[OF that(1)]]
                  eq_commute[of _ "{(v, va) |va. va \<in> vset_set vs}"]
              intro: help1 help2 help8 help9 help3 help13  help12 help10 help7 help11,
              insert help4 help6 help11, auto) force+
    qed
  qed
next
  case False
  note false = this
  show ?thesis
   proof(cases "slack_lookup slacks va", all \<open>cases "slack_lookup slacks v"\<close>, goal_cases)
     case 1
     have a1:"abstract_min_slack slacks va =
        Inf {ereal (edge_slack pot ua va) |ua. (ua, va) \<in>  E \<and> ua \<in>  A}"
       using good_slacks_generalD(1) one' that(2) by blast
     hence a2:"\<nexists> ua. (ua, va) \<in>  E \<and> ua \<in>  A" 
       by(force simp add: abstract_min_slack_def 1 Inf_eq_PInfty dest!: sym[of \<infinity>])
     have a5:"{ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> (ua = u \<or> ua \<in> A)} = 
          {ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> ( ua \<in> A)}"
       using a2 good_slacks_generalD(5)[OF that(2)] by auto
     show ?case
       using false a2 a5 a1
       by(auto simp add: abstract_min_slack_def inner_def Let_def 1
           abstract_min_slack_edges_def slack_map.map_update[OF slack_basic_invarD(1)[OF that(1)]]
           is_arg_min_def)
   next
     case (2 a)
     then obtain vs sl where a_split:"a = (sl, vs)" by (cases a) auto
     have a1:"abstract_min_slack slacks va =
        Inf {ereal (edge_slack pot ua va) |ua. (ua, va) \<in>  E \<and> ua \<in>  A}"
       using good_slacks_generalD(1) one' that(2) by blast
     hence a2:"\<nexists> ua. (ua, va) \<in>  E \<and> ua \<in>  A" 
       by(force simp add: abstract_min_slack_def 2 Inf_eq_PInfty dest!: sym[of \<infinity>])
     have a5:"{ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> (ua = u \<or> ua \<in> A)} = 
          {ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> ( ua \<in> A)}"
       using a2 good_slacks_generalD(5)[OF that(2)] by auto
     then show ?case 
       using false a2 a5 a1
       by(auto simp add: abstract_min_slack_def inner_def Let_def a_split 2
           abstract_min_slack_edges_def slack_map.map_update[OF slack_basic_invarD(1)[OF that(1)]]
           is_arg_min_def)
   next
     case (3 a)
     then obtain vs sl where a_split:"a = (sl, vs)" by (cases a) auto
     have a1:"abstract_min_slack slacks va =
        Inf {ereal (edge_slack pot ua va) |ua. (ua, va) \<in>  E \<and> ua \<in>  A}"
             "abstract_min_slack_edges slacks va =
            {(va, u) |u. is_arg_min (\<lambda>u. edge_slack pot u va) (\<lambda>u. (u, va) \<in> E \<and> u \<in> A) u}"
       using good_slacks_generalD(1,2)[OF that(2) one'] by auto
     have a2: "{ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> (ua = u \<or> ua \<in> A)} = 
               {ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and>  ua \<in> A}
              \<union> (if (u, va) \<in> E then {(ereal (edge_slack pot u va))} else {})"
       by auto
     have a3: "Inf {ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> (ua = u \<or> ua \<in> A)}
               = (if (u, va) \<in> E then
                  min  (ereal (edge_slack pot u va))
                       (Inf {ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> ua \<in> A})              
                 else Inf {ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> ua \<in> A})"
       by(auto simp add: a2)
     have a4: "Inf {ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> (ua = u \<or> ua \<in> A)} =
    min (ereal (edge_slack pot u va))
     (Inf {ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> ua \<in> A}) \<Longrightarrow>
    \<forall>x\<in>E. fst x \<in> A \<Longrightarrow>
    Inf {ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> ua \<in> A} =
    min (ereal (edge_slack pot u va)) (Inf {ereal (edge_slack pot u va) |u. (u, va) \<in> E \<and> u \<in> A})"
     by (smt (verit, ccfv_threshold) Collect_cong fst_conv)
     show ?case 
       using false a1 a3 good_slacks_generalD(5)[OF  that(2)] a_split a4
       by(force simp add: abstract_min_slack_def inner_def Let_def a_split 3
           abstract_min_slack_edges_def slack_map.map_update[OF slack_basic_invarD(1)[OF that(1)]]
           is_arg_min_def image_subset_iff) 
   next
     case (4 a aa)
     then obtain vs sl where a_split:"a = (sl, vs)" by (cases a) auto
     from 4 obtain avs asl where aa_split:"aa = (asl, avs)" by (cases aa) auto
     have a1:"abstract_min_slack slacks va =
        Inf {ereal (edge_slack pot ua va) |ua. (ua, va) \<in>  E \<and> ua \<in>  A}"
             "abstract_min_slack_edges slacks va =
            {(va, u) |u. is_arg_min (\<lambda>u. edge_slack pot u va) (\<lambda>u. (u, va) \<in> E \<and> u \<in> A) u}"
       using good_slacks_generalD(1,2)[OF that(2) one'] by auto
     have a2: "{ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> (ua = u \<or> ua \<in> A)} = 
               {ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and>  ua \<in> A}
              \<union> (if (u, va) \<in> E then {(ereal (edge_slack pot u va))} else {})"
       by auto
     have a3: "Inf {ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> (ua = u \<or> ua \<in> A)}
               = (if (u, va) \<in> E then
                  min  (ereal (edge_slack pot u va))
                       (Inf {ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> ua \<in> A})              
                 else Inf {ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> ua \<in> A})"
       by(auto simp add: a2)
     have a4: "Inf {ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> (ua = u \<or> ua \<in> A)} =
    min (ereal (edge_slack pot u va))
     (Inf {ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> ua \<in> A}) \<Longrightarrow>
    \<forall>x\<in>E. fst x \<in> A \<Longrightarrow>
    Inf {ereal (edge_slack pot ua va) |ua. (ua, va) \<in> E \<and> ua \<in> A} =
    min (ereal (edge_slack pot u va)) (Inf {ereal (edge_slack pot u va) |u. (u, va) \<in> E \<and> u \<in> A})"
     by (smt (verit, ccfv_threshold) Collect_cong fst_conv)
     show ?case 
       using false a1 a3 good_slacks_generalD(5)[OF  that(2)] a_split a4 aa_split
       by(force simp add: abstract_min_slack_def inner_def Let_def a_split 4
           abstract_min_slack_edges_def slack_map.map_update[OF slack_basic_invarD(1)[OF that(1)]]
           is_arg_min_def image_subset_iff  ) 
   qed
 qed 
next
  case 2
  show ?case
    using good_slacks_generalD(3) that(2) by auto
next
  case 3
  show ?case
    using good_slacks_generalD(4) that(2) by auto
next
  case 4
  show ?case
    using good_slacks_general_def that(2) by auto
qed
  show "slack_basic_invar (inner u v slacks)"
       "dom (slack_lookup (inner u v slacks)) = insert v (dom (slack_lookup slacks))"
   using slack_basic_invarD[OF that(1)]
   by(auto intro!: slack_basic_invarI slack_map.invar_update 
         simp add: inner_def Let_def  slack_map.map_update if_split[of "\<lambda> x. x = Some (_, _)"]
                  vset_set_specs.invar_insert vset_set_specs.invar_empty
       split: option.split prod.split)
qed
  have effect_inner_iterated:
     "good_slacks_general (edge_slack pot) (insert u A) B ({ (u, v) | v. v \<in> set vs} \<union> E)
     (foldr (inner u) vs slacks) \<and>
      slack_basic_invar (foldr (inner u) vs slacks) \<and>
      dom (slack_lookup (foldr (inner u) vs slacks)) =
      set vs \<union> (dom (slack_lookup slacks))" 
     if "slack_basic_invar slacks"  "good_slacks_general (edge_slack pot) A B E slacks"
        "\<nexists> v. (u, v) \<in> E"
    for u vs A B E slacks
    using that(1,2)
    proof(induction vs)
      case (Cons v vs)
      note IH = this
      have set_simpl:"{(u, va) |va. va = v \<or> va \<in> set vs} \<union> E = 
            insert (u, v) ({(u, va) |va. va \<in> set vs} \<union> E)" by auto
      have u_insert_double: "insert u A = insert u (insert u A)" by auto
      have "good_slacks_general (edge_slack pot) (insert u A) B
     ({(u, va) |va. va \<in> set (v # vs)} \<union> E) (foldr (inner u) (v # vs) slacks)"
      proof(cases vs)
        case Nil
        then show ?thesis 
          using Cons(2,3)
          by (auto intro!: conjunct1[OF effect_inner] simp add:  set_simpl)
      next
        case (Cons a list)
        show ?thesis 
         apply(simp add:  set_simpl)
         apply(subst u_insert_double)
         using IH(2,3)  IH(1)[OF IH(2,3)] Cons
         by (intro conjunct1[OF effect_inner]) auto
     qed
     moreover have "slack_basic_invar (foldr (inner u) (v # vs) slacks)"
      proof(cases vs)
        case Nil
        then show ?thesis 
          using Cons(2,3)
          by (auto intro!: conjunct1[OF conjunct2[OF effect_inner]] simp add:  set_simpl)
      next
        case (Cons a list)
        show ?thesis 
         using IH(2,3)  IH(1)[OF IH(2,3)] Cons
         by (auto intro: conjunct1[OF conjunct2[OF effect_inner]]) 
     qed
     moreover have "dom (slack_lookup (foldr (inner u) (v # vs) slacks))
                       = set (v # vs) \<union> dom (slack_lookup slacks)"
      proof(cases vs)
        case Nil
        then show ?thesis 
          using Cons(2,3)
          by (auto intro!: conjunct2[OF conjunct2[OF effect_inner]] simp add:  set_simpl)
      next
        case (Cons a list)
        show ?thesis 
         using IH(2,3) IH(1)[OF IH(2,3)] Cons conjunct2[OF conjunct2[OF effect_inner]] 
         by force
     qed
     ultimately show ?case by simp  
   next
     case Nil
     thus ?case
       using that(3)
       by(auto intro!: good_slacks_general_extended_lonely_left)
   qed
  have effect_outer:
     "good_slacks_general (edge_slack pot) (insert u A)
              B ({ (u, v) | v. v \<in> right_neighb_abstract u} \<union> E)
     (outer u slacks) \<and>
      slack_basic_invar (outer u slacks) \<and>
      dom (slack_lookup (outer u slacks)) =
      right_neighb_abstract u \<union> (dom (slack_lookup slacks))" 
     if "slack_basic_invar slacks"  "good_slacks_general (edge_slack pot) A B E slacks"
        "\<nexists> v. (u, v) \<in> E"
    for u A B E slacks
    unfolding outer_def
  proof(cases "right_neighbs u", goal_cases)
    case 1
     then show ?case
     using effect_inner_iterated[OF that(1,2), of u] reight_neighbs vset_flatten(1)
     by(auto simp add: outer_def that right_neighb_abstract_def  
          good_slacks_general_extended_lonely_left split: option.split)
    next
      case (2 vs)
      show ?case
        using effect_inner_iterated[OF that(1,2), of u]
              vset_flatten(1)[OF reight_neighbs[OF 2], symmetric]
        by(auto simp add: outer_def that right_neighb_abstract_def 2 split: option.split)
    qed
  have effect_outer_iterated:
     "good_slacks_general (edge_slack pot) (set vs \<union> A)
              B ({ (u, v) | u v. u \<in> set vs \<and> v \<in> right_neighb_abstract u} \<union> E)
     (foldr outer vs slacks) \<and>
      slack_basic_invar (foldr outer vs slacks) \<and>
      dom (slack_lookup (foldr outer vs slacks)) =
      \<Union> (right_neighb_abstract ` (set vs)) \<union> (dom (slack_lookup slacks))" 
     if "slack_basic_invar slacks"  "good_slacks_general (edge_slack pot) A B E slacks"
        "\<And> u. u \<in> set vs \<Longrightarrow> \<nexists> v . (u, v) \<in> E" "distinct vs"    for  A B E slacks vs 
    using that
    proof(induction vs)
      case (Cons v vs)
      note IH = this
      have no_v_edge_vs: "(\<And>u. u \<in> set vs \<Longrightarrow> \<nexists>v. (u, v) \<in> E)" 
        using IH(4) by auto
      have distinct_vs: "distinct vs"
        using IH(5) by auto
      have set_simpl:"{(u, va). (u = v \<or> u \<in> set vs) \<and> va \<in> right_neighb_abstract u} \<union> E
            = { (v, va) | va. va \<in> right_neighb_abstract v} \<union> 
              ({(u, va). u \<in> set vs \<and> va \<in> right_neighb_abstract u} \<union> E)" by auto
      have big_u_simp: "\<Union> (right_neighb_abstract ` set (v # vs)) = 
                       (right_neighb_abstract v) \<union> \<Union> (right_neighb_abstract ` set vs)"
        by auto
      have "good_slacks_general (edge_slack pot) (set (v # vs) \<union> A) B
             ({(u, va) |u va. u \<in> set (v # vs) \<and> va \<in> right_neighb_abstract u} \<union> E)
             (foldr outer (v # vs) slacks)"
        using  IH(1)[OF IH(2,3) no_v_edge_vs distinct_vs, simplified]  IH(4,5) 
        by (auto intro!: conjunct1[OF effect_outer] simp add:  set_simpl)
      moreover have "slack_basic_invar (foldr outer (v # vs) slacks)"
        using  IH(1)[OF IH(2,3) no_v_edge_vs distinct_vs, simplified]  IH(4,5) 
        by (auto intro!: conjunct1[OF conjunct2[OF effect_outer]])    
     moreover have "dom (slack_lookup (foldr outer (v # vs) slacks)) =
           \<Union> (right_neighb_abstract ` set (v # vs)) \<union> dom (slack_lookup slacks)"
       apply(simp add: big_u_simp)
       apply(subst conjunct2[OF conjunct2[OF effect_outer]])
        using  IH(1)[OF IH(2,3) no_v_edge_vs distinct_vs, simplified]  IH(4,5) 
        by auto
     ultimately show ?case by simp  
   qed simp
   have pairs_set_split:"{(u, v) |u v. v \<in> right_neighb_abstract u \<and> u \<in> set flat_new_left \<union> A} = 
      {(u, v) |u v. u \<in> set flat_new_left \<and> v \<in> right_neighb_abstract u} \<union>
      {(u, v) |u v. v \<in> right_neighb_abstract u \<and> u \<in> A}"
     by auto
  have  "good_slacks (\<lambda> u v. edge_slack pot u v) (A \<union> vset_set new_left)
           B (new_slacks slacks pot new_left) \<and>
           slack_basic_invar (new_slacks slacks pot new_left) \<and>
           dom (slack_lookup (new_slacks slacks pot new_left)) = 
           dom (slack_lookup slacks) \<union> \<Union> (right_neighb_abstract ` vset_set new_left)"
    using new_left_flattened(2)  assms(3,4)
    unfolding new_slacks_def new_left_flattened(1)[symmetric] flat_new_left_def[symmetric]
              fun_cong[OF inner_def, symmetric] outer_def[symmetric] Un_commute[of _ "\<Union> _"]
              Un_commute[of _ "set _"] 
              pairs_set_split good_slacks_good_slacks_general(3)
    by(intro effect_outer_iterated[OF assms(1), of A B _ flat_new_left]) auto
  thus "good_slacks (edge_slack pot) (A \<union> vset_set new_left) B (new_slacks slacks pot new_left)"
       " slack_basic_invar (new_slacks slacks pot new_left)"
       "dom (slack_lookup (new_slacks slacks pot new_left)) =
       dom (slack_lookup slacks) \<union> \<Union> (right_neighb_abstract ` vset_set new_left)"
    by auto
qed
