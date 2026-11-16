theory UnionFind_Representative_Specs
  imports Main AI_Provenance.Provenance
begin

provenance ai_human

section "Union-find with representatives over a fixed universe"

text "The representative observation describes the partition and is used in specifications.
  Executable lookup uses find, which may compress paths and returns the updated structure.
  Union may choose either class representative; clients do not prescribe its balancing rule.
  Reset accepts an existing workspace for a later refinement that reuses its storage."

locale fixed_univ_union_find =
  fixes K :: "'a set"
    and uf_invar :: "'uf \<Rightarrow> bool"
    and uf_representative :: "'uf \<Rightarrow> 'a \<Rightarrow> 'a"
    and uf_find :: "'uf \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'uf"
    and uf_union :: "'uf \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'uf"
    and uf_reset :: "'uf \<Rightarrow> 'uf"
  assumes representative_closed:
    "\<lbrakk>uf_invar U; x \<in> K\<rbrakk> \<Longrightarrow> uf_representative U x \<in> K"
    and representative_idempotent:
    "\<lbrakk>uf_invar U; x \<in> K\<rbrakk> \<Longrightarrow>
      uf_representative U (uf_representative U x) = uf_representative U x"
    and find_invar:
    "\<lbrakk>uf_invar U; x \<in> K\<rbrakk> \<Longrightarrow> uf_invar (snd (uf_find U x))"
    and find_result:
    "\<lbrakk>uf_invar U; x \<in> K\<rbrakk> \<Longrightarrow> fst (uf_find U x) = uf_representative U x"
    and find_representatives:
    "\<lbrakk>uf_invar U; x \<in> K; y \<in> K\<rbrakk> \<Longrightarrow>
      uf_representative (snd (uf_find U x)) y = uf_representative U y"
    and union_invar:
    "\<lbrakk>uf_invar U; x \<in> K; y \<in> K\<rbrakk> \<Longrightarrow> uf_invar (uf_union U x y)"
    and union_representative:
    "\<lbrakk>uf_invar U; x \<in> K; y \<in> K\<rbrakk> \<Longrightarrow>
      uf_representative (uf_union U x y) x \<in> {uf_representative U x, uf_representative U y}"
    and union_representatives:
    "\<lbrakk>uf_invar U; x \<in> K; y \<in> K; z \<in> K\<rbrakk> \<Longrightarrow>
      uf_representative (uf_union U x y) z =
        (if uf_representative U z \<in> {uf_representative U x, uf_representative U y}
         then uf_representative (uf_union U x y) x else uf_representative U z)"
    and reset_invar:
    "uf_invar U \<Longrightarrow> uf_invar (uf_reset U)"
    and reset_representatives:
    "\<lbrakk>uf_invar U; x \<in> K\<rbrakk> \<Longrightarrow> uf_representative (uf_reset U) x = x"
begin

definition "same_component U x y \<longleftrightarrow> uf_representative U x = uf_representative U y"

definition "component U x = {y \<in> K. same_component U x y}"

lemma representative_in_component:
  "\<lbrakk>uf_invar U; x \<in> K\<rbrakk> \<Longrightarrow> uf_representative U x \<in> component U x"
  by(auto simp: component_def same_component_def representative_closed representative_idempotent)

lemma component_representative:
  "\<lbrakk>uf_invar U; x \<in> K\<rbrakk> \<Longrightarrow> component U (uf_representative U x) = component U x"
  by(auto simp: component_def same_component_def representative_idempotent)

lemma find_component:
  "\<lbrakk>uf_invar U; x \<in> K; y \<in> K\<rbrakk> \<Longrightarrow> component (snd (uf_find U x)) y = component U y"
  by(auto simp: component_def same_component_def find_representatives)

lemma find_closed:
  "\<lbrakk>uf_invar U; x \<in> K\<rbrakk> \<Longrightarrow> fst (uf_find U x) \<in> K"
  by(auto simp: find_result representative_closed)

lemma union_same_component:
  "\<lbrakk>uf_invar U; x \<in> K; y \<in> K\<rbrakk> \<Longrightarrow> same_component (uf_union U x y) x y"
  using union_representatives[of U x y y]
  by(auto simp: same_component_def)

lemma union_other_representative:
  "\<lbrakk>uf_invar U; x \<in> K; y \<in> K; z \<in> K;
    \<not> same_component U z x; \<not> same_component U z y\<rbrakk> \<Longrightarrow>
    uf_representative (uf_union U x y) z = uf_representative U z"
  using union_representatives[of U x y z]
  by(auto simp: same_component_def)

lemma reset_component:
  "\<lbrakk>uf_invar U; x \<in> K\<rbrakk> \<Longrightarrow> component (uf_reset U) x = {x}"
  by(auto simp: component_def same_component_def reset_representatives)

bundle automation = representative_closed[intro] representative_idempotent[simp]
  find_invar[intro] find_result[simp] find_representatives[simp] find_closed[intro]
  union_invar[intro] union_same_component[intro] union_other_representative[simp]
  reset_invar[intro] reset_representatives[simp]

end

subsection "A functional model"

lemma function_union_find:
  "fixed_univ_union_find K
    (\<lambda>R. \<forall>x \<in> K. R x \<in> K \<and> R (R x) = R x)
    (\<lambda>R x. R x) (\<lambda>R x. (R x, R))
    (\<lambda>R x y z. if R z = R x then R y else R z) (\<lambda>_. id)"
  by unfold_locales auto

end
