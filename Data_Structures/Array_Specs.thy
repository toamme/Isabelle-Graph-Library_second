theory Array_Specs
  imports Main
begin

locale abstract_array =
fixes K::"'a set"
and abstract_array_invar::"'array \<Rightarrow> bool"
and abstract_array_upd::"'array \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'array"
and abstract_array_lookup::"'array \<Rightarrow> 'a \<Rightarrow> 'b"
assumes abstract_array_upd:
"\<And> A k v. 
 \<lbrakk>abstract_array_invar A; k \<in> K\<rbrakk> \<Longrightarrow>
abstract_array_lookup (abstract_array_upd A k v) =
(abstract_array_lookup A) (k := v)"
and abstract_array_upd_invar:
"\<And> A k v. \<lbrakk>abstract_array_invar A; k \<in> K\<rbrakk> 
\<Longrightarrow> abstract_array_invar (abstract_array_upd A k v)"

end