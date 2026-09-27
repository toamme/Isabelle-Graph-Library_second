theory Fixed_Univ_Key_Value_Queue_Specs_Imp
  imports Separation_Logic_Imperative_HOL_Partial.Sep_Main 
          Fixed_Univ_Key_Value_Queue_Specs
begin

locale key_value_queue_imp =
  key_value_queue where U = U
    and queue_empty = queue_empty
    and queue_extract_min = queue_extract_min
    and queue_decrease_key = queue_decrease_key
    and queue_insert = queue_insert
    and queue_invar = queue_invar
    and queue_abstract = queue_abstract
  for U :: "'v::heap set"
    and queue_empty :: "'queue"
    and queue_extract_min :: "'queue \<Rightarrow> ('queue \<times> 'v option)"
    and queue_decrease_key :: "'queue \<Rightarrow> 'v \<Rightarrow> ('a::linorder) \<Rightarrow> 'queue"
    and queue_insert :: "'queue \<Rightarrow> 'v \<Rightarrow> 'a \<Rightarrow> 'queue"
    and queue_invar :: "'queue \<Rightarrow> bool"
    and queue_abstract :: "'queue \<Rightarrow> ('v \<times> 'a) set" +
  fixes queue_key :: "'ai::heap \<Rightarrow> 'a"
    and queue_assn :: "'queue \<Rightarrow> 'queuei \<Rightarrow> assn"
    and queue_empty_imp :: "'queuei Heap"
    and queue_extract_min_imp :: "'queuei \<Rightarrow> 'v option Heap"
    and queue_decrease_key_imp :: "'queuei \<Rightarrow> 'v \<Rightarrow> 'ai \<Rightarrow> unit Heap"
    and queue_insert_imp :: "'queuei \<Rightarrow> 'v \<Rightarrow> 'ai \<Rightarrow> unit Heap"
  assumes queue_empty_rule[sep_heap_rules]:
      "<emp> queue_empty_imp <\<lambda>Hi. queue_assn queue_empty Hi>"
    and queue_extract_min_rule[sep_heap_rules]:
      "queue_invar H \<Longrightarrow>
       <queue_assn H Hi> queue_extract_min_imp Hi
       <\<lambda>r. queue_assn (fst (queue_extract_min H)) Hi * \<up>(r = snd (queue_extract_min H))>"
    and queue_insert_rule[sep_heap_rules]:
      "\<lbrakk>queue_invar H; x \<in> U; \<nexists>k. (x, k) \<in> queue_abstract H\<rbrakk> \<Longrightarrow>
       <queue_assn H Hi> queue_insert_imp Hi x k
       <\<lambda>_. queue_assn (queue_insert H x (queue_key k)) Hi>"
    and queue_decrease_key_rule[sep_heap_rules]:
      "\<lbrakk>queue_invar H; x \<in> U; (x, k') \<in> queue_abstract H; queue_key k < k'\<rbrakk> \<Longrightarrow>
       <queue_assn H Hi> queue_decrease_key_imp Hi x k
       <\<lambda>_. queue_assn (queue_decrease_key H x (queue_key k)) Hi>"

end