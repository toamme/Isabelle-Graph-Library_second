theory Set_Map_Fold
  imports Imperative.Imperative_DS
begin

locale set_fold_locale = 
imp_set_iterate where is_set = is_set and it_next = it_next +
imp_set_ins where ins = ins and is_set = is_set +
imp_set_empty where empty = empty and is_set = is_set
for is_set :: "nat set \<Rightarrow> 'simpl \<Rightarrow> assn" 
and ins :: "nat \<Rightarrow> 'simpl \<Rightarrow> 'simpl Heap"
and empty :: "'simpl Heap"
and it_next :: "'it \<Rightarrow> (nat \<times> 'it) Heap"
begin


partial_function (heap) set_fold_loop ::"'it \<Rightarrow>(nat => nat => nat Heap) \<Rightarrow> nat  \<Rightarrow> nat Heap"
  where
"set_fold_loop it f acc = 
  (do {b <- it_has_next it;
       if \<not> b then  return acc
       else  do {
         (x, it') <- it_next it;
          acc' <- f x acc;
           set_fold_loop it' f acc'
       }})"

definition "set_fold Simpl= (\<lambda> f acc. 
         do {it_init <- it_init Simpl;
             set_fold_loop it_init f acc})"

lemmas [code] = set_fold_loop.simps set_fold_def
end



(*interpretation hs: imp_set_iterate 
  is_hashset hs_is_it hs_it_init hs_it_has_next hs_it_next
  by (rule hs_iterate_impl)*)

definition "from_list_impl (xs:: nat list) \<equiv>
  do {S <- hs_new; foldM (\<lambda> x S. hs_ins  x S) xs S }"

  setup Locale_Code.open_block  
interpretation sfl: set_fold_locale
 hs_is_it hs_it_init hs_it_has_next is_hashset hs_ins hs_new hs_it_next
  by unfold_locales
setup Locale_Code.close_block

definition "set_fold_loop = 
  (sfl.set_fold_loop::
   nat \<times> (nat \<times> unit) list \<times> (nat, unit) hashtable 
    \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> nat Heap) \<Rightarrow> nat \<Rightarrow> nat Heap)"

definition "set_fold = (sfl.set_fold::
            ((nat, unit) hashtable \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> nat Heap) \<Rightarrow> nat \<Rightarrow> nat Heap))"(*(\<lambda> f acc. 
         do {it_init <- hs_it_init simpl;
             set_fold_loop it_init f acc})"*)

definition "f_here (x::nat) y = do{return (x+y)}"

(*definition "sinit = from_list_impl [1,2,3,4]"*)
                           
definition "hs_it_init_nat = (hs_it_init::(nat, unit) hashtable
   \<Rightarrow> (nat \<times> (nat \<times> unit) list \<times> (nat, unit) hashtable) Heap)"(* do {s <- sinit; it <- hs_it_init s; return it}"*)

definition "hs_new_nat = (hs_new::(nat, unit) hashtable Heap)"

 export_code set_fold set_fold_loop from_list_impl hs_it_init_nat hs_new_nat f_here checking SML_imp

 ML_val \<open>
    val noi = @{code nat_of_integer}
    val from_list_impl  = @{code from_list_impl} o map  noi
    val set_fold_loop = @{code set_fold_loop}
    val set_fold = @{code set_fold}
    val hs_it_init = @{code hs_it_init_nat}
    val hs_new = @{code hs_new_nat}
    val f_here = @{code f_here}
   
    val S = from_list_impl [0,1,2,3,4,5] ()
    val all_sum = set_fold S f_here (noi 3) ()
  
  \<close>


end