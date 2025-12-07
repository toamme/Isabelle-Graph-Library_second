theory Hungarian_Example
  imports Hungarian_Method_Instantiation  Directed_Set_Graphs.Pair_Graph_RBT
          "HOL-Library.Product_Lexorder"
begin

section \<open>HM on Example Graph\<close>

hide_const right 

definition "edges_and_costs = [(0::nat, 1::nat, 1::real), (0,3, -10), 
(0,5, 2/3), (0,7, 1/87), (2,5, -12), (2,9, 100), (2,1, 2.5), (4,5, 2+1/7), 
(4,3, -1.3), (4,7, 2.4),
   (6,1, 1.8+1/9), (6,9, 200), (8, 9, 10000), (8,1, 6.2), (0, 9, -100),
 (2, 7, -100), (2,3,-40), (2,9,-100), (4,9, -100)]"

definition "edges = zip (map fst edges_and_costs) (map (fst o snd) edges_and_costs)"

definition "c_list = zip (zip (map fst edges_and_costs)  (map (fst o snd) edges_and_costs)) 
                   (map (snd o snd) edges_and_costs)"

definition "c_impl = foldr (\<lambda> xy tree.
              update (prod.swap (prod.fst xy)) (prod.snd xy)
              ( update (prod.fst xy) (prod.snd xy) tree))
              c_list Leaf"

definition "weights = (\<lambda> u v. abstract_real_map (lookup c_impl) (u, v))"

definition "bipartite_test = filter odd (map fst edges) @ filter even (map snd edges)"
value bipartite_test

definition "G = a_graph edges"

definition "left = foldr (\<lambda> x tree. RBT.insert x tree) (map fst edges_and_costs) Leaf"
definition "right = foldr (\<lambda> x tree. RBT.insert x tree) (map (fst o snd) edges_and_costs) Leaf"
thm hungarian_def

definition "final_matching = hungarian left right weights (lookup G)
      lookup update"

value "final_matching"

value "inorder (the final_matching)"

end