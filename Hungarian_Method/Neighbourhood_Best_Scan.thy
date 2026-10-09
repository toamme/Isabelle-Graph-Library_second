theory Neighbourhood_Best_Scan
  imports Data_Structures.Iterable_Set_Specs Complex_Main
begin

section \<open>The Best Neighbour in a Collection of Neighbourhoods\<close>

text \<open>A cursor scan over the neighbourhood of a vertex @{term u} that keeps a neighbour of minimum
      key. Among neighbours of equal key, a neighbour satisfying @{term pref} wins. The key and the
      preference are arguments, so that the scan can be used with keys that change between calls.
      The scan is shared by the shortcut of the Hungarian method and by the initial potential.\<close>

locale nb_best_scan_spec =
  fixes rnb_current :: "'g \<Rightarrow> 'v \<Rightarrow> 'v"
    and rnb_has :: "'g \<Rightarrow> 'v \<Rightarrow> bool"
    and rnb_move :: "'g \<Rightarrow> 'v \<Rightarrow> 'g"
    and rnb_reset :: "'g \<Rightarrow> 'v \<Rightarrow> 'g"
begin

definition better :: "('v \<Rightarrow> bool) \<Rightarrow> real \<times> 'v \<Rightarrow> real \<times> 'v \<Rightarrow> bool" where
  "better pref p q = (fst p < fst q \<or> (fst p = fst q \<and> pref (snd p) \<and> \<not> pref (snd q)))"

definition "best_upd key pref u b r =
  (case b of None \<Rightarrow> Some (key u r, r)
   | Some p \<Rightarrow> if better pref (key u r, r) p then Some (key u r, r) else b)"

partial_function (tailrec) scan_best ::
  "('v \<Rightarrow> 'v \<Rightarrow> real) \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> 'v \<Rightarrow> 'g \<Rightarrow> (real \<times> 'v) option \<Rightarrow>
   'g \<times> (real \<times> 'v) option" where
  "scan_best key pref u C b =
     (if rnb_has C u then scan_best key pref u (rnb_move C u) (best_upd key pref u b (rnb_current C u))
      else (C, b))"

definition "best_of key pref u C = scan_best key pref u (rnb_reset C u) None"

lemmas [code] = better_def best_upd_def scan_best.simps best_of_def

text \<open>@{term b} is a best neighbour among @{term S}.\<close>

definition "best_inv key pref u S b =
  (case b of None \<Rightarrow> S = {}
   | Some (x, j) \<Rightarrow> j \<in> S \<and> x = key u j \<and> (\<forall>r\<in>S. x \<le> key u r) \<and>
                    (\<forall>r\<in>S. key u r = x \<and> pref r \<longrightarrow> pref j))"

lemma best_upd_inv:
  "best_inv key pref u S b \<Longrightarrow> best_inv key pref u (insert r S) (best_upd key pref u b r)"
proof(cases b)
  case (Some p)
  moreover obtain y s where "p = (y, s)" by (cases p) auto
  ultimately show "best_inv key pref u S b \<Longrightarrow> ?thesis"
    by (cases "better pref (key u r, r) (y, s)")
       (auto simp: best_inv_def best_upd_def better_def)
qed (simp add: best_inv_def best_upd_def)

end

locale nb_best_scan = nb_best_scan_spec +
  rnb: indexed_iterable_set rnb_invar rnb_abstract rnb_current rnb_has rnb_iterated
      rnb_remaining rnb_move rnb_reset K
  for rnb_invar rnb_abstract rnb_iterated rnb_remaining K
begin

lemma scan_best_props:
  assumes "rnb_invar C" "u \<in> K" "finite (rnb_remaining C u)" "best_inv key pref u S b"
  shows "rnb_invar (fst (scan_best key pref u C b)) \<and>
         rnb_abstract (fst (scan_best key pref u C b)) = rnb_abstract C \<and>
         best_inv key pref u (S \<union> rnb_remaining C u) (snd (scan_best key pref u C b))"
  using assms
proof(induction "card (rnb_remaining C u)" arbitrary: C S b)
  case 0
  hence empty: "rnb_remaining C u = {}" by simp
  hence not_has: "\<not> rnb_has C u" using rnb.idx_has[OF 0(2,3)] by simp
  show ?case
    using 0(2,5) by (simp add: scan_best.simps[of key pref u C b] not_has empty)
next
  case (Suc n)
  hence ne: "rnb_remaining C u \<noteq> {}" by auto
  hence has: "rnb_has C u" using rnb.idx_has[OF Suc(3,4)] by simp
  define x where "x = rnb_current C u"
  define C' where "C' = rnb_move C u"
  have x_in: "x \<in> rnb_remaining C u" using rnb.idx_current[OF Suc(3,4) ne] by (simp add: x_def)
  have C': "rnb_invar C'" "rnb_remaining C' u = rnb_remaining C u - {x}"
           "rnb_abstract C' = rnb_abstract C"
    using rnb.idx_move_invar[OF Suc(3,4)] rnb.idx_move_remaining[OF Suc(3,4) ne]
          rnb.idx_move_abstract[OF Suc(3,4) ne]
    by (auto simp: C'_def x_def fun_eq_iff)
  have card: "n = card (rnb_remaining C' u)" using Suc(2,5) x_in by (simp add: C'(2))
  define b' where "b' = best_upd key pref u b x"
  have IH: "rnb_invar (fst (scan_best key pref u C' b')) \<and>
            rnb_abstract (fst (scan_best key pref u C' b')) = rnb_abstract C' \<and>
            best_inv key pref u (insert x S \<union> rnb_remaining C' u) (snd (scan_best key pref u C' b'))"
    using Suc(1)[OF card C'(1) Suc(4) _ best_upd_inv[OF Suc(6)]] Suc(5)
    by (simp add: C'(2) b'_def)
  have eq: "scan_best key pref u C b = scan_best key pref u C' b'"
    by (simp add: scan_best.simps[of key pref u C b] has C'_def x_def b'_def)
  have "insert x S \<union> rnb_remaining C' u = S \<union> rnb_remaining C u" using x_in by (auto simp: C'(2))
  thus ?case using IH by (simp add: eq C'(3))
qed

lemma best_of_props:
  assumes "rnb_invar C" "u \<in> K" "finite (rnb_abstract C u)"
  shows "rnb_invar (fst (best_of key pref u C))"
        "rnb_abstract (fst (best_of key pref u C)) = rnb_abstract C"
        "snd (best_of key pref u C) = None \<longleftrightarrow> rnb_abstract C u = {}"
        "snd (best_of key pref u C) = Some (x, j) \<Longrightarrow>
           j \<in> rnb_abstract C u \<and> x = key u j \<and> (\<forall>r\<in>rnb_abstract C u. x \<le> key u r) \<and>
           (\<forall>r\<in>rnb_abstract C u. key u r = x \<and> pref r \<longrightarrow> pref j)"
proof-
  have R: "rnb_invar (rnb_reset C u)" "rnb_remaining (rnb_reset C u) u = rnb_abstract C u"
          "rnb_abstract (rnb_reset C u) = rnb_abstract C"
    using rnb.idx_reset_invar[OF assms(1,2)] rnb.idx_reset_remaining[OF assms(1,2)]
          rnb.idx_reset_abstract[OF assms(1,2)] by (auto simp: fun_eq_iff)
  have P: "rnb_invar (fst (best_of key pref u C)) \<and>
           rnb_abstract (fst (best_of key pref u C)) = rnb_abstract C \<and>
           best_inv key pref u (rnb_abstract C u) (snd (best_of key pref u C))"
    using scan_best_props[OF R(1) assms(2), of key pref "{}" None] assms(3)
    by (simp add: R(2,3) best_of_def best_inv_def)
  thus "rnb_invar (fst (best_of key pref u C))"
       "rnb_abstract (fst (best_of key pref u C)) = rnb_abstract C"
    by simp+
  show "snd (best_of key pref u C) = None \<longleftrightarrow> rnb_abstract C u = {}"
    using P by (auto simp: best_inv_def split: option.splits)
  show "snd (best_of key pref u C) = Some (x, j) \<Longrightarrow>
           j \<in> rnb_abstract C u \<and> x = key u j \<and> (\<forall>r\<in>rnb_abstract C u. x \<le> key u r) \<and>
           (\<forall>r\<in>rnb_abstract C u. key u r = x \<and> pref r \<longrightarrow> pref j)"
    using P by (auto simp: best_inv_def)
qed

end

end

