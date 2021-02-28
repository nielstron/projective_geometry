theory Proj3_Projective
imports Proj3 Projective_Plane_Axioms
begin



lemma cross3_scalar_multiple: "cross3 x y = 0 \<longleftrightarrow> (scalar_multiple x y \<or> x = 0 \<or> y = 0)"
  unfolding scalar_multiple_def
  unfolding cross_eq_0 collinear_lemma
  by (metis homogz.abs_eq_iff scalar_multiple_def scale_zero_left)

lemma cross3_scalar_non0: "\<lbrakk>x \<noteq> 0; y \<noteq> 0\<rbrakk> \<Longrightarrow> cross3 x y = 0 \<longleftrightarrow> scalar_multiple x y"
  by (simp add: cross3_scalar_multiple)

find_theorems cross3 norm
find_theorems norm inner
find_theorems "_ = norm ?x * norm ?y"
find_theorems "norm _ *\<^sub>R _ = _"
find_theorems norm

lemma scalar_multiple_coll: "\<lbrakk>a \<noteq> 0; b \<noteq> 0\<rbrakk> \<Longrightarrow> (scalar_multiple a b) = (collinear {0, a, b})"
  by (metis (no_types, lifting) collinear_lemma insert_commute scalar_multiple_def scale_eq_0_iff)

lemma "\<lbrakk>a = c; b = d; a \<noteq> b\<rbrakk> \<Longrightarrow> join a b = join c d"
  by (simp add: join_def[of a b])

lemma "\<lbrakk>a \<noteq> 0; b \<noteq> 0\<rbrakk> \<Longrightarrow> (scalar_multiple a b) = (norm b *\<^sub>R a = norm a *\<^sub>R b)"
  unfolding scalar_multiple_coll
  unfolding sym[OF norm_cauchy_schwarz_eq] sym[OF norm_cauchy_schwarz_equal]
  apply auto
  oops

lemma "\<lbrakk>orthogonal a x; orthogonal a y\<rbrakk> \<Longrightarrow> scalar_multiple a (cross3 x y)"
  apply(auto simp add: orthogonal_def cross3_def scalar_multiple_def vec_eq_iff)
  oops

definition "homogz_axis k x \<equiv> homogz_of_vec (axis k x)"
definition "homog_axis k x \<equiv> homog_of_homogz (homogz_of_vec (axis k x))"

lemma homogz_axis_non_zero: "x \<noteq> 0 \<Longrightarrow> homogz_axis k x \<noteq> 0"
  by (metis axis_eq_0_iff homogz_axis_def incidz.abs_eq inner_eq_zero_iff zero_homogz_def)

lemma ex_cross3_non_zero:
  assumes "P \<noteq> 0" shows "\<exists>Q. cross3 P Q \<noteq> 0"
proof (cases "scalar_multiple P (axis 1 1)")
  case True
  then have "\<not> scalar_multiple P (axis 2 1)"
    by (smt (verit) cross3_scalar_non0 axis_eq_0_iff cross_basis(2) homogz.abs_eq_iff neg_equal_0_iff_equal)
  then have "cross3 P (axis 2 1) \<noteq> 0"
    by (simp add: cross3_scalar_multiple assms)
  then show ?thesis
    by blast
next
  case False
  then have "cross3 P (axis 1 1) \<noteq> 0"
    by (simp add: Proj3_Projective.cross3_scalar_non0 assms)
  then show ?thesis
    by blast
qed

lemma ex_incid: "\<exists>l. incid P l" "\<exists>P. incid P l"
proof -
  have f1: "incidz (homogz_of_vec 0) (homogz_of_vec 0)"
    by (simp add: incidz.abs_eq)
  obtain vv :: "(real, 3) vec \<Rightarrow> (real, 3) vec" where
    f2: "\<not> incidz (homogz_of_vec (cross3 1 (vv 1))) (homogz_of_vec (cross3 1 (vv 1)))"
    by (metis (no_types) ex_cross3_non_zero incidz.abs_eq inner_eq_zero_iff rel_simps(93))
  { assume "incidz 0 0"
    then have "0 \<noteq> homogz_of_vec 1"
      by (metis incidz.abs_eq inner_eq_zero_iff rel_simps(93))
    then have "incidz 0 0 \<longrightarrow> (\<exists>n. incid P n) \<or> (\<exists>n. P \<noteq> n) \<or> (\<exists>h. homogz_of_homog P \<noteq> h \<and> 0 \<noteq> h)"
      using f2 by (metis (full_types) incidz_meet(1) joinz.abs_eq) }
  then show "\<exists>l. incid P l"
    using f1 by (metis homogz_homog_eq incid_def incid_joinz(2))
  then show "\<exists>P. incid P l"
    by (metis incid_joinz(3))
qed

lemma ex4_indep_homogz: "\<exists>A B C D.
       A \<noteq> 0 \<and> B \<noteq> 0 \<and> C \<noteq> 0 \<and> D \<noteq> 0 \<and>
       A \<noteq> B \<and>
       A \<noteq> C \<and>
       A \<noteq> D \<and>
       B \<noteq> C \<and>
       B \<noteq> D \<and>
       C \<noteq> D \<and>
       (\<forall>l \<noteq> 0. (incidz A l \<and> incidz B l \<longrightarrow> \<not> incidz C l \<and> \<not> incidz D l) \<and>
            (incidz A l \<and> incidz C l \<longrightarrow> \<not> incidz B l \<and> \<not> incidz D l) \<and>
            (incidz A l \<and> incidz D l \<longrightarrow> \<not> incidz B l \<and> \<not> incidz C l) \<and>
            (incidz B l \<and> incidz C l \<longrightarrow> \<not> incidz A l \<and> \<not> incidz D l) \<and>
            (incidz B l \<and> incidz D l \<longrightarrow> \<not> incidz A l \<and> \<not> incidz C l) \<and>
            (incidz C l \<and> incidz D l \<longrightarrow> \<not> incidz A l \<and> \<not> incidz B l))"
  apply (transfer)
  apply (inst_existentials
      "vector [1,0,0] :: (real, 3) vec"
      "vector [0,1,0] :: (real, 3) vec"
      "vector [0,0,1] :: (real, 3) vec"
      "vector [1,1,1] :: (real, 3) vec")
            apply (auto simp add: scalar_multiple_def)
                      apply (metis rel_simps(93) vector_3 zero_index)
                      apply (metis rel_simps(93) vector_3 zero_index)
                     apply (metis rel_simps(93) vector_3 zero_index)
                    apply (metis rel_simps(93) vector_3 zero_index)
                   apply (smt (z3) vector_3 vector_scaleR_component)
                  apply (smt (z3) vector_3 vector_scaleR_component)
                 apply (smt (z3) vector_3 vector_scaleR_component)
                apply (smt (z3) vector_3 vector_scaleR_component)
               apply (smt (z3) vector_3 vector_scaleR_component)
              apply (smt (z3) vector_3 vector_scaleR_component)
             apply (smt (verit, del_insts) inner_eq_zero_iff inner_real_def inner_vec_def mult_eq_0_iff sum_3 vector_3)+
  done
(* TODO transfer more from projective to this definition for successful interpretation *)

interpretation projective_real_plane: projective_plane incid
proof(standard, goal_cases)
  case (1 P Q)
  then show ?case
  proof (cases "P = Q")
    case True
    then show ?thesis
      by (simp add: ex_incid)
  next
    case False
    then have "incid P (join P Q)" "incid Q (join P Q)"
      by (simp_all add: incid_joinz)
    then show ?thesis by blast
  qed
next
  case (2 l m)
  then show ?case
  proof (cases "l = m")
    case True
    then show ?thesis
      by (simp add: ex_incid)
  next
    case False
    then have "incid (nzmeet l m) l" "incid (nzmeet l m) m"
      by (simp_all add: incid_joinz)
    then show ?thesis by blast
  qed
next
  case (3 P l Q m)
  then show ?case
    apply (transfer)
    apply(auto simp add: scalar_multiple_def)
    sorry (* TODO ! *)
    find_theorems inner 0
    find_theorems orthogonal
    find_theorems collinear
next
  case 4
  then show ?case
    unfolding incid_def
  proof (goal_cases)
    case 1
    obtain A B C D where ABCD_indep: "
       A \<noteq> 0 \<and> B \<noteq> 0 \<and> C \<noteq> 0 \<and> D \<noteq> 0 \<and>
       A \<noteq> B \<and>
       A \<noteq> C \<and>
       A \<noteq> D \<and>
       B \<noteq> C \<and>
       B \<noteq> D \<and>
       C \<noteq> D \<and>
       (\<forall>l \<noteq> 0. (incidz A l \<and> incidz B l \<longrightarrow> \<not> incidz C l \<and> \<not> incidz D l) \<and>
            (incidz A l \<and> incidz C l \<longrightarrow> \<not> incidz B l \<and> \<not> incidz D l) \<and>
            (incidz A l \<and> incidz D l \<longrightarrow> \<not> incidz B l \<and> \<not> incidz C l) \<and>
            (incidz B l \<and> incidz C l \<longrightarrow> \<not> incidz A l \<and> \<not> incidz D l) \<and>
            (incidz B l \<and> incidz D l \<longrightarrow> \<not> incidz A l \<and> \<not> incidz C l) \<and>
            (incidz C l \<and> incidz D l \<longrightarrow> \<not> incidz A l \<and> \<not> incidz B l))"
      using ex4_indep_homogz by presburger
    show ?case
      apply(inst_existentials "homog_of_homogz A" "homog_of_homogz B" "homog_of_homogz C" "homog_of_homogz D")
      by (metis ABCD_indep homog_non_zero(1) homogz_homog_eq)+
  qed
qed

end