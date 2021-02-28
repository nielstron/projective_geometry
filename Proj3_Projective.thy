theory Proj3_Projective
imports Projective_Geometry Projective_Plane_Axioms
begin



lemma cross3_scalar_multiple: "cross3 x y = 0 \<longleftrightarrow> (scalar_multiple x y \<or> x = 0 \<or> y = 0)"
  unfolding scalar_multiple_def
  unfolding cross_eq_0 collinear_lemma
  by (metis homog.abs_eq_iff scalar_multiple_def scale_zero_left)

lemma cross3_scalar_non0: "\<lbrakk>x \<noteq> 0; y \<noteq> 0\<rbrakk> \<Longrightarrow> cross3 x y = 0 \<longleftrightarrow> scalar_multiple x y"
  by (simp add: cross3_scalar_multiple)

find_theorems cross3 norm
find_theorems norm inner
find_theorems "_ = norm ?x * norm ?y"
find_theorems "norm _ *\<^sub>R _ = _"
find_theorems norm

lemma scalar_multiple_coll: "\<lbrakk>a \<noteq> 0; b \<noteq> 0\<rbrakk> \<Longrightarrow> (scalar_multiple a b) = (collinear {0, a, b})"
  by (metis (no_types, lifting) collinear_lemma insert_commute scalar_multiple_def scale_eq_0_iff)

lemma "\<lbrakk>a \<noteq> 0; b \<noteq> 0\<rbrakk> \<Longrightarrow> (scalar_multiple a b) = (norm b *\<^sub>R a = norm a *\<^sub>R b)"
  unfolding scalar_multiple_coll
  unfolding sym[OF norm_cauchy_schwarz_eq] sym[OF norm_cauchy_schwarz_equal]
  apply auto
  oops

lemma "\<lbrakk>orthogonal a x; orthogonal a y\<rbrakk> \<Longrightarrow> scalar_multiple a (cross3 x y)"
  apply(auto simp add: orthogonal_def cross3_def scalar_multiple_def vec_eq_iff)
  oops

definition "homog_axis k x \<equiv> homog_of_vec (axis k x)"
definition "nzhomog_axis k x \<equiv> nzhomog_of_homog (homog_of_vec (axis k x))"

lemma homog_axis_non_zero: "x \<noteq> 0 \<Longrightarrow> homog_axis k x \<noteq> 0"
  by (metis axis_eq_0_iff homog_axis_def incid.abs_eq inner_eq_zero_iff zero_homog_def)

lemma ex_cross3_non_zero:
  assumes "P \<noteq> 0" shows "\<exists>Q. cross3 P Q \<noteq> 0"
proof (cases "scalar_multiple P (axis 1 1)")
  case True
  then have "\<not> scalar_multiple P (axis 2 1)"
    by (smt (verit) Projective_Geometry.cross3_scalar_non0 axis_eq_0_iff cross_basis(2) homog.abs_eq_iff neg_equal_0_iff_equal)
  then have "cross3 P (axis 2 1) \<noteq> 0"
    by (simp add: cross3_scalar_multiple assms)
  then show ?thesis
    by blast
next
  case False
  then have "cross3 P (axis 1 1) \<noteq> 0"
    by (simp add: Projective_Geometry.cross3_scalar_non0 assms)
  then show ?thesis
    by blast
qed

lemma ex_nzincid: "\<exists>l. nzincid P l" "\<exists>P. nzincid P l"
proof -
  have f1: "incid (homog_of_vec 0) (homog_of_vec 0)"
    by (simp add: incid.abs_eq)
  obtain vv :: "(real, 3) vec \<Rightarrow> (real, 3) vec" where
    f2: "\<not> incid (homog_of_vec (cross3 1 (vv 1))) (homog_of_vec (cross3 1 (vv 1)))"
    by (metis (no_types) ex_cross3_non_zero incid.abs_eq inner_eq_zero_iff rel_simps(93))
  { assume "incid 0 0"
    then have "0 \<noteq> homog_of_vec 1"
      by (metis incid.abs_eq inner_eq_zero_iff rel_simps(93))
    then have "incid 0 0 \<longrightarrow> (\<exists>n. nzincid P n) \<or> (\<exists>n. P \<noteq> n) \<or> (\<exists>h. homog_of_nzhomog P \<noteq> h \<and> 0 \<noteq> h)"
      using f2 by (metis (full_types) incid_meet(1) join.abs_eq) }
  then show "\<exists>l. nzincid P l"
    using f1 by (metis homog_nzhomog_eq nzincid_def nzincid_join(2))
  then show "\<exists>P. nzincid P l"
    by (metis nzincid_join(3))
qed

interpretation projective_real_plane: projective_plane nzincid
proof(standard, goal_cases)
  case (1 P Q)
  then show ?case
  proof (cases "P = Q")
    case True
    then show ?thesis
      by (simp add: ex_nzincid)
  next
    case False
    then have "nzincid P (nzjoin P Q)" "nzincid Q (nzjoin P Q)"
      by (simp_all add: nzincid_join)
    then show ?thesis by blast
  qed
next
  case (2 l m)
  then show ?case
  proof (cases "l = m")
    case True
    then show ?thesis
      by (simp add: ex_nzincid)
  next
    case False
    then have "nzincid (nzmeet l m) l" "nzincid (nzmeet l m) m"
      by (simp_all add: nzincid_join)
    then show ?thesis by blast
  qed
next
  case (3 P l Q m)
  then show ?case
    apply (transfer)
    apply(auto simp add: scalar_multiple_def)
    find_theorems inner 0
    find_theorems orthogonal
    find_theorems collinear
    
  qed
next
  case 4
  then show ?case
    apply(transfer)
    apply (inst_existentials
        "vector [1,0,0] :: (real, 3) vec"
        "vector [0,1,0] :: (real, 3) vec"
        "vector [0,0,1] :: (real, 3) vec"
        "vector [1,1,1] :: (real, 3) vec")
          apply (auto simp add: scalar_multiple_def)
                     apply (smt (z3) vector_3 vector_scaleR_component)
                    apply (smt (z3) vector_3 vector_scaleR_component)
                   apply (smt (z3) vector_3 vector_scaleR_component)
                  apply (smt (z3) vector_3 vector_scaleR_component)
                 apply (smt (z3) vector_3 vector_scaleR_component)
                apply (smt (z3) vector_3 vector_scaleR_component)
               apply (smt (z3) cross3_def cross_zero_right inner_real_def inner_vec_def mult_eq_0_iff norm_and_cross_eq_0 sum_3 vector_3(1) vector_3(2) vector_3(3))
              apply (smt (z3) cross3_def cross_zero_right inner_real_def inner_vec_def mult_eq_0_iff norm_and_cross_eq_0 sum_3 vector_3(1) vector_3(2) vector_3(3))
             apply (smt (z3) cross3_def cross_zero_right inner_real_def inner_vec_def mult_eq_0_iff norm_and_cross_eq_0 sum_3 vector_3(1) vector_3(2) vector_3(3))
            apply (smt (z3) cross3_def cross_zero_right inner_real_def inner_vec_def mult_eq_0_iff norm_and_cross_eq_0 sum_3 vector_3(1) vector_3(2) vector_3(3))
           apply (smt (z3) cross3_def cross_zero_right inner_real_def inner_vec_def mult_eq_0_iff norm_and_cross_eq_0 sum_3 vector_3(1) vector_3(2) vector_3(3))
          apply (smt (z3) cross3_def cross_zero_right inner_real_def inner_vec_def mult_eq_0_iff norm_and_cross_eq_0 sum_3 vector_3(1) vector_3(2) vector_3(3))
         apply (smt (z3) cross3_def cross_zero_right inner_real_def inner_vec_def mult_eq_0_iff norm_and_cross_eq_0 sum_3 vector_3(1) vector_3(2) vector_3(3))
        apply (smt (z3) cross3_def cross_zero_right inner_real_def inner_vec_def mult_eq_0_iff norm_and_cross_eq_0 sum_3 vector_3(1) vector_3(2) vector_3(3))
       apply (smt (z3) cross3_def cross_zero_right inner_real_def inner_vec_def mult_eq_0_iff norm_and_cross_eq_0 sum_3 vector_3(1) vector_3(2) vector_3(3))
      apply (smt (z3) cross3_def cross_zero_right inner_real_def inner_vec_def mult_eq_0_iff norm_and_cross_eq_0 sum_3 vector_3(1) vector_3(2) vector_3(3))
     apply (smt (z3) cross3_def cross_zero_right inner_real_def inner_vec_def mult_eq_0_iff norm_and_cross_eq_0 sum_3 vector_3(1) vector_3(2) vector_3(3))
    apply (smt (z3) cross3_def cross_zero_right inner_real_def inner_vec_def mult_eq_0_iff norm_and_cross_eq_0 sum_3 vector_3(1) vector_3(2) vector_3(3))
    done
qed

end