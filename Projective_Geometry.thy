theory Projective_Geometry
imports "HOL-Analysis.Cross3"
begin                           

text "Some basic setup to pretty print calculation results."

fun of_vector3 :: "('a, 3) vec \<Rightarrow> 'a list" where 
 "of_vector3 a = [a$1, a$2, a$3]"

definition [code_unfold]: "example \<equiv> vector [1,2,3]::real^3"
definition "example2 \<equiv> vec_lambda (\<lambda>x. if x \<in> {1,2,3} then 1 else 0)::real^3"
lemma [code_unfold]: "example2 = vector [1, 1, 1]"
  unfolding vector_def example2_def by auto

declare vec_lambda_beta[code_unfold]

lemma [code_unfold]:
  "\<lbrakk>a = vector [a1,a2,a3]; b = (vector [b1,b2,b3])\<rbrakk> \<Longrightarrow>
    cross3 a b = 
            vector [a2 * b3 - a3 * b2,
            a3 * b1 - a1 * b3,
            a1 * b2 - a2 * b1]"
  unfolding cross3_def vector_def
  by auto

declare vector_3[code_unfold]
lemma [code_unfold]: "\<lbrakk>a = vector [a1, a2, a3] \<rbrakk> \<Longrightarrow> of_vector3 a = [a1,a2,a3]"
  by auto

value "vector [1::real,2,3] $ (2::3)"
value "of_vector3 (cross3 example example2)"

text "The quotient type"

definition scalar_multiple:: "(real,3) vec \<Rightarrow> (real,3) vec \<Rightarrow> bool" where
  "scalar_multiple u v \<equiv> \<exists>c::real. c \<noteq> 0 \<and> u = c *\<^sub>R v"

quotient_type homog = "(real,3) vec" / scalar_multiple
  apply(rule equivpI)
    apply (auto simp add: reflp_def symp_def transp_def scalar_multiple_def)
   apply (metis divide_inverse_commute divide_self_if inverse_eq_divide scaleR_one zero_eq_1_divide_iff)
  by (metis mult_eq_0_iff)

instantiation homog :: zero begin

lift_definition zero_homog :: homog is 0 .

instance ..

end

lift_definition incid :: "homog \<Rightarrow> homog \<Rightarrow> bool" is "\<lambda>u v. inner u v = 0"
  unfolding scalar_multiple_def
  by auto

lift_definition join :: "homog \<Rightarrow> homog \<Rightarrow> homog" is cross3
  unfolding scalar_multiple_def
proof (safe, standard, goal_cases)
  case (1 vec1 vec2 vec3 vec4 a b)
  then show "a * b \<noteq> 0 \<and>cross3 (a *\<^sub>R vec2) (b *\<^sub>R vec4) = (a*b) *\<^sub>R cross3 vec2 vec4"
    by (simp add: cross_mult_left cross_mult_right)
qed

definition "meet = join"

lemma incid_meet:
  "incid p (join p q)"
  "incid p (join q p)"
  by (transfer; simp add: dot_cross_self)+

term det

definition mat_of_vec3 :: "(real,3) vec \<Rightarrow> (real,3) vec \<Rightarrow> (real,3) vec \<Rightarrow> ((real,3) vec, 3) vec" where
  "mat_of_vec3 a b c = vector [a,b,c]"

definition mat_scalar_multiple:: "((real,3) vec, 3) vec \<Rightarrow> ((real,3) vec, 3) vec \<Rightarrow> bool" where
  "mat_scalar_multiple u v \<equiv> \<exists>c d e::real. c \<noteq> 0 \<and> d \<noteq> 0 \<and> e \<noteq> 0 \<and> u$1 = c *\<^sub>R v$1 \<and> u$2 = d *\<^sub>R v$2 \<and> u$3 = e *\<^sub>R v$3"

quotient_type mat_homog = "((real,3) vec, 3) vec" / mat_scalar_multiple
  apply(rule equivpI)
    apply (auto simp add: reflp_def symp_def transp_def mat_scalar_multiple_def)
    apply fastforce
   apply (metis divide_inverse_commute divide_self_if inverse_eq_divide scaleR_one zero_eq_1_divide_iff)
  by (metis mult_eq_0_iff)

lift_definition mat_of_homog :: "homog \<Rightarrow> homog \<Rightarrow> homog \<Rightarrow> mat_homog" is mat_of_vec3
  unfolding mat_of_vec3_def scalar_multiple_def mat_scalar_multiple_def
  by auto

instantiation mat_homog :: zero begin

lift_definition zero_mat_homog :: mat_homog is 0 .

instance ..

end

quotient_type real_homog = real / "\<lambda>x y. \<exists>c. x = c * y \<and> c \<noteq> 0"
  apply(rule equivpI)
    apply (auto simp add: reflp_def symp_def transp_def)
  by (metis divide_inverse_commute divide_self_if inverse_eq_divide zero_eq_1_divide_iff)

find_theorems det


text "It turns out (due to irrelevance of scalar multiples) 
we only care about whether the determinant of the representatives
is zero or not. We express this by identity with respect to scalar
multiples in the one dimensional case."

lift_definition det_homog :: "mat_homog \<Rightarrow> real_homog" is det
  unfolding mat_scalar_multiple_def
proof (safe; goal_cases)
  case (1 vec1 vec2 c d e)
  let ?c = "(((\<lambda>_. 0)(1 := c))(2 := d))(3 := e)  :: 3 \<Rightarrow> real"
  from 1 have "vec1 = (\<chi> i. ?c i *s (vec2 $ i))"
    apply (auto simp add: vec_eq_iff)
    by (metis exhaust_3)
  thm det_rows_mul
  then have "det vec1 = prod ?c UNIV * det vec2"
    by (simp add: det_rows_mul)
  moreover have "prod ?c UNIV \<noteq> 0"
    using 1 apply(auto)
    by (metis exhaust_3)
  ultimately show ?case
    by blast
qed

instantiation real_homog :: zero begin

lift_definition zero_real_homog :: real_homog is 0 .

instance ..

end

lemma inner_real_vec_def: "inner (p:: (real, 'a::finite) vec) q = (\<Sum>j\<in>UNIV. p $ j * q $ j)"
  by (metis (mono_tags, lifting) inner_real_def inner_vec_def sum.cong)


lemma vector_mul_is_scalar: "(vector [p, q, r::((real, 3) vec)]::(_,3) vec) *v l = vector [inner p l, inner q l, inner r l]"
  apply (auto simp add: matrix_vector_mult_def inner_real_vec_def vec_eq_iff)
  apply(subst UNIV_3)+
  apply simp
  subgoal for i
    apply(cases i)
    apply (auto)
    by (smt (z3) exhaust_3 vector_3)
  done
  


lemma incidence_det_0: 
  "(\<exists>l. l \<noteq> 0 \<and> incid p l \<and> incid q l \<and> incid r l) \<Longrightarrow> det_homog (mat_of_homog p q r) = 0"
  apply transfer
  apply safe
   apply (auto simp add: incid_def mat_of_vec3_def scalar_multiple_def)
proof (goal_cases)
  case (1 p q r l)
  thm dot_cross_det
  find_theorems cross3
  find_theorems dependent
  find_theorems "vec.dependent"
  then have "vector [p, q, r] *v l = (vector [inner p l, inner q l, inner r l]::(_,3) vec)"
    by (simp add: vector_mul_is_scalar)
  also have "\<dots> = 0"
    using 1
    by (metis inner_zero_right vec.zero vector_mul_is_scalar)
  finally have "(vector [p, q, r]::(_,3) vec) *v l = 0" .
  then show ?case
    by (metis (no_types, lifting) 1 cross_matrix_mult cross_zero_right dot_cross_det norm_and_cross_eq_0 scale_eq_0_iff vec.zero)
qed
end