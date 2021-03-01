theory Proj3
imports "HOL-Analysis.Cross3" "Instantiate_Existentials" "Tarskis_Geometry.Linear_Algebra2"
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


definition scalar_multiple:: "(real,'b::finite) vec \<Rightarrow> (real,'b::finite) vec \<Rightarrow> bool" where
  "scalar_multiple u v \<equiv> \<exists>c::real. c \<noteq> 0 \<and> u = c *\<^sub>R v"

definition parallel:: "(real,'b::finite) vec \<Rightarrow> (real,'b) vec \<Rightarrow> bool" where
  "parallel \<equiv> scalar_multiple"

definition "non_zero = {x. x \<noteq> 0}"

(*
typedef (overloaded) ('a::zero_neq_one, 'b::finite) nzvec = "non_zero :: (('a, 'b) vec) set"
  morphisms vec_of nzvec_of
proof
  show "(\<chi> i::'b. (1::'a)) \<in> non_zero"
    by (metis mem_Collect_eq non_zero_def one_index one_vec_def zero_index zero_neq_one)
qed

declare [[coercion vec_of]] *)

quotient_type homogz = "(real,3) vec" / scalar_multiple
  morphisms vec_of_homogz homogz_of_vec
  apply(rule equivpI)
    apply (auto simp add: reflp_def symp_def transp_def scalar_multiple_def)
   apply (metis divide_inverse_commute divide_self_if inverse_eq_divide scaleR_one zero_eq_1_divide_iff)
  by (metis mult_eq_0_iff)

declare [[coercion vec_of_homogz]]

instantiation homogz :: zero
begin

lift_definition zero_homogz :: homogz is "(0 :: (real,3) vec)" .

instance ..
end

lift_definition one_homogz :: homogz is "(\<chi> i. 1)" .

lemma homogz_mult_eq_abs:
  assumes "c \<noteq> 0"
  shows  "homogz_of_vec (c *\<^sub>R v) = homogz_of_vec v"
  by (meson Quotient3_homogz Quotient3_rel assms scalar_multiple_def)

lemma homogz_mult_eq:
  assumes "c \<noteq> 0"
  shows  "homogz_of_vec (c *\<^sub>R vec_of_homogz v) = v"
  by (metis Quotient3_abs_rep Quotient3_homogz assms homogz_mult_eq_abs)


typedef homog = "non_zero :: homogz set"
  morphisms homogz_of_homog homog_of_homogz
proof
  show "one_homogz \<in> non_zero"
    by (smt (verit, del_insts) Quotient3_homogz Quotient3_rel mem_Collect_eq non_zero_def one_homogz_def one_vec_def scalar_multiple_def scale_eq_0_iff zero_homogz_def zero_neq_one)
qed

abbreviation "homog_of_vec \<equiv> (\<lambda>x. homog_of_homogz (homogz_of_vec x))"
abbreviation "vec_of_homog \<equiv> (\<lambda>x. vec_of_homogz (homogz_of_homog x))"

lemma homog_mult_eq_abs:
  assumes "c \<noteq> 0"
  shows  "homog_of_vec (c *\<^sub>R v) = homog_of_vec v"
  by (simp add: assms homogz_mult_eq_abs)

lemma homog_mult_eq:
  assumes "c \<noteq> 0"
  shows  "homog_of_vec (c *\<^sub>R  vec_of_homog v) = v"
  by (simp add: assms homogz_mult_eq homogz_of_homog_inverse)


lemma homog_non_zero:
  "homogz_of_homog v \<noteq> 0"
  "vec_of_homog v \<noteq> 0"
  by (metis (full_types) Quotient3_abs_rep Quotient3_homogz homogz_of_homog mem_Collect_eq non_zero_def zero_homogz.abs_eq)+

declare [[coercion homogz_of_homog]]


lift_definition incidz :: "homogz \<Rightarrow> homogz \<Rightarrow> bool" is "\<lambda>u v. inner u v = 0"
  unfolding scalar_multiple_def
  by auto

definition incid :: "homog \<Rightarrow> homog \<Rightarrow> bool" where "incid = incidz"

lemma incidz_commute: "incidz p l = incidz l p"
  by (simp add: incidz.rep_eq inner_commute)+

lemma incid_commute: "incid p l = incid l p"
  by (simp add: incid_def incidz_commute)+

lift_definition joinz :: "homogz \<Rightarrow> homogz \<Rightarrow> homogz" is "\<lambda>u v.
   cross3 u v"
  unfolding scalar_multiple_def
proof (safe, goal_cases)
  case (1 v1 v2 v3 v4 a b)
  then show ?case
    apply(inst_existentials "a*b")
    by (auto simp add: cross_mult_left cross_mult_right)
qed

definition join :: "homog \<Rightarrow> homog \<Rightarrow> homog" where
  "u \<noteq> v \<Longrightarrow> join u v = homog_of_homogz (joinz u v)"


definition [simp]: "meetz \<equiv> joinz"

definition [simp]: "meet \<equiv> join"

lemma joinz_commute: "joinz p q = joinz q p"
  apply(transfer)
proof -
  fix p q
  have "cross3 p q = - cross3 q p"
    using cross_skew by blast
  moreover have "(-1::real) \<noteq> 0"
    by simp
  ultimately show "scalar_multiple (cross3 p q) (cross3 q p)"
    unfolding scalar_multiple_def
    by (metis scaleR_minus1_left)
qed

lemma join_commute: "join p q = join q p"
  by (metis join_def joinz_commute)

lemma incidz_joinz:
  "incidz p (joinz p q)"
  "incidz q (joinz p q)"
  by (transfer; simp add: dot_cross_self)+

lemma incidz_meetz:
  "incidz (joinz p q) p"
  "incidz (joinz p q) q"
  by (simp_all add: incidz_commute incidz_joinz)

lemma homogz_homog_eq: "p \<noteq> 0 \<Longrightarrow> homogz_of_homog (homog_of_homogz p) = p"
  by (simp add: non_zero_def homog_of_homogz_inverse)


lemma cross3_scalar_multiple: "cross3 x y = 0 \<longleftrightarrow> (scalar_multiple x y \<or> x = 0 \<or> y = 0)"
  unfolding scalar_multiple_def
  unfolding cross_eq_0 collinear_lemma
  by (metis homogz.abs_eq_iff scalar_multiple_def scale_zero_left)

lemma cross3_scalar_non0: "\<lbrakk>x \<noteq> 0; y \<noteq> 0\<rbrakk> \<Longrightarrow> cross3 x y = 0 \<longleftrightarrow> scalar_multiple x y"
  by (simp add: cross3_scalar_multiple)


lemma scalar_multiple_coll: "\<lbrakk>a \<noteq> 0; b \<noteq> 0\<rbrakk> \<Longrightarrow> (scalar_multiple a b) = (collinear {0, a, b})"
  by (metis (no_types, lifting) collinear_lemma insert_commute scalar_multiple_def scale_eq_0_iff)


lemma incid_joinz:
  assumes "p \<noteq> q"
  shows "incid p (join p q)"
  and "incid q (join p q)"
proof -
  from assms have "cross3 p q \<noteq> 0"
    by (metis (full_types) Quotient3_abs_rep Quotient3_homogz Quotient3_rel_rep cross3_scalar_multiple homogz_of_homog homogz_of_homog_inject mem_Collect_eq non_zero_def zero_homogz.abs_eq)
  then have "joinz p q \<noteq> 0"
    by (smt (verit, del_insts) Quotient3_abs_rep Quotient3_homogz incidz.abs_eq incidz.transfer inner_eq_zero_iff joinz.abs_eq rel_fun_def zero_homogz.transfer)
  moreover have "join p q = homog_of_homogz (joinz p q)"
    by (simp add: \<open>p \<noteq> q\<close> homogz_of_homog_inverse join_def)
  ultimately show
    "incid p (join p q)"
    "incid q (join p q)"
    by (simp_all add: homogz_of_homog_inverse incid_def homogz_homog_eq incidz_joinz incidz_meetz)
qed

definition mat_of_vec3 :: "(real,3) vec \<Rightarrow> (real,3) vec \<Rightarrow> (real,3) vec \<Rightarrow> ((real,3) vec, 3) vec" where
  "mat_of_vec3 a b c = vector [a,b,c]"

definition mat_scalar_multiple:: "((real,3) vec, 3) vec \<Rightarrow> ((real,3) vec, 3) vec \<Rightarrow> bool" where
  "mat_scalar_multiple u v \<equiv> \<exists>c d e::real. c \<noteq> 0 \<and> d \<noteq> 0 \<and> e \<noteq> 0 \<and> u$1 = c *\<^sub>R v$1 \<and> u$2 = d *\<^sub>R v$2 \<and> u$3 = e *\<^sub>R v$3"

quotient_type mat_homogz = "((real,3) vec, 3) vec" / mat_scalar_multiple
  apply(rule equivpI)
    apply (auto simp add: reflp_def symp_def transp_def mat_scalar_multiple_def)
    apply fastforce
   apply (metis divide_inverse_commute divide_self_if inverse_eq_divide scaleR_one zero_eq_1_divide_iff)
  by (metis mult_eq_0_iff)

lift_definition mat_of_homogz :: "homogz \<Rightarrow> homogz \<Rightarrow> homogz \<Rightarrow> mat_homogz" is mat_of_vec3
  unfolding mat_of_vec3_def scalar_multiple_def mat_scalar_multiple_def
  by auto

instantiation mat_homogz :: zero begin

lift_definition zero_mat_homogz :: mat_homogz is 0 .

instance ..

end


definition mat_of_homog :: "homog \<Rightarrow> homog \<Rightarrow> homog \<Rightarrow> mat_homogz" 
  where "mat_of_homog \<equiv> mat_of_homogz"

quotient_type real_homogz = real / "\<lambda>x y. \<exists>c. x = c * y \<and> c \<noteq> 0"
  apply(rule equivpI)
    apply (auto simp add: reflp_def symp_def transp_def)
  by (metis divide_inverse_commute divide_self_if inverse_eq_divide zero_eq_1_divide_iff)

find_theorems det


text "It turns out (due to irrelevance of scalar multiples) 
we only care about whether the determinant of the representatives
is zero or not. We express this by identity with respect to scalar
multiples in the one dimensional case."

lift_definition det_homogz :: "mat_homogz \<Rightarrow> real_homogz" is det
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

definition "det_homog \<equiv> det_homogz"

instantiation real_homogz :: zero begin

lift_definition zero_real_homogz :: real_homogz is 0 .

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
  
definition colz where "colz p q r = (\<exists>l. l \<noteq> 0 \<and> incidz p l \<and> incidz q l \<and> incidz r l)"

definition col where "col p q r = (\<exists>l. incid p l \<and> incid q l \<and> incid r l)"


lemma colz_det_0: 
  "colz p q r \<Longrightarrow> det_homogz (mat_of_homogz p q r) = 0"
  unfolding colz_def
  apply transfer
  apply safe
   apply (auto simp add: incidz_def mat_of_vec3_def scalar_multiple_def)
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
(* TODO other direction *)
(* TODO transfer to homog *)

lemma col_det_0: 
  "col p q r \<Longrightarrow> det_homog (mat_of_homog p q r) = 0"
  by (metis (mono_tags, hide_lams) col_def colz_def det_homog_def homog_non_zero(1) incid_def colz_det_0 mat_of_homog_def)


(* Taken from Tarski_Geometry *)

lemma dependent_proj2_abs:
  assumes "p \<noteq> 0" and "q \<noteq> 0" and "i \<noteq> 0 \<or> j \<noteq> 0" and "i *\<^sub>R p + j *\<^sub>R q = 0"
  shows "homogz_of_vec p = homogz_of_vec q" "homog_of_vec p = homog_of_vec q"
proof -
  have "i \<noteq> 0"
  proof
    assume "i = 0"
    with \<open>i \<noteq> 0 \<or> j \<noteq> 0\<close> have "j \<noteq> 0" by simp
    with \<open>i *\<^sub>R p + j *\<^sub>R q = 0\<close> and \<open>q \<noteq> 0\<close> have "i *\<^sub>R p \<noteq> 0" by auto
    with \<open>i = 0\<close> show False by simp
  qed
  with \<open>p \<noteq> 0\<close> and \<open>i *\<^sub>R p + j *\<^sub>R q = 0\<close> have "j \<noteq> 0" by auto

  from \<open>i \<noteq> 0\<close>
  have "homogz_of_vec p = homogz_of_vec (i *\<^sub>R p)"
    by (simp add: homogz_mult_eq_abs)
  also from \<open>i *\<^sub>R p + j *\<^sub>R q = 0\<close> and homogz_mult_eq_abs [of "-1" "j *\<^sub>R q"]
  have "\<dots> = homogz_of_vec (j *\<^sub>R q)" by (simp add: algebra_simps [symmetric])
  also from \<open>j \<noteq> 0\<close> have "\<dots> = homogz_of_vec q" by (rule homogz_mult_eq_abs)
  finally show "homogz_of_vec p = homogz_of_vec q" .
  then show "homog_of_vec p = homog_of_vec q"
    by simp
qed

lemma proj2_rep_dependent:
  assumes "i *\<^sub>R vec_of_homog v + j *\<^sub>R vec_of_homog w = 0"
  (is "i *\<^sub>R ?p + j *\<^sub>R ?q = 0")
  and "i \<noteq> 0 \<or> j \<noteq> 0"
  shows "v = w"
proof -
  have "?p \<noteq> 0" and "?q \<noteq> 0" by (rule homog_non_zero)+
  with \<open>i \<noteq> 0 \<or> j \<noteq> 0\<close> and \<open>i *\<^sub>R ?p + j *\<^sub>R ?q = 0\<close>
  have "homog_of_vec ?p = homog_of_vec ?q" by (simp add: dependent_proj2_abs)
  thus "v = w"
    by (metis Quotient3_abs_rep Quotient3_homogz \<open>vec_of_homog v \<noteq> 0\<close> \<open>vec_of_homog w \<noteq> 0\<close> assms(1) assms(2) dependent_proj2_abs(1) homogz_of_homog_inject)
qed

lemma proj2_rep_independent:
  assumes "p \<noteq> q"
  shows "independent {vec_of_homog p, vec_of_homog q}"
proof
  let ?p' = "vec_of_homog p"
  let ?q' = "vec_of_homog q"
  let ?S = "{?p', ?q'}"
  assume "dependent ?S"
  from  \<open>p \<noteq> q\<close> have "?p' \<noteq> ?q'"
    using \<open>dependent ?S\<close> homog_non_zero(2) by fastforce
  with dependent_explicit_2 [of ?p' ?q'] and \<open>dependent ?S\<close>
  obtain i and j where "i *\<^sub>R ?p' + j *\<^sub>R ?q' = 0" and "i \<noteq> 0 \<or> j \<noteq> 0"
    by (simp add: scalar_equiv) auto
  with proj2_rep_dependent have "p = q" by simp
  with \<open>p \<noteq> q\<close> show False ..
qed

lemma colz_permute:
  assumes "colz a b c"
  shows "colz a c b"
  and "colz b a c"
  using assms colz_def by auto

lemma colz_coincide:
  shows "colz a a c"
  unfolding colz_def
  apply(transfer)
  by (metis (no_types, hide_lams) scalar_multiple_def add.inverse_inverse axis_eq_0_iff cross_basis(2) cross_skew cross_triple dot_cross_self(1) dot_cross_self(2) inner_commute inner_zero_left pth_4(2) zero_neq_one)



lemma col_permute:
  assumes "col a b c"
  shows "col a c b"
  and "col b a c"
  using assms col_def by auto

lemma col_coincide:
  shows "col a a c"
  unfolding col_def incid_def
  by (metis colz_coincide colz_def homogz_homog_eq)


lemma colz_det_0: 
  "det_homogz (mat_of_homogz p q r) = 0 \<Longrightarrow> colz p q r"
  unfolding colz_def
  apply transfer
  apply safe
proof(goal_cases)
  case (1 p q r c)
  then have "det (mat_of_vec3 p q r) = 0"
    by simp
  then have "dependent {p, q, r}"
    oops


lemma proj2_points_define_linez:
  shows "\<exists>l\<noteq>0. incidz p l \<and> incidz q l"
proof -
  let ?p' = "vec_of_homogz p"
  let ?q' = "vec_of_homogz q"
  let ?B = "{?p', ?q'}"
  from card_suc_ge_insert [of ?p' "{?q'}"] have "card ?B \<le> 2" by simp
  with dim_le_card' [of ?B] have "dim ?B < 3" by simp
  with lowdim_subset_hyperplane [of ?B]
  obtain l' where "l' \<noteq> 0" and "span ?B \<subseteq> {x. l' \<bullet> x = 0}" by auto
  let ?l = "homogz_of_vec l'"
  let ?l'' = "vec_of_homogz ?l"
  from  \<open>l' \<noteq> 0\<close>
  obtain k where "?l'' = k *\<^sub>R l'"
    using homogz.abs_eq_iff homogz_mult_eq scalar_multiple_def by fastforce

  have "?p' \<in> ?B" and "?q' \<in> ?B" by simp_all
  with span_superset [of ?B] and \<open>span ?B \<subseteq> {x. l' \<bullet> x = 0}\<close>
  have "l' \<bullet> ?p' = 0" and "l' \<bullet> ?q' = 0" by auto
  hence "?p' \<bullet> l' = 0" and "?q' \<bullet> l' = 0" by (simp_all add: inner_commute)
  with dot_scaleR_mult(2) [of _ k l'] and \<open>?l'' = k *\<^sub>R l'\<close>
  have "incidz p ?l \<and> incidz q ?l"
    unfolding incidz_def
    by simp
  moreover have "homogz_of_vec l' \<noteq> 0"
    by (simp add: \<open>l' \<noteq> 0\<close> homogz.abs_eq_iff scalar_multiple_def zero_homogz_def)
  ultimately show "\<exists> l. l \<noteq> 0 \<and> incidz p l \<and> incidz q l"
    by blast
qed

lemma proj2_points_define_line:
  shows "\<exists> l. incid p l \<and> incid q l"
  unfolding incid_def
  using proj2_points_define_linez homog_non_zero homogz_homog_eq
  by metis

definition line_through :: "homog \<Rightarrow> homog \<Rightarrow> homog" where
  "line_through p q \<equiv> \<some> l. incid p l \<and> incid q l"

lemma line_through_incident:
  shows "incid p (line_through p q)"
  and "incid q (line_through p q)"
  unfolding line_through_def
  using proj2_points_define_line
    and someI_ex [of "\<lambda> l. incid p l \<and> incid q l"]
  by simp_all

lemma line_through_unique:
  assumes "p \<noteq> q" and "incid p l" and "incid q l"
  shows "l = line_through p q"
proof -
  let ?l' = "vec_of_homog l"
  let ?m = "line_through p q"
  let ?m' = "vec_of_homog ?m"
  let ?p' = "vec_of_homog p"
  let ?q' = "vec_of_homog q"
  let ?A = "{?p', ?q'}"
  let ?B = "insert ?m' ?A"
  from line_through_incident
  have "incid p ?m" and "incid q ?m" by simp_all
  with \<open>incid p l\<close> and \<open>incid q l\<close>
  have ortho: "\<And>w. w\<in>?A \<Longrightarrow> orthogonal ?m' w" "\<And>w. w\<in>?A \<Longrightarrow> orthogonal ?l' w"
    unfolding incid_def and orthogonal_def
    by (metis empty_iff incidz.rep_eq inner_commute insert_iff)+
  from proj2_rep_independent and \<open>p \<noteq> q\<close> have "independent ?A" by simp
  from homog_non_zero have "?m' \<noteq> 0" by simp
  with orthogonal_independent \<open>independent ?A\<close> ortho
  have "independent ?B" by auto

  from \<open>p \<noteq> q\<close> have "?p' \<noteq> ?q'"
    by (metis Quotient3_abs_rep Quotient3_homogz homogz_of_homog_inject)
  hence "card ?A = 2" by simp
  moreover have "?m' \<notin> ?A"
    using ortho(1) orthogonal_self homog_non_zero by auto
  ultimately have "card ?B = 3" by simp
  with independent_is_basis [of ?B] and \<open>independent ?B\<close>
  have "is_basis ?B" by simp
  with basis_expand obtain c where "?l' = (\<Sum> v\<in>?B. c v *\<^sub>R v)" by auto
  let ?l'' = "?l' - c ?m' *\<^sub>R ?m'"
  from \<open>?l' = (\<Sum> v\<in>?B. c v *\<^sub>R v)\<close> and \<open>?m' \<notin> ?A\<close>
  have "?l'' = (\<Sum> v\<in>?A. c v *\<^sub>R v)" by simp
  with orthogonal_sum [of ?A] ortho
  have "orthogonal ?l' ?l''" and "orthogonal ?m' ?l''"
    by (simp_all add: scalar_equiv)
  from \<open>orthogonal ?m' ?l''\<close>
  have "orthogonal (c ?m' *\<^sub>R ?m') ?l''" by (simp add: orthogonal_clauses)
  with \<open>orthogonal ?l' ?l''\<close>
  have "orthogonal ?l'' ?l''" by (simp add: orthogonal_clauses)
  with orthogonal_self_eq_0 [of ?l''] have "?l'' = 0" by simp
  with proj2_rep_dependent [of 1 l "- c ?m'" ?m] show "l = ?m" by simp
qed

lemma incid_unique:
  assumes "incid p l"
  and "incid q l"
  and "incid p m"
  and "incid q m"
  shows "p = q \<or> l = m"
proof cases
  assume "p = q"
  thus "p = q \<or> l = m" ..
next
  assume "p \<noteq> q"
  with \<open>incid p l\<close> and \<open>incid q l\<close>
    and line_through_unique
  have "l = line_through p q" by simp
  moreover from \<open>p \<noteq> q\<close> and \<open>incid p m\<close> and \<open>incid q m\<close>
  have "m = line_through p q" by (rule line_through_unique)
  ultimately show "p = q \<or> l = m" by simp
qed

lemma proj2_lines_define_point: "\<exists> p. incid p l \<and> incid p m"
proof -
  let ?l' = "l"
  let ?m' = "m"
  from proj2_points_define_line [of ?l' ?m']
  obtain p' where "incid ?l' p' \<and> incid ?m' p'" by auto
  hence "incid p' l \<and> incid p' m"
    unfolding incid_def
    by (simp add: incidz.rep_eq inner_commute)
  thus "\<exists> p. incid p l \<and> incid p m" by auto
qed

definition intersection :: "homog \<Rightarrow> homog \<Rightarrow> homog" where
  "intersection \<equiv> line_through"

declare intersection_def [simp]


lemma intersection_incident:
  shows "incid (intersection l m) l"
  and "incid (intersection l m) m"
  using line_through_incident(1) [of "l" "m"]
    and line_through_incident(2) [of "m" "l"]
  unfolding intersection_def
  by (simp_all add: incid_commute)

lemma intersection_unique:
  assumes "l \<noteq> m" and "incid p l" and "incid p m"
  shows "p = intersection l m"
proof -
  from \<open>incid p l\<close> and \<open>incid p m\<close>
    and incid_commute
  have "incid l p" and "incid m p"
    by simp_all
  with \<open>l \<noteq> m\<close> and line_through_unique
  have "p = line_through l m" by simp
  thus "p = intersection l m"
    unfolding intersection_def
    by (simp)
qed

lemma proj2_not_self_incident:
  "\<not> (incid p p)"
  unfolding incid_def
  using homog_non_zero and inner_eq_zero_iff [of "vec_of_homog p"]
  by (simp add: incidz.rep_eq)

lemma proj2_another_point_on_line:
  "\<exists> q. q \<noteq> p \<and> incid q l"
proof -
  let ?m = "p"
  let ?q = "intersection l ?m"
  from intersection_incident
  have "incid ?q l" and "incid ?q ?m" by simp_all
  from \<open>incid ?q ?m\<close> and proj2_not_self_incident have "?q \<noteq> p" by auto
  with \<open>incid ?q l\<close> show "\<exists> q. q \<noteq> p \<and> incid q l" by auto
qed

lemma proj2_another_line_through_point:
  "\<exists> m. m \<noteq> l \<and> incid p m"
proof -
  from proj2_another_point_on_line
  obtain q where "q \<noteq> l \<and> incid q p" by auto
  with incid_commute
  have "q \<noteq> l \<and> incid p q" by auto
  thus "\<exists> m. m \<noteq> l \<and> incid p m" ..
qed

lemma incid_abs:
  assumes "v \<noteq> 0" and "w \<noteq> 0"
  shows "incid (homog_of_vec v) (homog_of_vec w) \<longleftrightarrow> v \<bullet> w = 0"
  by (metis assms(1) assms(2) homogz_homog_eq incid_def incidz.abs_eq inner_eq_zero_iff zero_homogz_def)

lemma incid_left_abs:
  assumes "v \<noteq> 0"
  shows "incid (homog_of_vec v) l \<longleftrightarrow> v \<bullet> (vec_of_homog l) = 0"
proof -
  have "vec_of_homog l \<noteq> 0"
    by (simp add: homog_non_zero)
  with \<open>v \<noteq> 0\<close> and incid_abs [of v "vec_of_homog l"]
  show "incid (homog_of_vec v) l \<longleftrightarrow> v \<bullet> (vec_of_homog l) = 0"
    by (metis Quotient3_abs_rep Quotient3_homogz homogz_of_homog_inverse)
qed

lemma incid_right_abs:
  assumes "v \<noteq> 0"
  shows "incid p (homog_of_vec v) \<longleftrightarrow> (vec_of_homog p) \<bullet> v = 0"
proof -
  have "vec_of_homog p \<noteq> 0" by (simp add: homog_non_zero)
  with \<open>v \<noteq> 0\<close> and incid_abs [of "vec_of_homog p" v]
  show "incid p (homog_of_vec v) \<longleftrightarrow> (vec_of_homog p) \<bullet> v = 0"
    by (metis Quotient3_abs_rep Quotient3_homogz homogz_of_homog_inverse)
qed

lemma "p \<noteq> q \<Longrightarrow> join p q = line_through p q"
  by (simp add: incid_joinz line_through_unique)


end