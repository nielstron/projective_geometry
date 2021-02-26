
(* Title:      HOL/Analysis/Cross3.thy
   Author:     L C Paulson, University of Cambridge

Ported from HOL Light
*)

section\<open>Vector Cross Products in 3 Dimensions\<close>
theory Complex_Cross3
  imports "HOL-Analysis.Determinants" "HOL-Analysis.Cartesian_Euclidean_Space"
"Complex_Inner_Product"
begin

subsection \<open>Orthogonality\<close>

definition\<^marker>\<open>tag important\<close> (in complex_inner) "orthogonal\<^sub>c x y \<longleftrightarrow> x \<bullet> y = 0"

context real_inner
begin

lemma orthogonal\<^sub>c_self: "orthogonal\<^sub>c x x \<longleftrightarrow> x = 0"
  by (simp add: orthogonal\<^sub>c_def)

lemma orthogonal\<^sub>c_clauses:
  "orthogonal\<^sub>c a 0"
  "orthogonal\<^sub>c a x \<Longrightarrow> orthogonal\<^sub>c a (c *\<^sub>C x)"
  "orthogonal\<^sub>c a x \<Longrightarrow> orthogonal\<^sub>c a (- x)"
  "orthogonal\<^sub>c a x \<Longrightarrow> orthogonal\<^sub>c a y \<Longrightarrow> orthogonal\<^sub>c a (x + y)"
  "orthogonal\<^sub>c a x \<Longrightarrow> orthogonal\<^sub>c a y \<Longrightarrow> orthogonal\<^sub>c a (x - y)"
  "orthogonal\<^sub>c 0 a"
  "orthogonal\<^sub>c x a \<Longrightarrow> orthogonal\<^sub>c (c *\<^sub>C x) a"
  "orthogonal\<^sub>c x a \<Longrightarrow> orthogonal\<^sub>c (- x) a"
  "orthogonal\<^sub>c x a \<Longrightarrow> orthogonal\<^sub>c y a \<Longrightarrow> orthogonal\<^sub>c (x + y) a"
  "orthogonal\<^sub>c x a \<Longrightarrow> orthogonal\<^sub>c y a \<Longrightarrow> orthogonal\<^sub>c (x - y) a"
  unfolding orthogonal\<^sub>c_def inner_add inner_diff by auto

end

lemma orthogonal\<^sub>c_commute: "orthogonal\<^sub>c x y \<longleftrightarrow> orthogonal\<^sub>c y x"
  by (simp add: orthogonal\<^sub>c_def inner_commute)

lemma orthogonal\<^sub>c_scaleR [simp]: "c \<noteq> 0 \<Longrightarrow> orthogonal\<^sub>c (c *\<^sub>R x) = orthogonal\<^sub>c x"
  by (rule ext) (simp add: orthogonal\<^sub>c_def)

lemma pairwise_ortho_scaleR:
    "pairwise (\<lambda>i j. orthogonal\<^sub>c (f i) (g j)) B
    \<Longrightarrow> pairwise (\<lambda>i j. orthogonal\<^sub>c (a i *\<^sub>R f i) (a j *\<^sub>R g j)) B"
  by (auto simp: pairwise_def orthogonal\<^sub>c_clauses)

lemma orthogonal\<^sub>c_rvsum:
    "\<lbrakk>finite s; \<And>y. y \<in> s \<Longrightarrow> orthogonal\<^sub>c x (f y)\<rbrakk> \<Longrightarrow> orthogonal\<^sub>c x (sum f s)"
  by (induction s rule: finite_induct) (auto simp: orthogonal\<^sub>c_clauses)

lemma orthogonal\<^sub>c_lvsum:
    "\<lbrakk>finite s; \<And>x. x \<in> s \<Longrightarrow> orthogonal\<^sub>c (f x) y\<rbrakk> \<Longrightarrow> orthogonal\<^sub>c (sum f s) y"
  by (induction s rule: finite_induct) (auto simp: orthogonal\<^sub>c_clauses)


context includes no_Set_Product_syntax 
begin \<comment>\<open>locally disable syntax for set product, to avoid warnings\<close>

definition\<^marker>\<open>tag important\<close> cross3 :: "[complex^3, complex^3] \<Rightarrow> complex^3"  (infixr "\<times>" 80)
  where "a \<times> b \<equiv>
    vector [a$2 * b$3 - a$3 * b$2,
            a$3 * b$1 - a$1 * b$3,
            a$1 * b$2 - a$2 * b$1]"

end

bundle cross3_syntax begin
notation cross3 (infixr "\<times>" 80)
no_notation Product_Type.Times (infixr "\<times>" 80)
end

bundle no_cross3_syntax begin
no_notation cross3 (infixr "\<times>" 80)
notation Product_Type.Times (infixr "\<times>" 80)
end

unbundle cross3_syntax

subsection\<open> Basic lemmas\<close>

lemmas cross3_simps = cross3_def inner_vec_def sum_3 det_3 vec_eq_iff vector_def algebra_simps

lemma dot_cross_self: "x \<bullet> (x \<times> y) = 0" "x \<bullet> (y \<times> x) = 0" "(x \<times> y) \<bullet> y = 0" "(y \<times> x) \<bullet> y = 0"
  by (simp_all add: orthogonal\<^sub>c_def cross3_simps)

lemma  orthogonal\<^sub>c_cross: "orthogonal\<^sub>c (x \<times> y) x" "orthogonal\<^sub>c (x \<times> y) y"  
                        "orthogonal\<^sub>c y (x \<times> y)" "orthogonal\<^sub>c (x \<times> y) x"
  by (simp_all add: orthogonal\<^sub>c_def dot_cross_self)

lemma  cross_zero_left [simp]: "0 \<times> x = 0" and cross_zero_right [simp]: "x \<times> 0 = 0" for x::"real^3"
  by (simp_all add: cross3_simps)

lemma  cross_skew: "(x \<times> y) = -(y \<times> x)" for x::"real^3"
  by (simp add: cross3_simps)

lemma  cross_refl [simp]: "x \<times> x = 0" for x::"real^3"
  by (simp add: cross3_simps)

lemma  cross_add_left: "(x + y) \<times> z = (x \<times> z) + (y \<times> z)" for x::"real^3"
  by (simp add: cross3_simps)

lemma  cross_add_right: "x \<times> (y + z) = (x \<times> y) + (x \<times> z)" for x::"real^3"
  by (simp add: cross3_simps)

lemma  cross_mult_left: "(c *\<^sub>R x) \<times> y = c *\<^sub>R (x \<times> y)" for x::"real^3"
  by (simp add: cross3_simps)

lemma  cross_mult_right: "x \<times> (c *\<^sub>R y) = c *\<^sub>R (x \<times> y)" for x::"real^3"
  by (simp add: cross3_simps)

lemma  cross_minus_left [simp]: "(-x) \<times> y = - (x \<times> y)" for x::"real^3"
  by (simp add: cross3_simps)

lemma  cross_minus_right [simp]: "x \<times> -y = - (x \<times> y)" for x::"real^3"
  by (simp add: cross3_simps)

lemma  left_diff_distrib: "(x - y) \<times> z = x \<times> z - y \<times> z" for x::"real^3"
  by (simp add: cross3_simps)

lemma  right_diff_distrib: "x \<times> (y - z) = x \<times> y - x \<times> z" for x::"real^3"
  by (simp add: cross3_simps)

hide_fact (open) left_diff_distrib right_diff_distrib

proposition Jacobi: "x \<times> (y \<times> z) + y \<times> (z \<times> x) + z \<times> (x \<times> y) = 0" for x::"real^3"
  by (simp add: cross3_simps)

proposition Lagrange: "x \<times> (y \<times> z) = (x \<bullet> z) *\<^sub>R y - (x \<bullet> y) *\<^sub>R z"
  by (simp add: cross3_simps) (metis (full_types) exhaust_3)

proposition cross_triple: "(x \<times> y) \<bullet> z = (y \<times> z) \<bullet> x"
  by (simp add: cross3_def inner_vec_def sum_3 vec_eq_iff algebra_simps)

lemma  cross_components:
   "(x \<times> y)$1 = x$2 * y$3 - y$2 * x$3" "(x \<times> y)$2 = x$3 * y$1 - y$3 * x$1" "(x \<times> y)$3 = x$1 * y$2 - y$1 * x$2"
  by (simp_all add: cross3_def inner_vec_def sum_3 vec_eq_iff algebra_simps)

lemma  cross_basis: "(axis 1 1) \<times> (axis 2 1) = axis 3 1" "(axis 2 1) \<times> (axis 1 1) = -(axis 3 1)" 
                   "(axis 2 1) \<times> (axis 3 1) = axis 1 1" "(axis 3 1) \<times> (axis 2 1) = -(axis 1 1)" 
                   "(axis 3 1) \<times> (axis 1 1) = axis 2 1" "(axis 1 1) \<times> (axis 3 1) = -(axis 2 1)"
  using exhaust_3
  by (force simp add: axis_def cross3_simps)+

lemma  cross_basis_nonzero:
  "u \<noteq> 0 \<Longrightarrow> u \<times> axis 1 1 \<noteq> 0 \<or> u \<times> axis 2 1 \<noteq> 0 \<or> u \<times> axis 3 1 \<noteq> 0"
  by (clarsimp simp add: axis_def cross3_simps) (metis exhaust_3)

lemma  cross_dot_cancel:
  fixes x::"real^3"
  assumes deq: "x \<bullet> y = x \<bullet> z" and veq: "x \<times> y = x \<times> z" and x: "x \<noteq> 0"
  shows "y = z" 
proof -
  have "x \<bullet> x \<noteq> 0"
    by (simp add: x)
  then have "y - z = 0"
    using veq
    by (metis (no_types, lifting) Cross3.right_diff_distrib Lagrange deq eq_iff_diff_eq_0 inner_diff_right scale_eq_0_iff)
  then show ?thesis
    using eq_iff_diff_eq_0 by blast
qed

lemma  norm_cross_dot: "(norm (x \<times> y))\<^sup>2 + (x \<bullet> y)\<^sup>2 = (norm x * norm y)\<^sup>2"
  unfolding power2_norm_eq_inner power_mult_distrib
  by (simp add: cross3_simps power2_eq_square)

lemma  dot_cross_det: "x \<bullet> (y \<times> z) = det(vector[x,y,z])"
  by (simp add: cross3_simps) 

lemma  cross_cross_det: "(w \<times> x) \<times> (y \<times> z) = det(vector[w,x,z]) *\<^sub>R y - det(vector[w,x,y]) *\<^sub>R z"
  using exhaust_3 by (force simp add: cross3_simps) 

proposition  dot_cross: "(w \<times> x) \<bullet> (y \<times> z) = (w \<bullet> y) * (x \<bullet> z) - (w \<bullet> z) * (x \<bullet> y)"
  by (force simp add: cross3_simps)

proposition  norm_cross: "(norm (x \<times> y))\<^sup>2 = (norm x)\<^sup>2 * (norm y)\<^sup>2 - (x \<bullet> y)\<^sup>2"
  unfolding power2_norm_eq_inner power_mult_distrib
  by (simp add: cross3_simps power2_eq_square)

lemma  cross_eq_0: "x \<times> y = 0 \<longleftrightarrow> collinear{0,x,y}"
proof -
  have "x \<times> y = 0 \<longleftrightarrow> norm (x \<times> y) = 0"
    by simp
  also have "... \<longleftrightarrow> (norm x * norm y)\<^sup>2 = (x \<bullet> y)\<^sup>2"
    using norm_cross [of x y] by (auto simp: power_mult_distrib)
  also have "... \<longleftrightarrow> \<bar>x \<bullet> y\<bar> = norm x * norm y"
    using power2_eq_iff
    by (metis (mono_tags, hide_lams) abs_minus abs_norm_cancel abs_power2 norm_mult power_abs real_norm_def) 
  also have "... \<longleftrightarrow> collinear {0, x, y}"
    by (rule norm_cauchy_schwarz_equal)
  finally show ?thesis .
qed

lemma  cross_eq_self: "x \<times> y = x \<longleftrightarrow> x = 0" "x \<times> y = y \<longleftrightarrow> y = 0"
  apply (metis cross_zero_left dot_cross_self(1) inner_eq_zero_iff)
  by (metis cross_zero_right dot_cross_self(2) inner_eq_zero_iff)

lemma  norm_and_cross_eq_0:
   "x \<bullet> y = 0 \<and> x \<times> y = 0 \<longleftrightarrow> x = 0 \<or> y = 0" (is "?lhs = ?rhs")
proof 
  assume ?lhs
  then show ?rhs
    by (metis cross_dot_cancel cross_zero_right inner_zero_right)
qed auto

lemma  bilinear_cross: "bilinear(\<times>)"
  apply (auto simp add: bilinear_def linear_def)
  apply unfold_locales
  apply (simp add: cross_add_right)
  apply (simp add: cross_mult_right)
  apply (simp add: cross_add_left)
  apply (simp add: cross_mult_left)
  done

subsection   \<open>Preservation by rotation, or other orthogonal\<^sub>c transformation up to sign\<close>

lemma  cross_matrix_mult: "transpose A *v ((A *v x) \<times> (A *v y)) = det A *\<^sub>R (x \<times> y)"
  apply (simp add: vec_eq_iff   )
  apply (simp add: vector_matrix_mult_def matrix_vector_mult_def forall_3 cross3_simps)
  done

lemma  cross_orthogonal\<^sub>c_matrix:
  assumes "orthogonal\<^sub>c_matrix A"
  shows "(A *v x) \<times> (A *v y) = det A *\<^sub>R (A *v (x \<times> y))"
proof -
  have "mat 1 = transpose (A ** transpose A)"
    by (metis (no_types) assms orthogonal\<^sub>c_matrix_def transpose_mat)
  then show ?thesis
    by (metis (no_types) vector_matrix_mul_rid vector_transpose_matrix cross_matrix_mult matrix_vector_mul_assoc matrix_vector_mult_scaleR)
qed

lemma  cross_rotation_matrix: "rotation_matrix A \<Longrightarrow> (A *v x) \<times> (A *v y) =  A *v (x \<times> y)"
  by (simp add: rotation_matrix_def cross_orthogonal\<^sub>c_matrix)

lemma  cross_rotoinversion_matrix: "rotoinversion_matrix A \<Longrightarrow> (A *v x) \<times> (A *v y) = - A *v (x \<times> y)"
  by (simp add: rotoinversion_matrix_def cross_orthogonal\<^sub>c_matrix scaleR_matrix_vector_assoc)

lemma  cross_orthogonal\<^sub>c_transformation:
  assumes "orthogonal\<^sub>c_transformation f"
  shows   "(f x) \<times> (f y) = det(matrix f) *\<^sub>R f(x \<times> y)"
proof -
  have orth: "orthogonal\<^sub>c_matrix (matrix f)"
    using assms orthogonal\<^sub>c_transformation_matrix by blast
  have "matrix f *v z = f z" for z
    using assms orthogonal\<^sub>c_transformation_matrix by force
  with cross_orthogonal\<^sub>c_matrix [OF orth] show ?thesis
    by simp
qed

lemma  cross_linear_image:
   "\<lbrakk>linear f; \<And>x. norm(f x) = norm x; det(matrix f) = 1\<rbrakk>
           \<Longrightarrow> (f x) \<times> (f y) = f(x \<times> y)"
  by (simp add: cross_orthogonal\<^sub>c_transformation orthogonal\<^sub>c_transformation)

subsection \<open>Continuity\<close>

lemma  continuous_cross: "\<lbrakk>continuous F f; continuous F g\<rbrakk> \<Longrightarrow> continuous F (\<lambda>x. (f x) \<times> (g x))"
  apply (subst continuous_componentwise)
  apply (clarsimp simp add: cross3_simps)
  apply (intro continuous_intros; simp)
  done

lemma  continuous_on_cross:
  fixes f :: "'a::t2_space \<Rightarrow> real^3"
  shows "\<lbrakk>continuous_on S f; continuous_on S g\<rbrakk> \<Longrightarrow> continuous_on S (\<lambda>x. (f x) \<times> (g x))"
  by (simp add: continuous_on_eq_continuous_within continuous_cross)

unbundle no_cross3_syntax

end

