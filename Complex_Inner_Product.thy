(*  Title:      HOL/Analysis/Inner_Product.thy
    Author:     Brian Huffman
*)

section \<open>Inner Product Spaces and Gradient Derivative\<close>

theory Complex_Inner_Product
imports Complex_Main "Complex_Vector_Spaces"
begin

subsection \<open>Complex inner product spaces\<close>

declare  complex_cnj[simp] complex_mult[simp]

text \<open>
  Temporarily relax type constraints for \<^term>\<open>open\<close>, \<^term>\<open>uniformity\<close>,
  \<^term>\<open>dist\<close>, and \<^term>\<open>norm\<close>.
\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>open\<close>, SOME \<^typ>\<open>'a::open set \<Rightarrow> bool\<close>)\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>dist\<close>, SOME \<^typ>\<open>'a::dist \<Rightarrow> 'a \<Rightarrow> real\<close>)\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>uniformity\<close>, SOME \<^typ>\<open>('a::uniformity \<times> 'a) filter\<close>)\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>norm\<close>, SOME \<^typ>\<open>'a::norm \<Rightarrow> real\<close>)\<close>

class complex_inner = complex_vector + sgn_div_norm + dist_norm + uniformity_dist + open_uniformity +
  fixes inner :: "'a \<Rightarrow> 'a \<Rightarrow> complex"
  assumes inner_commute: "inner x y = cnj (inner y x)"
  and inner_add_left: "inner (x + y) z = inner x z + inner y z"
  and inner_scaleC_left [simp]: "inner (scaleC r x) y = (cnj r) * (inner x y)"
  and inner_zero_iff_zero [simp]: "inner x x = 0 \<longleftrightarrow> x = 0"
  and inner_nonneg_real [simp]: "Im (inner x x) = 0" "Re (inner x x) \<ge> 0"
begin

lemma inner_zero_left [simp]: "inner 0 x = 0"
  using inner_add_left [of 0 0 x] by simp

lemma inner_minus_left [simp]: "inner (- x) y = - inner x y"
  using inner_add_left [of x "- x" y]
  by (smt (z3) ab_semigroup_add_class.add.abel_semigroup_axioms abel_semigroup.commute cancel_ab_semigroup_add_class.add_diff_cancel_left' group_add_class.minus_diff_eq local.add_0_right local.inner_add_left local.neg_eq_iff_add_eq_0)

lemma inner_diff_left: "inner (x - y) z = inner x z - inner y z"
  using inner_add_left [of x "- y" z] by simp

lemma inner_sum_left: "inner (\<Sum>x\<in>A. f x) y = (\<Sum>x\<in>A. inner (f x) y)"
  by (cases "finite A", induct set: finite, simp_all add: inner_add_left)

lemma all_zero_iff [simp]: "(\<forall>u. inner x u = 0) \<longleftrightarrow> (x = 0)"
  apply auto
  using inner_zero_iff_zero by blast

text \<open>Transfer distributivity rules to right argument.\<close>

lemma inner_add_right: "inner x (y + z) = inner x y + inner x z"
  using inner_add_left [of y z x]
  by (metis complex_cnj_add local.inner_commute)

lemma inner_scaleC_right [simp]: "inner x (scaleC r y) = r * (inner x y)"
  using inner_scaleC_left [of r y x]
  by (metis complex_cnj_cnj complex_cnj_mult local.inner_commute)

lemma inner_zero_right [simp]: "inner x 0 = 0"
  using inner_zero_left [of x]
  by (metis (mono_tags, lifting) complex_cnj_zero local.inner_commute)

lemma inner_minus_right [simp]: "inner x (- y) = - inner x y"
  using inner_minus_left [of y x]
  by (metis complex_cnj_minus local.inner_commute)

lemma inner_diff_right: "inner x (y - z) = inner x y - inner x z"
  using inner_diff_left [of y z x]
  by (metis complex_cnj_diff local.inner_commute)

lemma inner_sum_right: "inner x (\<Sum>y\<in>A. f y) = (\<Sum>y\<in>A. inner x (f y))"
  using inner_sum_left [of f A x] oops

lemmas inner_add [algebra_simps] = inner_add_left inner_add_right
lemmas inner_diff [algebra_simps]  = inner_diff_left inner_diff_right
lemmas inner_scaleC = inner_scaleC_left inner_scaleC_right

text \<open>Legacy theorem names\<close>
lemmas inner_left_distrib = inner_add_left
lemmas inner_right_distrib = inner_add_right
lemmas inner_distrib = inner_left_distrib inner_right_distrib

lemma inner_gt_zero_iff [simp]: "0 < Re (inner x x) \<longleftrightarrow> x \<noteq> 0"
  by (smt (verit, del_insts) complex_eqI local.inner_nonneg_real(1) local.inner_nonneg_real(2) local.inner_zero_iff_zero zero_complex.simps(1))

(* TODO *)
lemma power2_norm_eq_inner: "(norm x)\<^sup>2 = inner x x"
  oops

text \<open>Identities involving complex multiplication and division.\<close>

lemma inner_mult_left: "inner (of_complex m * a) b = cnj m * (inner a b)"
  by (metis complex_inner_class.inner_scaleC_left scaleC_conv_of_complex)

lemma inner_mult_right: "inner a (of_complex m * b) = m * (inner a b)"
  by (metis complex_inner_class.inner_scaleC_right scaleC_conv_of_complex)

lemma inner_mult_left': "inner (a * of_complex m) b = cnj m * (inner a b)"
  by (simp add: of_complex_def)

lemma inner_mult_right': "inner a (b * of_complex m) = (inner a b) * m"
  by (simp add: of_complex_def complex_inner_class.inner_scaleC_right)

(* TODO, see https://arxiv.org/pdf/1701.06031.pdf *)
lemma Cauchy_Schwarz_ineq:
  "Re ((inner x y)\<^sup>2) \<le> Re (inner x x * inner y y)"
  oops

lemma Cauchy_Schwarz_ineq2:
  "Re \<bar>inner x y\<bar> \<le> norm x * norm y"
  oops

lemma norm_cauchy_schwarz: "Re (inner x y) \<le> norm x * norm y"
  oops

subclass real_normed_vector
  apply standard
  oops

end


lemma inner_divide_left:
  fixes a :: "'a :: {complex_inner,complex_div_algebra}"
  shows "inner (a / of_complex m) b = (inner a b) / cnj m"
  by (metis complex_cnj_divide complex_cnj_one divide_inverse inner_mult_left' inverse_eq_divide mult.commute of_complex_inverse)

lemma inner_divide_right:
  fixes a :: "'a :: {complex_inner,complex_div_algebra}"
  shows "inner a (b / of_complex m) = (inner a b) / m"
  by (metis divide_inverse inner_mult_right' of_complex_inverse)

text \<open>
  Re-enable constraints for \<^term>\<open>open\<close>, \<^term>\<open>uniformity\<close>,
  \<^term>\<open>dist\<close>, and \<^term>\<open>norm\<close>.
\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>open\<close>, SOME \<^typ>\<open>'a::topological_space set \<Rightarrow> bool\<close>)\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>uniformity\<close>, SOME \<^typ>\<open>('a::uniform_space \<times> 'a) filter\<close>)\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>dist\<close>, SOME \<^typ>\<open>'a::metric_space \<Rightarrow> 'a \<Rightarrow> real\<close>)\<close>

subsection \<open>Class instances\<close>
  

instantiation complex :: complex_inner
begin

definition inner_complex_def [simp]: "inner = (\<lambda>x y. (cnj x) *  y)"

find_theorems "Complex _ _  * Complex _ _"

instance
proof (standard, goal_cases)
  case (1 x y)
  then show ?case
    unfolding inner_complex_def
    by auto
next
  case (2 x y z)
  then show ?case
    unfolding inner_complex_def
    by (simp add: ring_class.ring_distribs(2))
next
  case (3 r x y)
  then show ?case
    unfolding inner_complex_def complex_scaleC_def
    by simp
next
  case (4 x)
  then show ?case 
    by simp
next
  case (5 x)
  then show ?case
    unfolding inner_complex_def
    by auto
  case (6 x)
  then show ?case
    by auto
qed

end

lemma
  shows complex_inner_1_left[simp]: "inner 1 x = x"
    and complex_inner_1_right[simp]: "inner x 1 = cnj x"
  by simp_all


lemma complex_inner_i_left [simp]: "inner \<i> x = -\<i>*x"
  unfolding inner_complex_def by simp

lemma complex_inner_i_right [simp]: "inner x \<i> = cnj x * \<i>"
  unfolding inner_complex_def by simp


subsection \<open>Gradient derivative\<close>
(* TODO *)

bundle inner_syntax begin
notation inner (infix "\<bullet>" 70)
end

bundle no_inner_syntax begin
no_notation inner (infix "\<bullet>" 70)
end

end
