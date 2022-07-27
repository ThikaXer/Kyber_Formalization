theory Coeffs

imports Main "HOL-Computational_Algebra.Computational_Algebra" 

begin

lemma coeffs_in_coeff:
  assumes "\<forall>i. poly.coeff x i \<in> A"
  shows "set (coeffs x) \<subseteq> A"
by (simp add: assms coeffs_def image_subsetI)

end