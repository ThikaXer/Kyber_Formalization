theory Cyclotomic_Poly
  imports "HOL-Computational_Algebra.Computational_Algebra"
  "Berlekamp_Zassenhaus.Poly_Mod" 
  "Berlekamp_Zassenhaus.Poly_Mod_Finite_Field"
begin

fun cyclotomic_poly :: "nat \<Rightarrow> int poly" where
  "cyclotomic_poly n = (if n = 0 then 1 else (Polynomial.monom 1 n - 1) div (\<Prod>d \<in> {0<..<n} \<inter> {d. d dvd n}. cyclotomic_poly d))"

lemmas [simp del] = cyclotomic_poly.simps

lemma cyclotomic_poly_1: "cyclotomic_poly (Suc 0) = [:-1, 1:]"
  by (subst cyclotomic_poly.simps) (auto simp: monom_Suc)

lemma of_nat_div': "b dvd a \<Longrightarrow> of_nat (a div b) = (of_nat a / of_nat b :: 'a :: field_char_0)"
  apply (elim dvdE)
  apply (auto)
  done

definition totatives' :: "nat \<Rightarrow> nat set"
  where "totatives' n = {..<n} \<inter> {d. coprime d n}"

lemma of_int_poly_dvd_imp_dvd:
  assumes "of_int_poly p dvd (of_int_poly q :: 'a :: {idom_divide, ring_char_0} poly)"
  shows   "p dvd q"
  sorry

lemma of_int_poly_div:
  assumes "of_int_poly q dvd (of_int_poly p :: 'a :: {idom_divide, ring_char_0} poly)"
  shows   "(of_int_poly (p div q) :: 'a poly) = of_int_poly p div of_int_poly q"
proof -
  have "of_int_poly (p div q) * (of_int_poly q :: 'a poly) =
        of_int_poly (p div q * q)"
    by (simp add: of_int_poly_hom.hom_mult)
  also have "p div q * q = p"
    using of_int_poly_dvd_imp_dvd[OF assms] by simp
  finally show ?thesis
    by (metis div_by_0 nonzero_mult_div_cancel_right of_int_poly_hom.hom_0)
qed

lemma cyclotomic_poly_0 [simp]: "cyclotomic_poly 0 = 1"
  by (subst cyclotomic_poly.simps) auto

lemma monom_1_minus_1_eq: "Polynomial.monom 1 n - 1 = (\<Prod>k<n. [:-cis (2 * pi * real k / real n), 1:])"
  sorry

lemma of_int_poly_cyclotomic_poly:
  "of_int_poly (cyclotomic_poly n) = (\<Prod>k\<in>totatives n. [:-cis (2 * pi * k / n), 1:])"
proof (induction n rule: less_induct)
  case (less n)

  let ?C = cyclotomic_poly
  have nz: "?C d \<noteq> 0" if "d > 0" "d < n" for d
  proof
    assume "?C d = 0"
    hence "(0 :: complex poly) = of_int_poly (?C d)"
      by simp
    thus False using that
      by (subst (asm) less.IH) auto
  qed

  show ?case
  proof (cases "n > 0")
    case True

    define f where "f = (\<lambda>k. (n div gcd n k, k div gcd n k))"
    define g where "g = (\<lambda>(d, k). k * (n div d))"
    define h where "h = (\<lambda>(d::nat, k::nat). (if d = 1 then (1, 1 - k) else (d, k)))"
  
    define S where "S = (SIGMA d:{0<..<n}\<inter>{d. d dvd n}. totatives d)"
    define S' where "S' = (SIGMA d:{d. d dvd n}. totatives' d)"
    define S'' where "S'' = (SIGMA d:{d. d dvd n}. totatives d)"
    have "of_int_poly (Polynomial.monom 1 n - 1) = (Polynomial.monom 1 n - 1 :: complex poly)"
      by (simp add: of_int_poly_hom.hom_minus)
    also have "\<dots> = (\<Prod>k<n. [:-cis (2 * pi * k / n), 1:])"
      by (rule monom_1_minus_1_eq)
    also have "\<dots> = (\<Prod>k<n. [:-cis (2 * pi * (k div gcd k n) / (n div gcd k n)), 1:])"
      apply (intro prod.cong refl)
      apply (auto simp: of_nat_div')
      done
    also have "\<dots> = (\<Prod>(d,k)\<in>S'. [:-cis (2 * pi * k / d), 1:])"
      apply (rule prod.reindex_bij_witness[of _ g f])
          apply (auto simp: g_def f_def S'_def totatives'_def gcd.commute coprime_commute)
            apply (metis dvd_mult_div_cancel gcd.commute gr_implies_not0 mult.commute mult_eq_0_iff nonzero_mult_div_cancel_right semiring_gcd_class.gcd_dvd2)
           apply (metis dvd_mult_div_cancel dvd_triv_left mult.commute semiring_gcd_class.gcd_dvd2)
          apply (metis comm_monoid_gcd_class.gcd_dvd2 dvd_div_mult_self less_mult_imp_div_less)
         apply (metis div_gcd_coprime not_less0)
        apply (smt (z3) coprime_iff_gcd_eq_1 div_mult_self1_is_m div_positive dvd_div_mult_self dvd_imp_le dvd_pos_nat gcd.commute gcd_mult_distrib_nat \<open>n > 0\<close> mult.commute mult.right_neutral)
      apply (smt (z3) coprime_iff_gcd_eq_1 div_mult_self_is_m div_positive dvd_div_mult_self dvd_imp_le dvd_pos_nat gcd.commute gcd_mult_distrib_nat \<open>n > 0\<close> mult.commute mult.right_neutral)
      using \<open>n > 0\<close> by fastforce
    also have "\<dots> = (\<Prod>(d,k)\<in>S''. [:-cis (2 * pi * k / d), 1:])"
      apply (rule prod.reindex_bij_witness[of _ h h])
          apply (auto simp: h_def S'_def S''_def totatives_def totatives'_def)
      apply (metis One_nat_def coprime_common_divisor_nat gcd_nat.extremum gcd_nat.refl gr0I)
      by (metis antisym_conv1 coprime_common_divisor_nat dvd_1_left dvd_refl)
    also have "S'' = S \<union> {n} \<times> totatives n"
      using \<open>n > 0\<close>
      apply (auto simp: S''_def S_def totatives_def)
      apply (metis nat_dvd_not_less not_less_iff_gr_or_eq)
      apply (metis dvd_imp_le le_neq_implies_less)
      done
    also have "(\<Prod>(d,k)\<in>\<dots>. [:-cis (2 * pi * k / d), 1:]) =
                 (\<Prod>(d,k)\<in>S. [:-cis (2 * pi * k / d), 1:]) *
                 (\<Prod>(d,k)\<in>{n} \<times> totatives n. [:-cis (2 * pi * k / d), 1:])"
      by (subst prod.union_disjoint) (auto simp: S_def)
    also have "(\<Prod>(d,k)\<in>{n} \<times> totatives n. [:-cis (2 * pi * k / d), 1:]) =
               (\<Prod>k\<in>totatives n. [:-cis (2 * pi * k / n), 1:])"
      by (subst prod.Sigma [symmetric]) auto
    also have "(\<Prod>(d,k)\<in>S. [:-cis (2 * pi * k / d), 1:]) =
               (\<Prod>d\<in>{0<..<n}\<inter>{d. d dvd n}. \<Prod>k\<in>totatives d. [:-cis (2 * pi * k / d), 1:])"
      by (subst prod.Sigma) (auto simp: S_def)
    also have "\<dots> = (\<Prod>d\<in>{0<..<n}\<inter>{d. d dvd n}. of_int_poly (?C d))"
      by (intro prod.cong refl less.IH [symmetric]) auto
    also have "\<dots> = of_int_poly ((\<Prod>d\<in>{0<..<n}\<inter>{d. d dvd n}. ?C d))"
      by (simp add: of_int_poly_hom.hom_prod)
    finally have *: "of_int_poly (Polynomial.monom 1 n - 1) =
                       of_int_poly (\<Prod>d\<in>{0<..<n}\<inter>{d. d dvd n}. ?C d) * 
                       (\<Prod>k\<in>totatives n. [:-cis (2 * pi * k / n), 1:])"
      (is "of_int_poly ?X = of_int_poly ?Y * ?Z") .
  
    hence "?Z = of_int_poly ?X div of_int_poly ?Y"
      using nz by (subst eq_commute, subst dvd_div_eq_mult) auto
    also have "\<dots> = of_int_poly (?X div ?Y)"
      using * by (intro of_int_poly_div [symmetric]) auto
    also have "?X div ?Y = ?C n"
      by (subst (2) cyclotomic_poly.simps) (use \<open>n > 0\<close> in simp)
    finally show ?thesis ..
  qed auto
qed

lemma cyclotomic_poly_dvd: "cyclotomic_poly n dvd (Polynomial.monom 1 n - 1)"
proof (cases "n > 1")
  case True
  have "of_int_poly (cyclotomic_poly n) = (\<Prod>k\<in>totatives n. [:-cis (2 * pi * k / n), 1:])"
    by (rule of_int_poly_cyclotomic_poly)
  also have "\<dots> dvd (\<Prod>k<n. [:-cis (2 * pi * k / n), 1:])"
    using True
    apply (intro prod_dvd_prod_subset)
     apply (auto simp: totatives_def)
    by (metis True coprime_common_divisor_nat dvd_refl le_neq_implies_less)
  also have "\<dots> = Polynomial.monom 1 n - 1"
    by (rule monom_1_minus_1_eq [symmetric])
  also have "\<dots> = of_int_poly (Polynomial.monom 1 n - 1)"
    by (simp add: of_int_poly_hom.hom_minus)
  finally show ?thesis
    using of_int_poly_dvd_imp_dvd by blast
next
  case False
  hence "n = 0 \<or> n = 1"
    by auto
  thus ?thesis
    by (auto simp: cyclotomic_poly.simps[of "Suc 0"])
qed

lemma prod_cyclotomic_poly_dvd:
  shows "(\<Prod>d \<in> {0<..<n} \<inter> {d. d dvd n}. cyclotomic_poly d) dvd Polynomial.monom 1 n - 1"
  sorry

lemma coprime_poly_linear_factors:
  assumes "x \<noteq> (y :: 'a :: field)"
  shows   "Rings.coprime [:x, 1:] [:y, 1:]"
  sorry

lemma coprime_cyclotomic_poly:
  fixes m n :: nat
  assumes "m \<noteq> n"
  shows   "Rings.coprime (cyclotomic_poly m) (cyclotomic_poly n)"
proof -
  have "Rings.coprime (of_int_poly (cyclotomic_poly m)) (of_int_poly (cyclotomic_poly n) :: complex poly)"
    unfolding of_int_poly_cyclotomic_poly
  proof (intro prod_coprime_left prod_coprime_right coprime_poly_linear_factors)
    fix k l
    assume kl: "k \<in> totatives m" "l \<in> totatives n"
    show "- cis (2 * pi * real k / real m) \<noteq> - cis (2 * pi * real l / real n)"
    proof
      assume eq: "- cis (2 * pi * real k / real m) = - cis (2 * pi * real l / real n)"
      hence "cis (2 * pi * (real k / real m - real l / real n)) = 1"
        by (simp flip: cis_divide add: ring_distribs)
      hence "real k / real m - real l / real n \<in> \<int>"
        sorry
      then obtain N where "real k / real m - real l / real n = real_of_int N"
        by (elim Ints_cases)
      hence "0 = real k * real n - real l * real m - real_of_int N * real m * real n"
        using kl by (auto simp add: divide_simps totatives_def)
      also have "\<dots> = real_of_int (int k * int n - int l * int m - N * int m * int n)"
        by simp
      finally have eq: "int k * int n = int l * int m + N * int m * int n"
        by linarith

      have "int m dvd int (k * n)"
        unfolding of_nat_mult by (subst eq) auto
      hence "m dvd k * n"
        using int_dvd_int_iff by blast
      with kl(1) have "m dvd n"
        using Rings.coprime_commute coprime_dvd_mult_right_iff unfolding totatives_def by blast

      moreover have "int n dvd int (l * m)"
        unfolding of_nat_mult using eq by (metis dvd_add_times_triv_right_iff dvd_triv_right)
      hence "n dvd l * m"
        using int_dvd_int_iff by blast
      with kl(2) have "n dvd m"
        using Rings.coprime_commute coprime_dvd_mult_right_iff unfolding totatives_def by blast

      ultimately have "m = n"
        by (rule dvd_antisym)
      thus False using \<open>m \<noteq> n\<close>
        by contradiction
    qed
  qed
  thus ?thesis
    sorry
qed

lemma irreducible_cyclotomic_poly [intro]:
  assumes "n > 0"
  shows   "irreducible (cyclotomic_poly n)"
  sorry

lemma degree_cyclotomic_poly: "degree (cyclotomic_poly n) = totient n"
proof -
  have "degree (cyclotomic_poly n) = degree (of_int_poly (cyclotomic_poly n) :: complex poly)"
    by simp
  also have "\<dots> = totient n"
    unfolding of_int_poly_cyclotomic_poly
    by (subst degree_prod_eq_sum_degree) (auto simp: totient_def)
  finally show ?thesis .
qed

lemma prod_cyclotomic_poly_eq:
  assumes "n > 0"
  shows   "(\<Prod>k | k dvd n. cyclotomic_poly k) = Polynomial.monom 1 n - 1"
proof -
  have "Polynomial.monom 1 n - 1 = (\<Prod>d \<in> {0<..<n} \<inter> {d. d dvd n}. cyclotomic_poly d) * cyclotomic_poly n"
    using prod_cyclotomic_poly_dvd[of n] assms by (subst (2) cyclotomic_poly.simps) simp
  also have "\<dots> = (\<Prod>d \<in> insert n ({0<..<n} \<inter> {d. d dvd n}). cyclotomic_poly d)"
    by (subst prod.insert) auto
  also have "insert n ({0<..<n} \<inter> {d. d dvd n}) = {d. d dvd n}"
    using assms by auto
  finally show ?thesis ..
qed

end