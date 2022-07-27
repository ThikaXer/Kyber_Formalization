theory Abs_Fr

imports Mod_Plus_Minus
        Kyber_spec

begin


context kyber_spec
begin 
text \<open>We want to show that \<open>abs_infty_q\<close> is a norm induced by the euclidean norm on the \<open>mod_ring\<close>,
  while \<open>abs_infty_poly\<close> is the induced norm by \<open>abs_infty_q\<close> on polynomials over the polynomial 
  ring over the \<open>mod_ring\<close>. In explicit, we need the triangular inequalities.\<close>

definition abs_infty_q :: "('a mod_ring) \<Rightarrow> int" where
  "abs_infty_q p = abs ((to_int_mod_ring p) mod+- q)"

definition abs_infty_poly :: "'a fr \<Rightarrow> int" where
  "abs_infty_poly p = Max (range (abs_infty_q \<circ> poly.coeff (of_fr p)))"

text \<open>Helping lemmas and properties of Max, range and finite\<close>

lemma to_int_mod_ring_range: 
  "range (to_int_mod_ring :: 'a mod_ring \<Rightarrow> int) = {0 ..< q}"
using CARD_a by (simp add: range_to_int_mod_ring)

lemma finite_Max:
  "finite (range (\<lambda>xa. abs_infty_q (poly.coeff (of_fr x) xa)))"
proof -
  have finite_range: "finite (range (\<lambda>xa. (poly.coeff (of_fr x) xa)))" 
  using MOST_coeff_eq_0[of "of_fr x"] by auto
  have "range (\<lambda>xa. \<bar>to_int_mod_ring (poly.coeff (of_fr x) xa) mod+- q\<bar>) = 
        (\<lambda>z. \<bar>to_int_mod_ring z mod+- q\<bar>) ` range (poly.coeff (of_fr x))"
  using range_composition[of "(\<lambda>z. abs (to_int_mod_ring z mod+- q))" "poly.coeff (of_fr x)"] 
    by auto
  then show ?thesis 
    using finite_range finite_image_set[where f = "(\<lambda>z. abs (to_int_mod_ring z) mod+- q)" ] 
    by (auto simp add: abs_infty_q_def)
qed

lemma finite_Max_sum: 
  "finite (range (\<lambda>xa. abs_infty_q (poly.coeff (of_fr x) xa + poly.coeff (of_fr y) xa)))"
proof -
  have finite_range: "finite (range (\<lambda>xa. (poly.coeff (of_fr x) xa + poly.coeff (of_fr y) xa)))" 
  using MOST_coeff_eq_0[of "of_fr x"] by auto
  have "range (\<lambda>xa. \<bar>to_int_mod_ring (poly.coeff (of_fr x) xa + poly.coeff (of_fr y) xa) mod+- q\<bar>) = 
        (\<lambda>z. \<bar>to_int_mod_ring z mod+- q\<bar>) ` range (\<lambda>xa. poly.coeff (of_fr x) xa + poly.coeff (of_fr y) xa)"
  using range_composition[of "(\<lambda>z. abs (to_int_mod_ring z mod+- q))" 
    "(\<lambda>xa. poly.coeff (of_fr x) xa + poly.coeff (of_fr y) xa)"] by auto
  then show ?thesis 
    using finite_range finite_image_set[where f = "(\<lambda>z. abs (to_int_mod_ring z) mod+- q)" ] 
    by (auto simp add: abs_infty_q_def)
qed


lemma finite_range_plus: 
  assumes "finite (range f)"
          "finite (range g)"
  shows "finite (range (\<lambda>x. f x + g x))"
proof -
  have subs: "range (\<lambda>x. (f x, g x)) \<subseteq> range f \<times> range g" by auto
  have cart: "finite (range f \<times> range g)" using assms by auto
  have finite: "finite (range (\<lambda>x. (f x, g x)))" 
    using rev_finite_subset[OF cart subs] .
  have "range (\<lambda>x. f x + g x) = (\<lambda>(a,b). a+b) ` range (\<lambda>x. (f x, g x))"
    using range_composition[of "(\<lambda>(a,b). a+b)" "(\<lambda>x. (f x, g x))"] by auto
  then show ?thesis using finite finite_image_set[where f = "(\<lambda>(a,b). a+b)"] by auto
qed

lemma finite_Max_sum':
  "finite (range
     (\<lambda>xa. abs_infty_q (poly.coeff (of_fr x) xa) + abs_infty_q (poly.coeff (of_fr y) xa)))"
proof -
  have finite_range_x: "finite (range (\<lambda>xa. abs_infty_q (poly.coeff (of_fr x) xa)))" 
    using finite_Max[of x] by auto
  have finite_range_y: "finite (range (\<lambda>xa. abs_infty_q (poly.coeff (of_fr y) xa)))" 
    using finite_Max[of y] by auto
  show ?thesis using finite_range_plus[OF finite_range_x finite_range_y] by auto
qed


lemma all_impl_Max: 
  assumes "\<forall>x. f x \<ge> (a::int)"
          "finite (range f)"
  shows "(MAX x. f x) \<ge> a"
by (simp add: Max_ge_iff assms(1) assms(2))


lemma Max_mono':
  assumes "\<forall>x. f x \<le> g x"
          "finite (range f)"
          "finite (range g)"
  shows "(MAX x. f x) \<le> (MAX x. g x)"
using assms 
by (metis (no_types, lifting) Max_ge_iff Max_in UNIV_not_empty image_is_empty rangeE rangeI)  

lemma Max_mono_plus:
  assumes "finite (range (f::_\<Rightarrow>_::ordered_ab_semigroup_add))" 
          "finite (range g)"
  shows "(MAX x. f x + g x) \<le> (MAX x. f x) + (MAX x. g x)"
proof -
  obtain xmax where xmax_def: "f xmax + g xmax = (MAX x. f x + g x)" 
    using finite_range_plus[OF assms] Max_in by fastforce
  have "(MAX x. f x + g x) = f xmax + g xmax" using xmax_def by auto
  also have "\<dots> \<le> (MAX x. f x) + g xmax" 
    using Max_ge[OF assms(1), of "f xmax"] 
    by (auto simp add: add_right_mono[of "f xmax"]) 
  also have "\<dots> \<le> (MAX x. f x) + (MAX x. g x)" 
    using Max_ge[OF assms(2), of "g xmax"]
    by (auto simp add: add_left_mono[of "g xmax"])
  finally show ?thesis by auto
qed

text \<open>Show that \<open>abs_infty_q\<close> is indeed a norm (definite, positive, triangle inequality)\<close>

lemma abs_infty_q_definite:
  "abs_infty_q x = 0 \<longleftrightarrow> x = 0"
proof (auto simp add: abs_infty_q_def mod_plus_minus_zero'[OF q_gt_zero q_odd])
  assume "to_int_mod_ring x mod+- q = 0"
  then have "to_int_mod_ring x mod q = 0" 
    using mod_plus_minus_zero[of "to_int_mod_ring x" q] by auto
  then have "to_int_mod_ring x = 0" 
    using to_int_mod_ring_range CARD_a
    by (metis mod_rangeE range_eqI)
  then show "x = 0" by force
qed

lemma abs_infty_q_pos:
  "abs_infty_q x \<ge> 0"
by (auto simp add: abs_infty_q_def) 


lemma abs_infty_q_minus:
  "abs_infty_q (- x) = abs_infty_q x"
proof (cases "x=0")
case True
  then show ?thesis by auto
next
case False
  have minus_x: "to_int_mod_ring (-x) = q - to_int_mod_ring x"
  proof -
    have "to_int_mod_ring (-x) = to_int_mod_ring (-x) mod q"
      by (metis CARD_a Rep_mod_ring_mod to_int_mod_ring.rep_eq)
    also have "\<dots> = (- to_int_mod_ring x) mod q" 
      by (metis (no_types, opaque_lifting) CARD_a diff_eq_eq mod_add_right_eq 
        plus_mod_ring.rep_eq to_int_mod_ring.rep_eq uminus_add_conv_diff)
    also have "\<dots> = q - to_int_mod_ring x" 
    proof -
      have "- to_int_mod_ring x \<in> {-q<..<0}"
      using CARD_a range_to_int_mod_ring False 
        by (smt (verit, best) Rep_mod_ring_mod greaterThanLessThan_iff q_gt_zero 
          to_int_mod_ring.rep_eq to_int_mod_ring_hom.eq_iff to_int_mod_ring_hom.hom_zero 
          zmod_trivial_iff)
      then have "q-to_int_mod_ring x\<in>{0<..<q}" by auto
      then show ?thesis 
        using minus_mod_self1 mod_rangeE
        by (simp add: to_int_mod_ring.rep_eq zmod_zminus1_eq_if)
    qed
    finally show ?thesis by auto
  qed
  then have "\<bar>to_int_mod_ring (- x) mod+- q\<bar> = \<bar>(q - (to_int_mod_ring x)) mod+- q\<bar>" 
    by auto
  also have "\<dots> = \<bar> (- to_int_mod_ring x) mod+- q\<bar>" 
    unfolding mod_plus_minus_def by (smt (z3) mod_add_self2)
  also have "\<dots> = \<bar> - (to_int_mod_ring x mod+- q)\<bar>" 
    using neg_mod_plus_minus[OF q_odd q_gt_zero, of "to_int_mod_ring x"] by simp
  also have "\<dots> = \<bar>to_int_mod_ring x mod+- q\<bar>" by auto
  finally show ?thesis unfolding abs_infty_q_def by auto
qed



lemma to_int_mod_ring_mult:
  "to_int_mod_ring (a*b) = 
    to_int_mod_ring (a::'a mod_ring) * to_int_mod_ring (b::'a mod_ring) mod q"
by (metis (no_types, lifting) CARD_a of_int_hom.hom_mult of_int_mod_ring.rep_eq 
    of_int_mod_ring_to_int_mod_ring of_int_of_int_mod_ring to_int_mod_ring.rep_eq)

lemma mod_plus_minus_mult: 
  "s*x mod+- q = (s mod+- q) * (x mod+- q) mod+- q"
unfolding mod_plus_minus_def
by (smt (verit, del_insts) mod_add_eq mod_diff_left_eq mod_mult_left_eq mod_mult_right_eq)

(*Scaling only with inequality not equality! This causes a problem in proof of scheme.
  Need to add q=1mod4 to change proof*)
lemma mod_plus_minus_leq_mod: 
  "\<bar>x mod+- q\<bar> \<le> \<bar>x\<bar>"
by (smt (verit, best) atLeastAtMost_iff mod_plus_minus_range mod_plus_minus_rangeE' q_gt_zero q_odd)

lemma abs_infty_q_scale_pos:
  assumes "s\<ge>0"
  shows "abs_infty_q ((of_int_mod_ring s :: 'a mod_ring) * x) \<le> \<bar>s\<bar> * (abs_infty_q x)"
proof -
  have "\<bar>to_int_mod_ring (of_int_mod_ring s * x) mod+- q\<bar> = 
        \<bar>(to_int_mod_ring (of_int_mod_ring s ::'a mod_ring) * to_int_mod_ring x mod q) mod+- q\<bar>"
    using to_int_mod_ring_mult[of "of_int_mod_ring s" x] by simp
  also have "\<dots> = \<bar>(s mod q * to_int_mod_ring x) mod+- q\<bar>" 
    by (metis CARD_a mod_add_left_eq mod_plus_minus_def of_int_mod_ring.rep_eq 
      to_int_mod_ring.rep_eq)
  also have "\<dots> \<le> \<bar>s mod q\<bar> * \<bar>to_int_mod_ring x mod+- q\<bar>" 
  proof -
    have "\<bar>s mod q * to_int_mod_ring x mod+- q\<bar> = 
          \<bar>(s mod q mod+- q) * (to_int_mod_ring x mod+- q) mod+- q\<bar>"
      using mod_plus_minus_mult by auto
    also have "\<dots> \<le> \<bar>(s mod q mod+- q) * (to_int_mod_ring x mod+- q)\<bar>" 
      using mod_plus_minus_leq_mod by blast
    also have "\<dots> \<le> \<bar>s mod q mod+- q\<bar> * \<bar>(to_int_mod_ring x mod+- q)\<bar>" 
      by (simp add: abs_mult)
    also have "\<dots> \<le> \<bar>s mod q\<bar> * \<bar>(to_int_mod_ring x mod+- q)\<bar>"
      using mod_plus_minus_leq_mod[of "s mod q"] by (simp add: mult_right_mono)
    finally show ?thesis by auto
  qed 
  also have "\<dots> \<le> \<bar>s\<bar> * \<bar>to_int_mod_ring x mod+- q\<bar>" using assms
    by (simp add: mult_mono' q_gt_zero zmod_le_nonneg_dividend)
  finally show ?thesis unfolding abs_infty_q_def by auto
qed

lemma abs_infty_q_scale_neg:
  assumes "s<0"
  shows "abs_infty_q ((of_int_mod_ring s :: 'a mod_ring) * x) \<le> \<bar>s\<bar> * (abs_infty_q x)"
using abs_infty_q_minus abs_infty_q_scale_pos 
by (smt (verit, best) mult_minus_left of_int_minus of_int_of_int_mod_ring)

lemma abs_infty_q_scale:
  "abs_infty_q ((of_int_mod_ring s :: 'a mod_ring) * x) \<le> \<bar>s\<bar> * (abs_infty_q x)"
apply (cases "s\<ge>0") 
using abs_infty_q_scale_pos apply presburger 
using abs_infty_q_scale_neg by force


(*
lemma abs_infty_q_ineq_1:
assumes "a = 1"
shows "abs_infty_q (of_int_mod_ring (round((real_of_int q)/2)) * a) \<ge> 
              2 * round (real_of_int q / 4)"
proof -
  have "abs_infty_q (of_int_mod_ring (round((real_of_int q)/2)) * a) =
        abs_infty_q (of_int_mod_ring (round((real_of_int q)/2))::'a mod_ring)"
  using assms by simp
  also have "\<dots> = \<bar>round((real_of_int q)/2) mod+- q\<bar>"
    unfolding abs_infty_q_def using to_int_mod_ring_of_int_mod_ring CARD_a
    by (simp add: assms mod_add_left_eq mod_plus_minus_def of_int_mod_ring.rep_eq 
      to_int_mod_ring.rep_eq)
  also have "\<dots> = \<bar>\<lfloor>(real_of_int q)/2\<rfloor>\<bar>" unfolding mod_plus_minus_def round_def 
    by (simp add: q_def)
  also have "\<dots> = 2 * round (real_of_int q / 4)" by (simp add: q_def round_def)
  finally show "abs_infty_q (of_int_mod_ring (round((real_of_int q)/2)) * a) \<ge> 
              2 * round (real_of_int q / 4)" by simp
qed

lemma abs_infty_q_ineq_minus_1:
assumes "a = -1"
shows "abs_infty_q (of_int_mod_ring (round((real_of_int q)/2)) * a) \<ge> 
              2 * round (real_of_int q / 4)"
proof -
  have "abs_infty_q (of_int_mod_ring (round((real_of_int q)/2)) * a) = 
        abs_infty_q (of_int_mod_ring (round((real_of_int q)/2)) * (-a))"
  using abs_infty_q_minus by simp
  then show ?thesis using abs_infty_q_ineq_1[of "-a"] using assms by auto
qed
*)

lemma of_fr_mult:
  "of_fr (a * b) = of_fr a * of_fr b mod fr_poly"
by (metis of_fr_to_fr to_fr_mult to_fr_of_fr)

lemma of_fr_scale:
  "of_fr (to_module s * b) = Polynomial.smult (of_int_mod_ring s) (of_fr b)"
unfolding to_module_def
  by (auto simp add: of_fr_mult[of "to_fr [:of_int_mod_ring s:]" "b"] of_fr_to_fr) 
     (simp add: mod_mult_left_eq mod_smult_left of_fr.rep_eq)

lemma to_module_mult:
  "poly.coeff (of_fr (to_module s * a)) x1 = 
   of_int_mod_ring (s) * poly.coeff (of_fr a) x1"
using of_fr_scale[of s a] by simp

lemma odd_round_up:
assumes "odd x"
shows "round (real_of_int x / 2) = (x+1) div 2"
proof -
  have "round (real_of_int x / 2) = round (real_of_int (x+1) /2)"
    using assms unfolding round_def 
    by (metis (no_types, opaque_lifting) add.commute add_divide_distrib even_add even_succ_div_2 
    floor_divide_of_int_eq odd_one of_int_add of_int_hom.hom_one of_int_numeral)
  also have "\<dots> = (x+1) div 2"
    by (metis add_divide_distrib calculation floor_divide_of_int_eq of_int_add of_int_hom.hom_one 
    of_int_numeral round_def)
  finally show ?thesis by blast
qed

lemma floor_unique:
assumes "real_of_int a \<le> x" "x < a+1"
shows "floor x = a"
  using assms(1) assms(2) by linarith

lemma same_floor:
assumes "real_of_int a \<le> x" "real_of_int a \<le> y" "x < a+1" "y < a+1"
shows "floor x = floor y"
using assms floor_unique  by presburger

lemma one_mod_four_round:
assumes "x mod 4 = 1"
shows "round (real_of_int x / 4) = (x-1) div 4"
proof -
  have leq: "(x-1) div 4 \<le> real_of_int x / 4  + 1 / 2"
    using assms by linarith 
  have gr: "real_of_int x / 4  + 1 / 2 < (x-1) div 4 + 1" 
  proof -
    have "x+2 < 4 * ((x-1) div 4 + 1)" 
    proof -
      have *:  "(x-1) div 4 + 1 = (x+3) div 4" by auto
      have "4 dvd x + 3" using assms by presburger
      then have "4 * ((x+3) div 4) = x+3" by (subst dvd_imp_mult_div_cancel_left, auto)
      then show ?thesis unfolding * by auto
    qed
    then show ?thesis by auto
  qed
  show "round (real_of_int x / 4) = (x-1) div 4"
    using floor_unique[OF leq gr] unfolding round_def by auto
qed

lemma odd_half_floor:
assumes "odd x"
shows "\<lfloor>real_of_int x / 2\<rfloor> = (x-1) div 2"
using assms 
  by (metis add.commute diff_add_cancel even_add even_succ_div_2 floor_divide_of_int_eq 
  odd_one of_int_numeral)



lemma abs_infty_poly_ineq_pm_1:
assumes "\<exists>x. poly.coeff (of_fr a) x \<in> {of_int_mod_ring (-1),1}"
shows "abs_infty_poly (to_module (round((real_of_int q)/2)) * a) \<ge> 
              2 * round (real_of_int q / 4)"
proof -
  let ?x = "to_module (round((real_of_int q)/2)) * a"
  obtain x1 where x1_def: "poly.coeff (of_fr a) x1 \<in> {of_int_mod_ring(-1),1}" using assms by auto
  have "abs_infty_poly (to_module (round((real_of_int q)/2)) * a)
        \<ge> abs_infty_q (poly.coeff (of_fr (to_module (round (real_of_int q / 2)) * a)) x1)" 
    unfolding abs_infty_poly_def using x1_def by (simp add: finite_Max)
  also have "abs_infty_q (poly.coeff (of_fr (to_module (round (real_of_int q / 2)) * a)) x1)
             = abs_infty_q (of_int_mod_ring (round (real_of_int q / 2))
                  * (poly.coeff (of_fr a) x1))" 
    using to_module_mult[of "round (real_of_int q / 2)" a] by simp
  also have "\<dots> = abs_infty_q (of_int_mod_ring (round (real_of_int q / 2)))" 
  proof -
    consider "poly.coeff (of_fr a) x1=1" | "poly.coeff (of_fr a) x1 = of_int_mod_ring (-1)" 
      using x1_def by auto
    then show ?thesis 
    proof (cases)
      case 2
      then show ?thesis
      by (metis abs_infty_q_minus mult.right_neutral mult_minus_right 
          of_int_hom.hom_one of_int_minus of_int_of_int_mod_ring)
    qed (auto)
  qed
  also have "\<dots> = \<bar>round (real_of_int q / 2) mod+- q\<bar>" 
    unfolding abs_infty_q_def using to_int_mod_ring_of_int_mod_ring 
    by (simp add: CARD_a mod_add_left_eq mod_plus_minus_def of_int_mod_ring.rep_eq 
      to_int_mod_ring.rep_eq)
  also have "\<dots> = \<bar>((q + 1) div 2) mod+- q\<bar>" using odd_round_up[OF q_odd] by auto 
  also have "\<dots> = \<bar>((2 * q) div 2) mod q - (q - 1) div 2\<bar>" 
    unfolding mod_plus_minus_def odd_half_floor[OF q_odd] using q_odd 
    by (smt (verit, ccfv_SIG) even_plus_one_iff even_succ_div_2 odd_two_times_div_two_succ)
  also have "\<dots> = \<bar>(q-1) div 2\<bar>" using q_odd 
    by (subst nonzero_mult_div_cancel_left[of 2 q], simp) 
       (simp add: abs_div abs_minus_commute)
  also have "\<dots> = 2 * ((q-1) div 4)" 
  proof -
    have "(q-1) div 2 > 0" by (simp add: div_positive_int q_gt_two)
    then have "\<bar>(q-1) div 2\<bar> = (q-1) div 2" by auto
    also have "\<dots> = 2 * ((q-1) div 4)" 
      by (subst div_mult_swap) (use q_mod_4 in \<open>metis dvd_minus_mod\<close>, force)
    finally show ?thesis by blast
  qed
  also have "\<dots> = 2 * round (real_of_int q / 4)" 
    unfolding odd_round_up[OF q_odd] one_mod_four_round[OF q_mod_4] by (simp add: round_def)
  finally show ?thesis unfolding abs_infty_poly_def by simp
qed



lemma abs_infty_q_triangle_ineq:
  "abs_infty_q (x+y) \<le> abs_infty_q x + abs_infty_q y"
proof -
  have "to_int_mod_ring (x + y) mod+- q = 
        (to_int_mod_ring x + to_int_mod_ring y) mod q mod+-q"
    by (simp add: to_int_mod_ring_def CARD_a plus_mod_ring.rep_eq)
  also have "\<dots> = (to_int_mod_ring x + to_int_mod_ring y) mod+-q"
    unfolding mod_plus_minus_def by presburger
  also have "\<dots> = (to_int_mod_ring x mod+- q + to_int_mod_ring y mod+- q) mod+- q"
    unfolding mod_plus_minus_def 
    by (smt (verit, ccfv_threshold) mod_add_eq mod_diff_left_eq)
  finally have rewrite:"to_int_mod_ring (x + y) mod+- q = 
    (to_int_mod_ring x mod+- q + to_int_mod_ring y mod+- q) mod+- q" .
  then have "\<bar>to_int_mod_ring (x + y) mod+- q\<bar>
    \<le> \<bar>to_int_mod_ring x mod+- q\<bar> + \<bar>to_int_mod_ring y mod+- q\<bar>"
    proof (cases "(to_int_mod_ring x mod+- q + to_int_mod_ring y mod+- q) \<in> 
                  {-\<lfloor>real_of_int q/2\<rfloor>..<\<lfloor>real_of_int q/2\<rfloor>}")
    case True
      then have "(to_int_mod_ring x mod+- q + to_int_mod_ring y mod+- q) mod+- q
                 = to_int_mod_ring x mod+- q + to_int_mod_ring y mod+- q" 
        using mod_plus_minus_rangeE[OF True q_odd] by auto 
      then show ?thesis by (simp add: rewrite)
    next
    case False
      then have "\<bar>(to_int_mod_ring x mod+- q + to_int_mod_ring y mod+- q)\<bar> \<ge> \<lfloor>real_of_int q /2\<rfloor>" 
        by auto
      then have "\<bar>(to_int_mod_ring x mod+- q + to_int_mod_ring y mod+- q)\<bar> \<ge> 
        \<bar>(to_int_mod_ring x mod+- q + to_int_mod_ring y mod+- q) mod+- q\<bar>"
      using mod_plus_minus_range[OF q_gt_zero, 
            of "(to_int_mod_ring x mod+- q + to_int_mod_ring y mod+- q)"]
      by auto
      then show ?thesis by (simp add: rewrite)
    qed
  then show ?thesis 
    by (auto simp add: abs_infty_q_def mod_plus_minus_def)
qed

text \<open>Show that \<open>abs_infty_poly\<close> is indeed a norm (definite, positive, triangle inequality)\<close>

lemma abs_infty_poly_definite:
  "abs_infty_poly x = 0 \<longleftrightarrow> x = 0"
proof (auto simp add: abs_infty_poly_def abs_infty_q_definite)
  assume "(MAX xa. abs_infty_q (poly.coeff (of_fr x) xa)) = 0"
  then have abs_le_zero: "abs_infty_q (poly.coeff (of_fr x) xa) \<le> 0" for xa
    using Max_ge[OF finite_Max[of x], 
      of "abs_infty_q (poly.coeff (of_fr x) xa)"]
    by (auto simp add: Max_ge[OF finite_Max])
  have "abs_infty_q (poly.coeff (of_fr x) xa) = 0" for xa 
    using abs_infty_q_pos[of "poly.coeff (of_fr x) xa"] abs_le_zero[of xa]
    by auto
  then have "poly.coeff (of_fr x) xa = 0" for xa
    by (auto simp add: abs_infty_q_definite)
  then show "x = 0" 
    using leading_coeff_0_iff of_fr_eq_0_iff by blast
qed



lemma abs_infty_poly_pos:
  "abs_infty_poly x \<ge> 0"
proof (auto simp add: abs_infty_poly_def)
  have f_ge_zero: "\<forall>xa. abs_infty_q (poly.coeff (of_fr x) xa) \<ge> 0"
    by (auto simp add: abs_infty_q_pos)
  then show " 0 \<le> (MAX xa. abs_infty_q (poly.coeff (of_fr x) xa))"
    using all_impl_Max[OF f_ge_zero finite_Max] by auto
qed

(*
(* Problem: Scaling is only true for inequality not necessarily equality! 
  Thus proof as before does not work out. Need to change proof, and add q=1 mod 4*)
lemma abs_infty_poly_scale:
  "abs_infty_poly ((to_module s) * x) = (abs s) * (abs_infty_poly x)"
apply (auto simp add: abs_infty_poly_def)oops


lemma mod_plus_minus_alt_def:
  "x mod+- q = x - q * round (real_of_int x / real_of_int q)"
oops

lemma q_odd_round_half: "round (real_of_int q / 2) = (q+1) div 2"
by (simp add: round_def q_def)


lemma abs_infty_q_scale':
  "abs_infty_q (of_int_mod_ring (round (real_of_int q / 2)) * x) =
    \<bar>round (real_of_int q / 2)\<bar> * abs_infty_q x"
proof -
  have "abs_infty_q (of_int_mod_ring (round (real_of_int q / 2)) * x) =
        abs_infty_q (of_int_mod_ring ((q+1) div 2) * x)" using q_odd_round_half by simp
  also have "\<dots> = \<bar>(to_int_mod_ring (of_int_mod_ring ((q+1) div 2)::'a mod_ring))*
                    (to_int_mod_ring x) mod q mod+- q\<bar>" 
    unfolding abs_infty_q_def using to_int_mod_ring_mult[of "of_int_mod_ring ((q + 1) div 2)" "x"]
    by simp
  also have "\<dots> = \<bar> ((q+1) div 2) * (to_int_mod_ring x) mod q mod+- q\<bar>" 
    using to_int_mod_ring_of_int_mod_ring
    by (simp add: CARD_a mod_mult_right_eq mult.commute of_int_mod_ring.rep_eq 
      to_int_mod_ring.rep_eq)
  also have "\<dots> = \<bar> ((q+1) div 2) * (to_int_mod_ring x) mod+- q\<bar>" 
  also have "\<dots> =  \<bar>round (real_of_int q / 2)\<bar> * abs_infty_q x" unfolding abs_infty_q_def
unfolding abs_infty_q_def mod_plus_minus_def oops

lemma abs_infty_poly_scale':
  "abs_infty_poly (to_module (round (real_of_int q / 2)) * x) =
    \<bar>round (real_of_int q / 2)\<bar> * abs_infty_poly x"
proof -
  have "abs_infty_poly (to_module (round (real_of_int q / 2)) * x) =
        abs_infty_poly (to_module (\<lceil>real_of_int q/2\<rceil>) * x)" using q_odd_round_half by simp
  also have "\<dots> = \<bar>round (real_of_int q / 2)\<bar> * abs_infty_poly x" unfolding abs_infty_poly_def

unfolding abs_infty_poly_def oops
*)


lemma abs_infty_poly_triangle_ineq:
  "abs_infty_poly (x+y) \<le> abs_infty_poly x + abs_infty_poly y"
proof -
  have "abs_infty_q (poly.coeff (of_fr x) xa + poly.coeff (of_fr y) xa) \<le> 
        abs_infty_q (poly.coeff (of_fr x) xa) + abs_infty_q (poly.coeff (of_fr y) xa)"
    for xa
    using abs_infty_q_triangle_ineq[of "poly.coeff (of_fr x) xa" "poly.coeff (of_fr y) xa"]
    by auto
  then have abs_q_triang: "\<forall>xa. abs_infty_q (poly.coeff (of_fr x) xa + poly.coeff (of_fr y) xa) \<le> 
        abs_infty_q (poly.coeff (of_fr x) xa) + abs_infty_q (poly.coeff (of_fr y) xa)"
    by auto
  have "(MAX xa. abs_infty_q (poly.coeff (of_fr x) xa + poly.coeff (of_fr y) xa))
    \<le> (MAX xa. abs_infty_q (poly.coeff (of_fr x) xa) + abs_infty_q (poly.coeff (of_fr y) xa))"
    using Max_mono'[OF abs_q_triang finite_Max_sum finite_Max_sum'] by auto
  also have "\<dots> \<le> (MAX xa. abs_infty_q (poly.coeff (of_fr x) xa)) +
       (MAX xb. abs_infty_q (poly.coeff (of_fr y) xb))" 
    using Max_mono_plus[OF finite_Max[of x] finite_Max[of y]] by auto
  finally have "(MAX xa. abs_infty_q (poly.coeff (of_fr x) xa + poly.coeff (of_fr y) xa))
    \<le> (MAX xa. abs_infty_q (poly.coeff (of_fr x) xa)) +
       (MAX xb. abs_infty_q (poly.coeff (of_fr y) xb))"
    by auto
  then show ?thesis 
    by (auto simp add: abs_infty_poly_def)
qed







end
end