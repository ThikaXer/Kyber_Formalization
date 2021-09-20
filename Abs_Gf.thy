theory Abs_Gf

imports Mod_Plus_Minus
        Kyber_spec

begin


context kyber_spec
begin 
text \<open>We want to show that \<open>abs_infty_q\<close> is a norm induced by the euclidean norm on the mod_ring,
  while \<open>abs_infty_poly\<close> is the induced norm by \<open>abs_infty_q\<close> on polynomials over the polynomial 
  ring over the mod_ring. In explicit, we need the triangular inequalities.\<close>

definition abs_infty_q :: "('a mod_ring) \<Rightarrow> int" where
  "abs_infty_q p = abs ((to_int_mod_ring p) mod+- q)"

definition abs_infty_poly :: "'a gf \<Rightarrow> int" where
  "abs_infty_poly p = Max (range (abs_infty_q \<circ> poly.coeff (of_gf p)))"

text \<open>Helping lemmas and properties of Max, range and finite\<close>

lemma to_int_mod_ring_range: 
  "range (to_int_mod_ring :: 'a mod_ring \<Rightarrow> int) = {0 ..< q}"
using CARD_a by (simp add: range_to_int_mod_ring)

lemma finite_Max:
  "finite (range (\<lambda>xa. abs_infty_q (poly.coeff (of_gf x) xa)))"
proof -
  have finite_range: "finite (range (\<lambda>xa. (poly.coeff (of_gf x) xa)))" 
  using MOST_coeff_eq_0[of "of_gf x"] by auto
  have "range (\<lambda>xa. \<bar>to_int_mod_ring (poly.coeff (of_gf x) xa) mod+- q\<bar>) = 
        (\<lambda>z. \<bar>to_int_mod_ring z mod+- q\<bar>) ` range (poly.coeff (of_gf x))"
  using range_composition[of "(\<lambda>z. abs (to_int_mod_ring z mod+- q))" "poly.coeff (of_gf x)"] 
    by auto
  then show ?thesis 
    using finite_range finite_image_set[where f = "(\<lambda>z. abs (to_int_mod_ring z) mod+- q)" ] 
    by (auto simp add: abs_infty_q_def)
qed

lemma finite_Max_sum: 
  "finite (range (\<lambda>xa. abs_infty_q (poly.coeff (of_gf x) xa + poly.coeff (of_gf y) xa)))"
proof -
  have finite_range: "finite (range (\<lambda>xa. (poly.coeff (of_gf x) xa + poly.coeff (of_gf y) xa)))" 
  using MOST_coeff_eq_0[of "of_gf x"] by auto
  have "range (\<lambda>xa. \<bar>to_int_mod_ring (poly.coeff (of_gf x) xa + poly.coeff (of_gf y) xa) mod+- q\<bar>) = 
        (\<lambda>z. \<bar>to_int_mod_ring z mod+- q\<bar>) ` range (\<lambda>xa. poly.coeff (of_gf x) xa + poly.coeff (of_gf y) xa)"
  using range_composition[of "(\<lambda>z. abs (to_int_mod_ring z mod+- q))" 
    "(\<lambda>xa. poly.coeff (of_gf x) xa + poly.coeff (of_gf y) xa)"] by auto
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
     (\<lambda>xa. abs_infty_q (poly.coeff (of_gf x) xa) + abs_infty_q (poly.coeff (of_gf y) xa)))"
proof -
  have finite_range_x: "finite (range (\<lambda>xa. abs_infty_q (poly.coeff (of_gf x) xa)))" 
    using finite_Max[of x] by auto
  have finite_range_y: "finite (range (\<lambda>xa. abs_infty_q (poly.coeff (of_gf y) xa)))" 
    using finite_Max[of y] by auto
  show ?thesis using finite_range_plus[OF finite_range_x finite_range_y] by auto
qed


lemma all_impl_Max: 
  assumes "\<forall>x. f x \<ge> (0::int)"
          "finite (range f)"
  shows "(MAX x. f x) \<ge> 0"
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

text \<open>Show that abs_infty_q is indeed a norm (definite, positive, triangle inequality)\<close>

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


lemma abs_infty_q_scale:
  "abs_infty_q ((of_int_mod_ring s) * x) = (abs s) * (abs_infty_q x)"
sorry



lemma abs_infty_q_minus:
  "abs_infty_q (- x) = abs_infty_q x"
proof -

  have minus_x: "to_int_mod_ring (-x) = q - to_int_mod_ring x" sorry
  have "abs_infty_q (-x) = abs ((q - to_int_mod_ring x) mod+- q)" 
    unfolding abs_infty_q_def using minus_x by auto
  also have "\<dots> = abs ((- to_int_mod_ring x) mod+- q)" unfolding mod_plus_minus_def
    by (smt (z3) mod_add_self2)
  also have "\<dots> = abs (- (to_int_mod_ring x mod+- q))" unfolding mod_plus_minus_def
    sorry

  also have "\<dots> = abs (to_int_mod_ring x mod+- q)" by auto
  finally show ?thesis unfolding abs_infty_q_def by auto
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

text \<open>Show that abs_infty_poly is indeed a norm (definite, positive, triangle inequality)\<close>

lemma abs_infty_poly_definite:
  "abs_infty_poly x = 0 \<longleftrightarrow> x = 0"
proof (auto simp add: abs_infty_poly_def abs_infty_q_definite)
  assume "(MAX xa. abs_infty_q (poly.coeff (of_gf x) xa)) = 0"
  then have abs_le_zero: "abs_infty_q (poly.coeff (of_gf x) xa) \<le> 0" for xa
    using Max_ge[OF finite_Max[of x], 
      of "abs_infty_q (poly.coeff (of_gf x) xa)"]
    by (auto simp add: Max_ge[OF finite_Max])
  have "abs_infty_q (poly.coeff (of_gf x) xa) = 0" for xa 
    using abs_infty_q_pos[of "poly.coeff (of_gf x) xa"] abs_le_zero[of xa]
    by auto
  then have "poly.coeff (of_gf x) xa = 0" for xa
    by (auto simp add: abs_infty_q_definite)
  then show "x = 0" 
    using leading_coeff_0_iff of_gf_eq_0_iff by blast
qed



lemma abs_infty_poly_pos:
  "abs_infty_poly x \<ge> 0"
proof (auto simp add: abs_infty_poly_def)
  have f_ge_zero: "\<forall>xa. abs_infty_q (poly.coeff (of_gf x) xa) \<ge> 0"
    by (auto simp add: abs_infty_q_pos)
  then show " 0 \<le> (MAX xa. abs_infty_q (poly.coeff (of_gf x) xa))"
    using all_impl_Max[OF f_ge_zero finite_Max] by auto
qed



lemma abs_infty_poly_scale:
  "abs_infty_poly ((to_module s) * x) = (abs s) * (abs_infty_poly x)"
sorry





lemma abs_infty_poly_triangle_ineq:
  "abs_infty_poly (x+y) \<le> abs_infty_poly x + abs_infty_poly y"
proof -
  have "abs_infty_q (poly.coeff (of_gf x) xa + poly.coeff (of_gf y) xa) \<le> 
        abs_infty_q (poly.coeff (of_gf x) xa) + abs_infty_q (poly.coeff (of_gf y) xa)"
    for xa
    using abs_infty_q_triangle_ineq[of "poly.coeff (of_gf x) xa" "poly.coeff (of_gf y) xa"]
    by auto
  then have abs_q_triang: "\<forall>xa. abs_infty_q (poly.coeff (of_gf x) xa + poly.coeff (of_gf y) xa) \<le> 
        abs_infty_q (poly.coeff (of_gf x) xa) + abs_infty_q (poly.coeff (of_gf y) xa)"
    by auto
  have "(MAX xa. abs_infty_q (poly.coeff (of_gf x) xa + poly.coeff (of_gf y) xa))
    \<le> (MAX xa. abs_infty_q (poly.coeff (of_gf x) xa) + abs_infty_q (poly.coeff (of_gf y) xa))"
    using Max_mono'[OF abs_q_triang finite_Max_sum finite_Max_sum'] by auto
  also have "\<dots> \<le> (MAX xa. abs_infty_q (poly.coeff (of_gf x) xa)) +
       (MAX xb. abs_infty_q (poly.coeff (of_gf y) xb))" 
    using Max_mono_plus[OF finite_Max[of x] finite_Max[of y]] by auto
  finally have "(MAX xa. abs_infty_q (poly.coeff (of_gf x) xa + poly.coeff (of_gf y) xa))
    \<le> (MAX xa. abs_infty_q (poly.coeff (of_gf x) xa)) +
       (MAX xb. abs_infty_q (poly.coeff (of_gf y) xb))"
    by auto
  then show ?thesis 
    by (auto simp add: abs_infty_poly_def)
qed







end
end