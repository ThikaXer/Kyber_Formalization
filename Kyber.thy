theory Kyber
imports Main "HOL-Computational_Algebra.Computational_Algebra" "HOL-Computational_Algebra.Polynomial_Factorial"
 "Berlekamp_Zassenhaus.Poly_Mod" "Berlekamp_Zassenhaus.Poly_Mod_Finite_Field"

begin


(* this is the polynomial "X ^ n + 1" *)
definition gf_poly :: "'n itself \<Rightarrow> 'q :: prime_card mod_ring poly" where
  "gf_poly _ = Polynomial.monom 1 CARD('n) + 1"

lemma degree_gf_poly [simp]: "degree (gf_poly TYPE('n :: finite)) = CARD('n)"
  unfolding gf_poly_def by (subst degree_add_eq_left)  (auto simp: degree_monom_eq)

lemma gf_poly_nz [simp]: "gf_poly TYPE('n :: finite) \<noteq> 0"
  using degree_gf_poly[where ?'n = 'n] zero_less_card_finite[where ?'a = 'n]
        degree_0 zero_less_iff_neq_zero by metis

lemma gf_poly_not_one [simp]: "gf_poly TYPE('n :: finite) \<noteq> 1"
  using degree_gf_poly[where ?'n = 'n] zero_less_card_finite[where ?'a = 'n]
        degree_1 zero_less_iff_neq_zero by metis

lemma gf_poly_not_neg_one [simp]: "gf_poly TYPE('n :: finite) \<noteq> -1"
  using degree_gf_poly[where ?'n = 'n] zero_less_card_finite[where ?'a = 'n]
        degree_1 zero_less_iff_neq_zero degree_minus by metis

lemma one_mod_gf_poly [simp]: "1 mod gf_poly TYPE('n :: finite) = 1"
proof -
  have "2 ^ 1 \<le> (2 ^ CARD('n) :: nat)"
    by (intro power_increasing) auto
  thus ?thesis
    by (intro mod_eqI[where q = 0]) (auto simp: euclidean_size_poly_def)
qed

(* FIXME: this doesn't actually hold for all combinations of q and n\<dots> *)
lemma irreducible_gf_poly: "irreducible (gf_poly TYPE('n :: finite))"
  sorry

(*

(* this type corresponds to \<int>q[X] / (X^n + 1) *)

typedef ('q, 'n) gf =
  "{p mod gf_poly TYPE('n) |p. p \<in> (UNIV :: 'q :: prime_card mod_ring poly set)}"
  sorry

setup_lifting type_definition_gf


instantiation gf :: (prime_card, finite) zero
begin

lift_definition zero_gf :: "('q :: prime_card, 'n :: finite) gf"
  is "0 :: 'q :: prime_card mod_ring poly"
  apply (rule exI[of _ 0])
  apply simp
  done

instance ..
end


instantiation gf :: (prime_card, finite) plus
begin

lift_definition plus_gf :: "('q :: prime_card, 'n :: finite) gf \<Rightarrow> ('q, 'n) gf \<Rightarrow> ('q, 'n) gf"
  is "\<lambda>p q. (p + q) mod gf_poly TYPE('n) :: 'q :: prime_card mod_ring poly"
  apply auto
  done

instance ..
end


instantiation gf :: (prime_card, finite) monoid_add
begin

instance sorry
end


lemma
  fixes x y z :: "('q :: prime_card, 'n :: finite) gf"
  shows "x + (y + z) = (x + y) + z"
  apply transfer
  sorry
*)






definition gf_rel :: "'n itself \<Rightarrow> 'q :: prime_card mod_ring poly \<Rightarrow> 'q mod_ring poly \<Rightarrow> bool" where
  "gf_rel _ P Q \<longleftrightarrow> [P = Q] (mod gf_poly TYPE('n))"

lemma equivp_gf_rel: "equivp (gf_rel TYPE('n :: finite))"
  by(intro equivpI sympI reflpI transpI) (auto simp: gf_rel_def cong_sym intro: cong_trans)

quotient_type ('q, 'n) gf = "'q :: prime_card mod_ring poly" / "gf_rel TYPE('n :: finite)"
  by (rule equivp_gf_rel)

(* reduction of a polynomial in \<int>q[X] modulo X^n + 1 *)
lift_definition to_gf :: "'q :: prime_card mod_ring poly \<Rightarrow> ('q, 'n :: finite) gf" 
  is "\<lambda>x. (x :: 'q mod_ring poly)" .

(* canonical representative in \<int>q[X] of an element of GF(q,n) *)
lift_definition of_gf :: "('q :: prime_card, 'n :: finite) gf \<Rightarrow> 'q mod_ring poly" 
  is "\<lambda>P::'q mod_ring poly. P mod gf_poly TYPE('n)"
  by (simp add: gf_rel_def cong_def)

(* analogous: conversion between 'q mod_ring and int *)
term "of_int_mod_ring :: int \<Rightarrow> 'a :: finite mod_ring"
term "to_int_mod_ring :: 'a :: finite mod_ring \<Rightarrow> int"

(* some operations on polynomials *)
term "[:3, 2, 1:] :: real poly" (* entspricht x^2 + 2x + 1 *)
term "Polynomial.monom c n :: real poly" (* entspricht c * x^n *)
term "poly.coeff :: real poly \<Rightarrow> nat \<Rightarrow> real" (* n-ter Koeffizient *)
term poly (* Auswertungshomomorphismus *)
term map_poly (* Wende Funktion f auf alle Koeffizienten an (Vorsicht: f 0 sollte 0 sein *)

find_consts "'a poly"





(* type class instantiations for gf *)

instantiation gf :: (prime_card, finite) comm_ring_1
begin

lift_definition zero_gf :: "('a :: prime_card, 'n :: finite) gf" is "0" .

lift_definition one_gf :: "('a :: prime_card, 'n :: finite) gf" is "1" .

lift_definition plus_gf :: "('a :: prime_card, 'n :: finite) gf \<Rightarrow> ('a, 'n) gf \<Rightarrow> ('a, 'n) gf"
  is "(+)"
  unfolding gf_rel_def using cong_add by blast

lift_definition uminus_gf :: "('a :: prime_card, 'n :: finite) gf \<Rightarrow> ('a, 'n) gf"
  is "uminus"
  unfolding gf_rel_def  using cong_minus_minus_iff by blast

lift_definition minus_gf :: "('a :: prime_card, 'n :: finite) gf \<Rightarrow> ('a, 'n) gf \<Rightarrow> ('a, 'n) gf"
  is "(-)"
  unfolding gf_rel_def using cong_diff by blast

lift_definition times_gf :: "('a :: prime_card, 'n :: finite) gf \<Rightarrow> ('a, 'n) gf \<Rightarrow> ('a, 'n) gf"
  is "(*)"
  unfolding gf_rel_def using cong_mult by blast

instance
proof
  show "0 \<noteq> (1 :: ('a, 'b) gf)"
    by transfer (simp add: gf_rel_def cong_def)
qed (transfer; simp add: gf_rel_def algebra_simps; fail)+

end

(*
lemma (in unique_euclidean_semiring)
  assumes "a * x + b * y = gcd x y"
  shows   "bezout_coefficients x y = (a, b)"
  using assms bezout_coefficients_fst_snd[of x y]
  sledgehammer
  find_theorems bezout_coefficients
proof -
*)

lemma of_gf_0 [simp]: "of_gf 0 = 0"
  and of_gf_1 [simp]: "of_gf 1 = 1"
  and of_gf_uminus [simp]: "of_gf (-p) = -of_gf p"
  and of_gf_add [simp]: "of_gf (p + q) = of_gf p + of_gf q"
  and of_gf_diff [simp]: "of_gf (p - q) = of_gf p - of_gf q"
  by (transfer; simp add: poly_mod_add_left poly_mod_diff_left; fail)+

lemma to_gf_0 [simp]: "to_gf 0 = 0"
  and to_gf_1 [simp]: "to_gf 1 = 1"
  and to_gf_uminus [simp]: "to_gf (-p) = -to_gf p"
  and to_gf_add [simp]: "to_gf (p + q) = to_gf p + to_gf q"
  and to_gf_diff [simp]: "to_gf (p - q) = to_gf p - to_gf q"
  and to_gf_mult [simp]: "to_gf (p * q) = to_gf p * to_gf q"
  by (transfer'; simp; fail)+

lemma to_gf_of_nat [simp]: "to_gf (of_nat n) = of_nat n"
  by (induction n) auto

lemma to_gf_of_int [simp]: "to_gf (of_int n) = of_int n"
  by (induction n) auto

lemma of_gf_of_nat [simp]: "of_gf (of_nat n) = of_nat n"
  by (induction n) auto

lemma of_gf_of_int [simp]: "of_gf (of_int n) = of_int n"
  by (induction n) auto

lemma of_gf_eq_0_iff [simp]: "of_gf p = 0 \<longleftrightarrow> p = 0"
  by transfer (simp add: gf_rel_def cong_def)

lemma to_gf_eq_0_iff:
  "to_gf p = (0 :: ('q :: prime_card, 'n :: finite) gf) \<longleftrightarrow> gf_poly (TYPE('n)) dvd p"
  by transfer (auto simp: gf_rel_def cong_def)


instantiation gf :: (prime_card, finite) inverse
begin

definition inverse_gf :: "('a :: prime_card, 'b :: finite) gf \<Rightarrow> ('a, 'b) gf" where
  "inverse P = to_gf (fst (bezout_coefficients (of_gf P) (gf_poly (TYPE('b)))))"

definition divide_gf :: "('a :: prime_card, 'b :: finite) gf \<Rightarrow> ('a, 'b) gf \<Rightarrow> ('a, 'b) gf" where
  "divide_gf P Q = P * inverse Q"

instance ..

end

instantiation gf :: (prime_card, finite) field
begin

instance proof (standard, goal_cases)
  case (1 z)
  thus ?case
    unfolding inverse_gf_def
  proof transfer
    fix P :: "'a mod_ring poly"
    define Q :: "'a mod_ring poly" where "Q = gf_poly TYPE('b)"
    define B where "B = bezout_coefficients (P mod Q) Q"
    assume "\<not>gf_rel TYPE('b) P 0"
    hence "\<not>Q dvd P"
      by (auto simp: gf_rel_def Q_def cong_def)
    have "[fst B * P + snd B * 0 = fst B * (P mod Q) + snd B * Q] (mod Q)"
      by (intro cong_mult cong_add cong) (auto simp: cong_def)
    also have "fst B * (P mod Q) + snd B * Q = gcd (P mod Q) Q"
      unfolding B_def by (meson bezout_coefficients_fst_snd)
    also have "Rings.coprime Q P"
      using \<open>\<not>Q dvd P\<close> unfolding Q_def
      by (intro prime_elem_imp_coprime irreducible_imp_prime_elem irreducible_gf_poly)
    hence "gcd (P mod Q) Q = 1"
      by (simp add: Q_def gcd.commute)
    finally show "gf_rel TYPE('b) (fst B * P) 1"
      by (simp add: gf_rel_def Q_def)
  qed
next
  show "inverse (0 :: ('a, 'b) gf) = 0"
    by (auto simp: inverse_gf_def bezout_coefficients_left_0)
qed (auto simp: divide_gf_def)

end




(* some more lemmas that will probably be useful *)

lemma to_gf_eq_iff [simp]:
  "to_gf P = (to_gf Q :: ('q :: prime_card, 'n :: finite) gf) \<longleftrightarrow>
   [P = Q] (mod (gf_poly TYPE('n)))"
  by transfer (auto simp: gf_rel_def)

(*
  reduction modulo (X^n + 1) is injective on polynomials of degree < n
  in particular, this means that card(GF(q^n)) = q^n.
*)
lemma inj_on_to_gf:
  "inj_on
     (to_gf :: 'q :: prime_card mod_ring poly \<Rightarrow> ('q, 'n :: finite) gf)
     {P. degree P < CARD('n)}"
  by (intro inj_onI) (auto simp: cong_def mod_poly_less)

(* characteristic of GF is exactly q *)
lemma of_int_mod_ring_eq_0_iff:
  "(of_int n :: ('n :: {finite, nontriv} mod_ring)) = 0 \<longleftrightarrow> int (CARD('n)) dvd n"
  by transfer auto

lemma of_int_mod_ring_eq_of_int_iff:
  "(of_int n :: ('n :: {finite, nontriv} mod_ring)) = of_int m \<longleftrightarrow> [n = m] (mod (int (CARD('n))))"
  by transfer (auto simp: cong_def)

lemma of_int_gf_eq_0_iff [simp]:
  "of_int n = (0 :: ('q :: prime_card, 'n :: finite) gf) \<longleftrightarrow> int (CARD('q)) dvd n"
proof -
  have "of_int n = (0 :: ('q, 'n) gf) \<longleftrightarrow> (of_int n :: 'q mod_ring poly) = 0"
    by (smt (z3) of_gf_eq_0_iff of_gf_of_int)
  also have "\<dots> \<longleftrightarrow> (of_int n :: 'q mod_ring) = 0"
    by (simp add: of_int_poly)
  also have "\<dots> \<longleftrightarrow> int (CARD('q)) dvd n"
    by (simp add: of_int_mod_ring_eq_0_iff)
  finally show ?thesis .
qed

lemma of_int_gf_eq_of_int_iff:
  "of_int n = (of_int m :: ('q :: prime_card, 'n :: finite) gf) \<longleftrightarrow> [n = m] (mod (int (CARD('q))))"
  using of_int_gf_eq_0_iff[of "n - m", where ?'q = 'q and ?'n = 'n]
  by (simp del: of_int_gf_eq_0_iff add: cong_iff_dvd_diff)

lemma of_nat_gf_eq_of_nat_iff:
  "of_nat n = (of_nat m :: ('q :: prime_card, 'n :: finite) gf) \<longleftrightarrow> [n = m] (mod CARD('q))"
  using of_int_gf_eq_of_int_iff[of "int n" "int m"] 
  by (simp add: cong_int_iff)

lemma of_nat_gf_eq_0_iff [simp]:
  "of_nat n = (0 :: ('q :: prime_card, 'n :: finite) gf) \<longleftrightarrow> CARD('q) dvd n"
  using of_int_gf_eq_0_iff[of "int n"] by simp



locale kyber_spec =
fixes n n' q::int
and R R_q
assumes
"n   = 256"
"n'  = 9"
"q   = 7681"
"R   = Z_x"
"R_q = Z_q_x"
assumes "CARD('q :: prime_card) = q"
assumes "CARD('n :: finite) = n"
begin

(* This type corresponds to \<int>q = \<int>/q\<int> *)
typ "'q mod_ring"

(* This type corresponds to \<int>q[X] *)
typ "'q mod_ring poly"

(* This type corresponds to \<int>q[X] / (X^n + 1) *)
typ "('q, 'n) gf"


lemma q_nonzero: "q \<noteq> 0" 
by (smt (verit) kyber_spec_axioms kyber_spec_def)

lemma q_gt_zero: "q>0"
by (smt (verit, best) kyber_spec_axioms kyber_spec_def)

definition "Z_q = range (\<lambda>x. x mod q)"

text \<open>Define the polynomial ring over the integers. \<close>
definition Z_x :: "int poly set" where
"Z_x = UNIV"




text \<open>Define the polynomial ring over the integers modulo 7681, the prime number used in Kyber.\<close>
interpretation poly_mod_q: poly_mod "7681" .

definition Z_q_x :: "int poly set" where
"Z_q_x = range (poly_mod_q.Mp \<circ> Poly)"



text \<open>To define the Compress and Decompress functions, we need some special forms of modulo.\<close>


definition mod_plus_minus :: "int \<Rightarrow> int \<Rightarrow> int" (infixl "mod+-" 70) where 
"m mod+- b = ((m + (q div 2)) mod b) - (q div 2)"  

lemma mod_range: assumes "x \<in> set [0..b-1]" shows "x mod b = x"
using assms by (auto)

text \<open>Compression only works for \<open>x \<in> Z_q\<close> and
outputs an integer in \<open>{0,\<dots> , 2 d − 1}\<close> , where \<open>d < \<lceil>log_2 (q)\<rceil>\<close> .
\<close>

definition compress :: "int \<Rightarrow> nat \<Rightarrow> int" where
"compress x d = round (real_of_int (2 ^ d * x) / real_of_int q) mod (2^d)"

definition decompress :: "int \<Rightarrow> nat \<Rightarrow> int" where
"decompress x d = round (real_of_int q * real_of_int x / real_of_int 2 ^ d)"

lemma range_compress:
assumes 
    "x\<in>{0..q-1}"
    "of_nat d < \<lceil>(log 2 q)::real\<rceil>"
shows "compress x d \<in> {0..2^d - 1}"
using compress_def by auto

lemma decompress_zero: "decompress 0 d = 0"
unfolding decompress_def by auto



lemma compress_in_range:
assumes 
  "x\<in>{0..ceiling (q-(q/2^(d+1)))-1}" 
  "of_nat d < \<lceil>(log 2 q)::real\<rceil>"
shows "round (real_of_int (2 ^ d * x) / real_of_int q) < 2^d " 
proof -
  have "d < log 2 q" using assms(2) by linarith
  have "(2::int)^d \<noteq> 0" by simp
  have "2 powr (real d) < of_int q" using less_log_iff[of 2 q d] \<open>d< log 2 q\<close> q_gt_zero by auto
  then have "real_of_int x < real_of_int q - real_of_int q / (2 * 2 ^ d)" 
    using assms(1) less_ceiling_iff by auto
  then have "2 ^ d * real_of_int x / real_of_int q < 
    2 ^ d * (real_of_int q - real_of_int q / (2 * 2 ^ d)) / real_of_int q"
    using \<open>2 powr (real d) < q\<close> 
    by (simp add: divide_strict_right_mono q_gt_zero)
  also have "\<dots> =  2 ^ d * ((real_of_int q / real_of_int q) - 
                  (real_of_int q / real_of_int q) / (2 * 2 ^ d))"
    using q_nonzero by (simp add:algebra_simps diff_divide_distrib)
  also have "\<dots> =  2^d * (1 - 1/(2*2^d))" using q_nonzero by simp
  also have "\<dots> = 2^d - 1/2" using \<open>2^d \<noteq> 0\<close>
    by (simp add: right_diff_distrib')
  finally have "2 ^ d * real_of_int x / real_of_int q < 2^d - (1::real)/(2::real)" by auto
  then show ?thesis unfolding round_def using floor_less_iff by fastforce
qed 


lemma compress_no_mod:
assumes 
  "x\<in>{0..\<lceil>q-(q / 2^(d+1))\<rceil>-1}" 
  "of_nat d < \<lceil>(log 2 q)::real\<rceil>"
shows "compress x d = round (real_of_int (2 ^ d * x) / real_of_int q)"
 unfolding compress_def using compress_in_range[OF assms] assms(1) 
 by (smt (verit, best) atLeastAtMost_iff div_neg_pos_less0 divide_nonneg_nonneg 
    mod_pos_pos_trivial nonzero_mult_div_cancel_left not_exp_less_eq_0_int 
    of_int_0_le_iff q_gt_zero round_0 round_mono)

lemma compress_2d:
assumes
  "x\<in>{\<lceil>q-(q/2^(d+1))\<rceil>..q-1}" 
  "of_nat d < \<lceil>(log 2 q)::real\<rceil>"
shows "round (real_of_int (2 ^ d * x) / real_of_int q) = 2^d "
using assms proof -
  have "x\<ge>q-(q/2^(d+1))" using assms(1) 
    by (meson atLeastAtMost_iff ceiling_le_iff)
  then have "real_of_int (2 ^ d * x) / real_of_int q \<ge> 
        2 ^ d * (real_of_int q - real_of_int q / 2 ^ (d + 1)) / real_of_int q"
    by (smt (verit, ccfv_SIG) divide_strict_right_mono less_eq_real_def 
    linordered_comm_semiring_strict_class.comm_mult_strict_left_mono of_int_0_less_iff 
    of_int_add of_int_hom.hom_mult of_int_hom.hom_one of_int_power q_gt_zero zero_less_power)
  also have "\<dots> = 2 ^ d * (1 - 1 / 2 ^ (d + 1))" using q_nonzero sorry
  also have "\<dots> = 2^d - 1/2 " sorry
  finally have "real_of_int (2 ^ d * x) / real_of_int q \<ge> 2^d -1/2" sorry
  then have "round (real_of_int (2 ^ d * x) / real_of_int q) \<ge> 2^d" sorry
  moreover have "round (real_of_int (2 ^ d * x) / real_of_int q) \<le> 2^d" sorry
  ultimately show ?thesis by auto
qed

lemma compress_mod:
assumes 
  "x\<in>{\<lceil>q-(q/2^(d+1))\<rceil>..q-1}" 
  "of_nat d < \<lceil>(log 2 q)::real\<rceil>"
shows "compress x d = 0"
unfolding compress_def using compress_2d[OF assms] by simp





lemma decompress_compress_1: 
assumes 
    "x\<in>set [0..\<lceil>q-(q/2^(d+1))\<rceil>-1]"
    "of_nat d < \<lceil>(log 2 q)::real\<rceil>"
shows "abs (decompress (compress x d) d - x) \<le> round ( of_int q / of_int (2^(d+1)) )"
using assms
proof -
  have "d < log 2 q" using assms(2) by linarith
  have "(2::int)^d \<noteq> 0" by simp
  have "2 powr (real d) < of_int q" using less_log_iff[of 2 q d] \<open>d< log 2 q\<close> q_gt_zero by auto

  have "let c_real = real_of_int (2 ^ d * x) / real_of_int q in 
        abs (of_int (compress x d) - c_real) \<le> 1/2"
    using of_int_round_abs_le unfolding compress_def Let_def 
    using mod_range sorry
  have "let d_real = real_of_int q * real_of_int y / real_of_int 2 ^ d in
        abs (of_int (decompress y d) - d_real) \<le> 1/2" if "y \<in> {0.. 2^d-1}" for y 
    using of_int_round_abs_le unfolding decompress_def Let_def by auto
  
  have  "abs (decompress (compress x d) d - x) = abs (decompress)"

  then show ?thesis sorry
qed




lemma decompress_compress: 
assumes 
    "d < \<lceil>(log 2 q)::real\<rceil>"
shows "let x' = decompress (compress x d) d in
       abs ((x' - x) mod+- q) \<le> round ( of_int q / of_int (2^(d+1)) )"
using assms unfolding compress_def decompress_def 
apply (auto simp add: round_def mod_plus_minus_def) 

sorry

find_theorems "_ mod _ " 

fun sample_matrix where
"sample_matrix k rho = TODO"

fun Sample_vector where
"Sample beta_eta_k sigma = TODO"

type seed = int

fun key_gen :: "seed \<Rightarrow> seed \<Rightarrow> vector" where
"key_gen rho sigma = (compress q (A s + e) d_t)
  where A = sample_matrix q k rho 
  and (s,e) = sample_vector beta_eta_k sigma"
















end





end