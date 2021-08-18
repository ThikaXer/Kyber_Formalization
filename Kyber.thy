theory Kyber
imports Main "HOL-Computational_Algebra.Computational_Algebra" 
  "HOL-Computational_Algebra.Polynomial_Factorial"
  "Berlekamp_Zassenhaus.Poly_Mod" 
  "Berlekamp_Zassenhaus.Poly_Mod_Finite_Field"

begin

lemma of_int_mod_ring_eq_0_iff:
  "(of_int n :: ('n :: {finite, nontriv} mod_ring)) = 0 \<longleftrightarrow> int (CARD('n)) dvd n"
  by transfer auto

lemma of_int_mod_ring_eq_of_int_iff:
  "(of_int n :: ('n :: {finite, nontriv} mod_ring)) = of_int m \<longleftrightarrow> [n = m] (mod (int (CARD('n))))"
  by transfer (auto simp: cong_def)

lemma degree_of_int_poly':
  assumes "of_int (lead_coeff p) \<noteq> (0 :: 'a :: ring_1)"
  shows "degree (of_int_poly p :: 'a poly) = degree p"
proof (intro antisym)
  show "degree (of_int_poly p) \<le> degree p"
    by (intro degree_le) (auto simp: coeff_eq_0)
  show "degree (of_int_poly p :: 'a poly) \<ge> degree p"
    using assms by (intro le_degree) auto
qed



definition mod_poly_rel :: "nat \<Rightarrow> int poly \<Rightarrow> int poly \<Rightarrow> bool" where
  "mod_poly_rel m p q \<longleftrightarrow> (\<forall>n. [poly.coeff p n = poly.coeff q n] (mod (int m)))"

lemma mod_poly_rel_altdef:
  "mod_poly_rel CARD('n :: nontriv) p q \<longleftrightarrow> (of_int_poly p) = (of_int_poly q :: 'n mod_ring poly)"
  by (auto simp: poly_eq_iff mod_poly_rel_def of_int_mod_ring_eq_of_int_iff)

definition mod_poly_is_unit :: "nat \<Rightarrow> int poly \<Rightarrow> bool" where
  "mod_poly_is_unit m p \<longleftrightarrow> (\<exists>r. mod_poly_rel m (p * r) 1)"

lemma mod_poly_is_unit_altdef:
  "mod_poly_is_unit CARD('n :: nontriv) p \<longleftrightarrow> (of_int_poly p :: 'n mod_ring poly) dvd 1"
proof
  assume "mod_poly_is_unit CARD('n) p"
  thus "(of_int_poly p :: 'n mod_ring poly) dvd 1"
    by (auto simp: mod_poly_is_unit_def dvd_def mod_poly_rel_altdef of_int_poly_hom.hom_mult)
next 
  assume "(of_int_poly p :: 'n mod_ring poly) dvd 1"
  then obtain q where q: "(of_int_poly p :: 'n mod_ring poly) * q = 1"
    by auto
  also have "q = of_int_poly (map_poly to_int_mod_ring q)"
    by (simp add: of_int_of_int_mod_ring poly_eqI)
  also have "of_int_poly p * \<dots> = of_int_poly (p * map_poly to_int_mod_ring q)"
    by (simp add: of_int_poly_hom.hom_mult)
  finally show "mod_poly_is_unit CARD('n) p"
    by (auto simp: mod_poly_is_unit_def mod_poly_rel_altdef)
qed

definition mod_poly_irreducible :: "nat \<Rightarrow> int poly \<Rightarrow> bool" where
  "mod_poly_irreducible m Q \<longleftrightarrow>
     \<not>mod_poly_rel m Q 0 \<and>
     \<not>mod_poly_is_unit m Q \<and>
        (\<forall>a b. mod_poly_rel m Q (a * b) \<longrightarrow>
               mod_poly_is_unit m a \<or> mod_poly_is_unit m b)"

lemma of_int_poly_to_int_poly: "of_int_poly (to_int_poly p) = p"
  by (simp add: of_int_of_int_mod_ring poly_eqI)

lemma mod_poly_irreducible_altdef:
  "mod_poly_irreducible CARD('n :: nontriv) p \<longleftrightarrow> irreducible (of_int_poly p :: 'n mod_ring poly)"
proof
  assume "irreducible (of_int_poly p :: 'n mod_ring poly)"
  thus "mod_poly_irreducible CARD('n) p"
    by (auto simp: mod_poly_irreducible_def mod_poly_rel_altdef mod_poly_is_unit_altdef
                   irreducible_def of_int_poly_hom.hom_mult)
next
  assume *: "mod_poly_irreducible CARD('n) p"
  show "irreducible (of_int_poly p :: 'n mod_ring poly)"
    unfolding irreducible_def
  proof (intro conjI impI allI)
    fix a b assume ab: "(of_int_poly p :: 'n mod_ring poly) = a * b"
    have "of_int_poly (map_poly to_int_mod_ring a * map_poly to_int_mod_ring b) =
          of_int_poly (map_poly to_int_mod_ring a) *
          (of_int_poly (map_poly to_int_mod_ring b) :: 'n mod_ring poly)"
      by (simp add: of_int_poly_hom.hom_mult)
    also have "\<dots> = a * b"
      by (simp add: of_int_poly_to_int_poly)
    also have "\<dots> = of_int_poly p"
      using ab by simp
    finally have "(of_int_poly p :: 'n mod_ring poly) = of_int_poly (to_int_poly a * to_int_poly b)" ..
    hence "of_int_poly (to_int_poly a) dvd (1 :: 'n mod_ring poly) \<or> 
           of_int_poly (to_int_poly b) dvd (1 :: 'n mod_ring poly)"
      using * unfolding mod_poly_irreducible_def mod_poly_rel_altdef mod_poly_is_unit_altdef
      by blast
    thus "(a dvd (1 :: 'n mod_ring poly)) \<or> (b dvd (1 :: 'n mod_ring poly))"
      by (simp add: of_int_poly_to_int_poly)
  qed (use * in \<open>auto simp: mod_poly_irreducible_def mod_poly_rel_altdef mod_poly_is_unit_altdef\<close>)
qed
    

class gf_spec = prime_card +
  fixes gf_poly' :: "'a itself \<Rightarrow> int poly"
  assumes irreducible_gf_poly'': "mod_poly_irreducible CARD('a) (gf_poly' TYPE('a))"
  assumes not_dvd_lead_coeff_gf_poly':  "\<not>int CARD('a) dvd lead_coeff (gf_poly' TYPE('a))"

definition gf_poly :: "'a :: gf_spec mod_ring poly" where
  "gf_poly = of_int_poly (gf_poly' TYPE('a))"


definition (in gf_spec) deg_gf :: "'a itself \<Rightarrow> nat" where
  "deg_gf _ = degree (gf_poly' TYPE('a))"

lemma degree_gf_poly': "degree (gf_poly' TYPE('a :: gf_spec)) = deg_gf (TYPE('a))"
  by (simp add: deg_gf_def)

lemma degree_gf_poly:
  "degree (gf_poly :: 'a :: gf_spec mod_ring poly) = deg_gf (TYPE('a))"
  unfolding gf_poly_def using not_dvd_lead_coeff_gf_poly'[where ?'a = 'a]
  by (subst degree_of_int_poly') (auto simp: of_int_mod_ring_eq_0_iff degree_gf_poly')

lemma irreducible_gf_poly: "irreducible gf_poly"
  using irreducible_gf_poly''[where ?'a = 'a]
  unfolding irreducible_def mod_poly_irreducible_altdef gf_poly_def .

lemma deg_gf_pos: "deg_gf TYPE('a :: gf_spec) > 0"
  unfolding degree_gf_poly [symmetric] using irreducible_gf_poly[where ?'a = 'a]
  by (auto intro!: Nat.gr0I)

lemma gf_poly_nz [simp]: "gf_poly \<noteq> 0"
  using deg_gf_pos[where ?'a = 'a] by (auto simp flip: degree_gf_poly)

lemma one_mod_gf_poly [simp]: "1 mod (gf_poly :: 'a :: gf_spec mod_ring poly) = 1"
proof -
  have "2 ^ 1 \<le> (2 ^ deg_gf TYPE('a) :: nat)"
    using deg_gf_pos[where ?'a = 'a] by (intro power_increasing) auto
  thus ?thesis
    by (intro mod_eqI[where q = 0]) (auto simp: euclidean_size_poly_def degree_gf_poly)
qed


definition gf_rel :: "'a :: gf_spec mod_ring poly \<Rightarrow> 'a mod_ring poly \<Rightarrow> bool" where
  "gf_rel P Q \<longleftrightarrow> [P = Q] (mod gf_poly)"

lemma equivp_gf_rel: "equivp gf_rel"
  by (intro equivpI sympI reflpI transpI)
     (auto simp: gf_rel_def cong_sym intro: cong_trans)

quotient_type (overloaded) 'a gf = "'a :: gf_spec mod_ring poly" / gf_rel
  by (rule equivp_gf_rel)

(* reduction of a polynomial in \<int>q[X] modulo X^n + 1 *)
lift_definition to_gf :: "'a :: gf_spec mod_ring poly \<Rightarrow> 'a gf" 
  is "\<lambda>x. (x :: 'q mod_ring poly)" .

(* canonical representative in \<int>q[X] of an element of GF(q,n) *)
lift_definition of_gf :: "'a :: gf_spec gf \<Rightarrow> 'a mod_ring poly" 
  is "\<lambda>P::'a mod_ring poly. P mod gf_poly"
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

instantiation gf :: (gf_spec) comm_ring_1
begin

lift_definition zero_gf :: "'a gf" is "0" .

lift_definition one_gf :: "'a gf" is "1" .

lift_definition plus_gf :: "'a gf \<Rightarrow> 'a gf \<Rightarrow> 'a gf"
  is "(+)"
  unfolding gf_rel_def using cong_add by blast

lift_definition uminus_gf :: "'a gf \<Rightarrow> 'a gf"
  is "uminus"
  unfolding gf_rel_def  using cong_minus_minus_iff by blast

lift_definition minus_gf :: "'a gf \<Rightarrow> 'a gf \<Rightarrow> 'a gf"
  is "(-)"
  unfolding gf_rel_def using cong_diff by blast

lift_definition times_gf :: "'a gf \<Rightarrow> 'a gf \<Rightarrow> 'a gf"
  is "(*)"
  unfolding gf_rel_def using cong_mult by blast

instance
proof
  show "0 \<noteq> (1 :: 'a gf)"
    by transfer (simp add: gf_rel_def cong_def)
qed (transfer; simp add: gf_rel_def algebra_simps; fail)+

end

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
  "to_gf p = 0 \<longleftrightarrow> gf_poly dvd p"
  by transfer (auto simp: gf_rel_def cong_def)


instantiation gf :: (gf_spec) field
begin

definition inverse_gf :: "'a gf \<Rightarrow> 'a gf" where
  "inverse P = to_gf (fst (bezout_coefficients (of_gf P) gf_poly))"

definition divide_gf :: "'a gf \<Rightarrow> 'a gf \<Rightarrow> 'a gf" where
  "divide_gf P Q = P * inverse Q"

instance proof (standard, goal_cases)
  case (1 z)
  thus ?case
    unfolding inverse_gf_def
  proof transfer
    fix P :: "'a mod_ring poly"
    define Q :: "'a mod_ring poly" where "Q = gf_poly"
    define B where "B = bezout_coefficients (P mod Q) Q"
    assume "\<not>gf_rel P 0"
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
    finally show "gf_rel (fst B * P) 1"
      by (simp add: gf_rel_def Q_def)
  qed
next
  show "inverse (0 :: 'a gf) = 0"
    by (auto simp: inverse_gf_def bezout_coefficients_left_0)
qed (auto simp: divide_gf_def)

end




(* some more lemmas that will probably be useful *)

lemma to_gf_eq_iff [simp]:
  "to_gf P = (to_gf Q :: 'a :: gf_spec gf) \<longleftrightarrow> [P = Q] (mod gf_poly)"
  by transfer (auto simp: gf_rel_def)

(*
  reduction modulo (X^n + 1) is injective on polynomials of degree < n
  in particular, this means that card(GF(q^n)) = q^n.
*)
lemma inj_on_to_gf:
  "inj_on
     (to_gf :: 'a :: gf_spec mod_ring poly \<Rightarrow> 'a gf)
     {P. degree P < deg_gf TYPE('a)}"
  by (intro inj_onI) (auto simp: cong_def mod_poly_less simp flip: degree_gf_poly)

(* characteristic of GF is exactly q *)

lemma of_int_gf_eq_0_iff [simp]:
  "of_int n = (0 :: 'a :: gf_spec gf) \<longleftrightarrow> int (CARD('a)) dvd n"
proof -
  have "of_int n = (0 :: 'a gf) \<longleftrightarrow> (of_int n :: 'a mod_ring poly) = 0"
    by (smt (z3) of_gf_eq_0_iff of_gf_of_int)
  also have "\<dots> \<longleftrightarrow> (of_int n :: 'a mod_ring) = 0"
    by (simp add: of_int_poly)
  also have "\<dots> \<longleftrightarrow> int (CARD('a)) dvd n"
    by (simp add: of_int_mod_ring_eq_0_iff)
  finally show ?thesis .
qed

lemma of_int_gf_eq_of_int_iff:
  "of_int n = (of_int m :: 'a :: gf_spec gf) \<longleftrightarrow> [n = m] (mod (int (CARD('a))))"
  using of_int_gf_eq_0_iff[of "n - m", where ?'a = 'a]
  by (simp del: of_int_gf_eq_0_iff add: cong_iff_dvd_diff)

lemma of_nat_gf_eq_of_nat_iff:
  "of_nat n = (of_nat m :: 'a :: gf_spec gf) \<longleftrightarrow> [n = m] (mod CARD('a))"
  using of_int_gf_eq_of_int_iff[of "int n" "int m"] 
  by (simp add: cong_int_iff)

lemma of_nat_gf_eq_0_iff [simp]:
  "of_nat n = (0 :: 'a :: gf_spec gf) \<longleftrightarrow> CARD('a) dvd n"
  using of_int_gf_eq_0_iff[of "int n"] by simp



lemma mod_poly_irreducible_gf_7681_256:
  "mod_poly_irreducible 7681 (Polynomial.monom 1 256 + 1)"
  sorry

locale kyber_spec =
fixes n n' q::int
and R R_q
assumes
"n   = 256"
"n'  = 9"
"q   = 7681"
"R   = Z_x"
"R_q = Z_q_x"
assumes CARD_a: "int (CARD('a :: gf_spec)) = q"
assumes n_gt_1: "n > 1"
assumes gf_poly'_eq: "gf_poly' TYPE('a) = Polynomial.monom 1 (nat n) + 1"

begin

(* 
  an abbreviation for our polynomial so that we don't have to annotate the typ
  all the time
*)
abbreviation "Q \<equiv> (gf_poly :: 'a mod_ring poly)"

(* We know here that gf_poly is "X^n + 1" and that it is irreducible in \<int>q[X]. *)
lemma Q_eq: "Q = (Polynomial.monom 1 (nat n) + 1)"
  by (simp add: of_int_poly_hom.hom_add gf_poly_def gf_poly'_eq)

lemma degree_Q: "degree Q = nat n"
proof -
  have "degree Q = degree (gf_poly' TYPE('a))"
    by (simp add: degree_gf_poly degree_gf_poly')
  also have "\<dots> = nat n"
    unfolding gf_poly'_eq using n_gt_1
    by (simp add: degree_add_eq_left degree_monom_eq)
  finally show ?thesis .
qed

lemma irreducible_Q: "irreducible Q"
  by (fact irreducible_gf_poly)


(* This type corresponds to \<int>q = \<int>/q\<int> *)
typ "'a mod_ring"

(* This type corresponds to \<int>q[X] *)
typ "'a mod_ring poly"

(* This type corresponds to \<int>q[X] / (X^n + 1) *)
typ "'a gf"


lemma q_nonzero: "q \<noteq> 0" 
by (smt (verit) kyber_spec_axioms kyber_spec_def)

lemma q_gt_zero: "q > 0"
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
  "x\<in>{\<lceil>q-(q/(2*2^d))\<rceil>..q-1}" 
  "of_nat d < \<lceil>(log 2 q)::real\<rceil>"
shows "round (real_of_int (2 ^ d * x) / real_of_int q) = 2^d "
using assms proof -
  have "(2::int)^d \<noteq> 0" by simp
  have "x\<ge>q-(q/(2*2^d))" using assms(1) 
    by (meson atLeastAtMost_iff ceiling_le_iff)
  then have "real_of_int (2 ^ d * x) / real_of_int q \<ge> 
        2 ^ d * (real_of_int q - real_of_int q / (2 * 2 ^ d)) / real_of_int q"
    by (smt (verit, ccfv_SIG) divide_strict_right_mono less_eq_real_def 
    linordered_comm_semiring_strict_class.comm_mult_strict_left_mono of_int_0_less_iff 
    of_int_add of_int_hom.hom_mult of_int_hom.hom_one of_int_power q_gt_zero zero_less_power)
  also have "\<dots> =  2 ^ d * ((real_of_int q / real_of_int q) - 
                  (real_of_int q / real_of_int q) / (2 * 2 ^ d))"
    using q_nonzero apply (simp add:algebra_simps diff_divide_distrib) sorry
  also have "\<dots> =  2^d * (1 - 1/(2*2^d))" using q_nonzero by simp
  also have "\<dots> = 2^d - 1/2" using \<open>2^d \<noteq> 0\<close> by (simp add: right_diff_distrib')
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