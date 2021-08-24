theory Kyber_spec
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



locale kyber_spec =
fixes n n' q::int
assumes
"n   = 256"
"n'  = 9"
"q   = 7681"
assumes CARD_a: "int (CARD('a :: gf_spec)) = q"
assumes n_gt_1: "n > 1"
assumes gf_poly'_eq: "gf_poly' TYPE('a) = Polynomial.monom 1 (nat n) + 1"

begin

end
end