theory Kyber_spec
imports Main "HOL-Computational_Algebra.Computational_Algebra" 
  "HOL-Computational_Algebra.Polynomial_Factorial"
  "Berlekamp_Zassenhaus.Poly_Mod" 
  "Berlekamp_Zassenhaus.Poly_Mod_Finite_Field"

begin
section \<open>Type class for factorial ring $\mathbb{Z}_q[x]/(x^n+1)$.\<close>
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

text \<open>Modulo relation between two polynomials \<close>

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
    
text \<open>Type class for factorial ring $\mathbb{Z}_q[x]/(p)$. 
  The polynomial p is represented as \<open>fr_poly'\<close> (an polynomial over the integers).\<close>

class fr_spec = prime_card +
  fixes fr_poly' :: "'a itself \<Rightarrow> int poly"
  assumes not_dvd_lead_coeff_fr_poly':  "\<not>int CARD('a) dvd lead_coeff (fr_poly' TYPE('a))"
    and deg_fr'_pos : "degree (fr_poly' TYPE('a)) > 0"

text \<open>\<open>fr_poly\<close> is the respecive polynomial in $\mathbb{Z}_q[x]$.\<close>
definition fr_poly :: "'a :: fr_spec mod_ring poly" where
  "fr_poly = of_int_poly (fr_poly' TYPE('a))"

text \<open>Functions to get the degree of the polynomials to be factored out.\<close>
definition (in fr_spec) deg_fr :: "'a itself \<Rightarrow> nat" where
  "deg_fr _ = degree (fr_poly' TYPE('a))"

lemma degree_fr_poly': "degree (fr_poly' TYPE('a :: fr_spec)) = deg_fr (TYPE('a))"
  by (simp add: deg_fr_def)

lemma degree_fr_poly:
  "degree (fr_poly :: 'a :: fr_spec mod_ring poly) = deg_fr (TYPE('a))"
  unfolding fr_poly_def using not_dvd_lead_coeff_fr_poly'[where ?'a = 'a]
  by (subst degree_of_int_poly') (auto simp: of_int_mod_ring_eq_0_iff degree_fr_poly')

lemma deg_fr_pos : "deg_fr TYPE('a :: fr_spec) > 0"
by (metis deg_fr'_pos degree_fr_poly')

text \<open>The factor polynomial is non-zero.\<close>
lemma fr_poly_nz [simp]: "fr_poly \<noteq> 0"
  using deg_fr_pos[where ?'a = 'a] by (auto simp flip: degree_fr_poly)

text \<open>Thus, when factoring out $p$, it has no effect on the neutral element $1$.\<close>
lemma one_mod_fr_poly [simp]: "1 mod (fr_poly :: 'a :: fr_spec mod_ring poly) = 1"
proof -
  have "2 ^ 1 \<le> (2 ^ deg_fr TYPE('a) :: nat)"
    using deg_fr_pos[where ?'a = 'a] by (intro power_increasing) auto
  thus ?thesis
    by (intro mod_eqI[where q = 0]) (auto simp: euclidean_size_poly_def degree_fr_poly)
qed

text \<open>We define a modulo relation for polynomials modulo a polynomial $p=$\<open>fr_poly\<close>.\<close>
definition fr_rel :: "'a :: fr_spec mod_ring poly \<Rightarrow> 'a mod_ring poly \<Rightarrow> bool" where
  "fr_rel P Q \<longleftrightarrow> [P = Q] (mod fr_poly)"

lemma equivp_fr_rel: "equivp fr_rel"
  by (intro equivpI sympI reflpI transpI)
     (auto simp: fr_rel_def cong_sym intro: cong_trans)

text \<open>Using this equivalence relation, we can define the factorial ring as a \<open>quotient_type\<close>.\<close>
quotient_type (overloaded) 'a fr = "'a :: fr_spec mod_ring poly" / fr_rel
  by (rule equivp_fr_rel)

(*Changed from "\<lambda>x. (x :: 'q mod_ring poly)" *)


(* reduction of a polynomial in \<int>q[X] modulo X^n + 1 *)
lift_definition to_fr :: "'a :: fr_spec mod_ring poly \<Rightarrow> 'a fr" 
  is "\<lambda>x. (x :: 'a mod_ring poly)" .

(*Is this correct?? Before:
of_fr :: "'a :: fr_spec fr \<Rightarrow> 'a mod_ring poly" 
*)


(* canonical representative in \<int>q[X] of an element of GF(q,n) *)
lift_definition of_fr :: "'a fr \<Rightarrow> 'a :: fr_spec mod_ring poly" 
  is "\<lambda>P::'a mod_ring poly. P mod fr_poly"
  by (simp add: fr_rel_def cong_def)


lemma of_fr_to_fr: "of_fr (to_fr (x)) = x mod fr_poly"
  apply (auto simp add: of_fr_def to_fr_def)
  by (metis of_fr.abs_eq of_fr.rep_eq)


lemma to_fr_of_fr: "to_fr (of_fr (x)) = x"
  apply (auto simp add: of_fr_def to_fr_def)
  by (metis (mono_tags, lifting) Quotient3_abs_rep Quotient3_fr Quotient3_rel cong_def fr_rel_def mod_mod_trivial)

lemma eq_to_fr: "x = y \<Longrightarrow> to_fr x = to_fr y" by auto

(* analogous: conversion between 'a mod_ring and int *)
term "of_int_mod_ring :: int \<Rightarrow> 'a :: finite mod_ring"
term "to_int_mod_ring :: 'a :: finite mod_ring \<Rightarrow> int"

(* some operations on polynomials *)
term "[:3, 2, 1:] :: real poly" (* entspricht x^2 + 2x + 1 *)
term "Polynomial.monom c n :: real poly" (* entspricht c * x^n *)
term "poly.coeff :: real poly \<Rightarrow> nat \<Rightarrow> real" (* n-ter Koeffizient *)
term poly (* Auswertungshomomorphismus *)
term map_poly (* Wende Funktion f auf alle Koeffizienten an (Vorsicht: f 0 sollte 0 sein *)






(* type class instantiations for fr *)

instantiation fr :: (fr_spec) comm_ring_1
begin

lift_definition zero_fr :: "'a fr" is "0" .

lift_definition one_fr :: "'a fr" is "1" .

lift_definition plus_fr :: "'a fr \<Rightarrow> 'a fr \<Rightarrow> 'a fr"
  is "(+)"
  unfolding fr_rel_def using cong_add by blast

lift_definition uminus_fr :: "'a fr \<Rightarrow> 'a fr"
  is "uminus"
  unfolding fr_rel_def  using cong_minus_minus_iff by blast

lift_definition minus_fr :: "'a fr \<Rightarrow> 'a fr \<Rightarrow> 'a fr"
  is "(-)"
  unfolding fr_rel_def using cong_diff by blast

lift_definition times_fr :: "'a fr \<Rightarrow> 'a fr \<Rightarrow> 'a fr"
  is "(*)"
  unfolding fr_rel_def using cong_mult by blast

instance
proof
  show "0 \<noteq> (1 :: 'a fr)"
    by transfer (simp add: fr_rel_def cong_def)
qed (transfer; simp add: fr_rel_def algebra_simps; fail)+

end

lemma of_fr_0 [simp]: "of_fr 0 = 0"
  and of_fr_1 [simp]: "of_fr 1 = 1"
  and of_fr_uminus [simp]: "of_fr (-p) = -of_fr p"
  and of_fr_add [simp]: "of_fr (p + q) = of_fr p + of_fr q"
  and of_fr_diff [simp]: "of_fr (p - q) = of_fr p - of_fr q"
  by (transfer; simp add: poly_mod_add_left poly_mod_diff_left; fail)+

lemma to_fr_0 [simp]: "to_fr 0 = 0"
  and to_fr_1 [simp]: "to_fr 1 = 1"
  and to_fr_uminus [simp]: "to_fr (-p) = -to_fr p"
  and to_fr_add [simp]: "to_fr (p + q) = to_fr p + to_fr q"
  and to_fr_diff [simp]: "to_fr (p - q) = to_fr p - to_fr q"
  and to_fr_mult [simp]: "to_fr (p * q) = to_fr p * to_fr q"
  by (transfer'; simp; fail)+

lemma to_fr_of_nat [simp]: "to_fr (of_nat n) = of_nat n"
  by (induction n) auto

lemma to_fr_of_int [simp]: "to_fr (of_int n) = of_int n"
  by (induction n) auto

lemma of_fr_of_nat [simp]: "of_fr (of_nat n) = of_nat n"
  by (induction n) auto

lemma of_fr_of_int [simp]: "of_fr (of_int n) = of_int n"
  by (induction n) auto

lemma of_fr_eq_0_iff [simp]: "of_fr p = 0 \<longleftrightarrow> p = 0"
  by transfer (simp add: fr_rel_def cong_def)

lemma to_fr_eq_0_iff:
  "to_fr p = 0 \<longleftrightarrow> fr_poly dvd p"
  by transfer (auto simp: fr_rel_def cong_def)






(* some more lemmas that will probably be useful *)

lemma to_fr_eq_iff [simp]:
  "to_fr P = (to_fr Q :: 'a :: fr_spec fr) \<longleftrightarrow> [P = Q] (mod fr_poly)"
  by transfer (auto simp: fr_rel_def)

(*
  reduction modulo (X^n + 1) is injective on polynomials of degree < n
  in particular, this means that card(FR(q^n)) = q^n.
*)
lemma inj_on_to_fr:
  "inj_on
     (to_fr :: 'a :: fr_spec mod_ring poly \<Rightarrow> 'a fr)
     {P. degree P < deg_fr TYPE('a)}"
  by (intro inj_onI) (auto simp: cong_def mod_poly_less simp flip: degree_fr_poly)

(* characteristic of factorial ring is exactly q *)

lemma of_int_fr_eq_0_iff [simp]:
  "of_int n = (0 :: 'a :: fr_spec fr) \<longleftrightarrow> int (CARD('a)) dvd n"
proof -
  have "of_int n = (0 :: 'a fr) \<longleftrightarrow> (of_int n :: 'a mod_ring poly) = 0"
    by (smt (z3) of_fr_eq_0_iff of_fr_of_int)
  also have "\<dots> \<longleftrightarrow> (of_int n :: 'a mod_ring) = 0"
    by (simp add: of_int_poly)
  also have "\<dots> \<longleftrightarrow> int (CARD('a)) dvd n"
    by (simp add: of_int_mod_ring_eq_0_iff)
  finally show ?thesis .
qed

lemma of_int_fr_eq_of_int_iff:
  "of_int n = (of_int m :: 'a :: fr_spec fr) \<longleftrightarrow> [n = m] (mod (int (CARD('a))))"
  using of_int_fr_eq_0_iff[of "n - m", where ?'a = 'a]
  by (simp del: of_int_fr_eq_0_iff add: cong_iff_dvd_diff)

lemma of_nat_fr_eq_of_nat_iff:
  "of_nat n = (of_nat m :: 'a :: fr_spec fr) \<longleftrightarrow> [n = m] (mod CARD('a))"
  using of_int_fr_eq_of_int_iff[of "int n" "int m"] 
  by (simp add: cong_int_iff)

lemma of_nat_fr_eq_0_iff [simp]:
  "of_nat n = (0 :: 'a :: fr_spec fr) \<longleftrightarrow> CARD('a) dvd n"
  using of_int_fr_eq_0_iff[of "int n"] by simp


(*
The specifications use 
n=256 = 2^9
n' = 9
q = 7681 or 3329
k = 3
*)




locale kyber_spec =
fixes n q::int and k n'::nat
assumes
n_powr_2: "n = 2 ^ n'" and
n'_gr_0: "n' > 0" and 
q_gr_two: "q > 2" and
q_mod_4: "q mod 4 = 1" and 
q_prime : "prime q"
assumes CARD_a: "int (CARD('a :: fr_spec)) = q"
assumes CARD_k: "int (CARD('k :: finite)) = k"

assumes fr_poly'_eq: "fr_poly' TYPE('a) = Polynomial.monom 1 (nat n) + 1"

begin
text \<open>Some properties of the modulus q.\<close>

lemma q_nonzero: "q \<noteq> 0" 
using kyber_spec_axioms kyber_spec_def by (smt (z3))

lemma q_gt_zero: "q>0" 
using kyber_spec_axioms kyber_spec_def by (smt (z3))

lemma q_gt_two: "q>2"
using kyber_spec_axioms kyber_spec_def by (smt (z3))

lemma q_odd: "odd q"
using kyber_spec_axioms kyber_spec_def
 prime_odd_int by blast


text \<open>Some properties of the degree n.\<close>

lemma n_gt_1: "n > 1"
using kyber_spec_axioms kyber_spec_def
  by (simp add: n'_gr_0 n_powr_2)

lemma n_nonzero: "n \<noteq> 0" 
using n_gt_1 by auto

lemma n_gt_zero: "n>0" 
using n_gt_1 by auto

(*
text \<open>In order to make certain that the proof of the scheme goes through, 
  we need $q \cong 1 \mod 4$.\<close>
lemma q_mod_4: "q mod 4 = 1"
using q_def by force
*)

text \<open>Properties in the ring \<open>'a fr\<close>. A good representative has degree up to n.\<close>
lemma deg_mod_fr_poly:
  assumes "degree x < deg_fr TYPE('a)"
  shows "x mod (fr_poly :: 'a mod_ring poly) = x"
using mod_poly_less[of x fr_poly] unfolding deg_fr_def
by (metis assms degree_fr_poly) 

lemma of_fr_to_fr': 
  assumes "degree x < deg_fr TYPE('a)"
  shows "of_fr (to_fr x) = (x ::'a mod_ring poly)"
using deg_mod_fr_poly[OF assms] of_fr_to_fr[of x] by simp

lemma deg_fr_n: 
  "deg_fr TYPE('a) = n"
unfolding deg_fr_def using fr_poly'_eq n_gt_1
by (simp add: degree_add_eq_left degree_monom_eq)

lemma deg_of_fr: 
  "degree (of_fr (x ::'a fr)) < deg_fr TYPE('a)"
by (metis deg_fr_pos degree_0 degree_fr_poly degree_mod_less' fr_poly_nz of_fr.rep_eq)

definition to_module :: "int \<Rightarrow> 'a fr" where
  "to_module x = to_fr (Poly [of_int_mod_ring x ::'a mod_ring])"

lemma to_fr_smult_to_module: 
  "to_fr (Polynomial.smult a p) = (to_fr (Poly [a])) * (to_fr p)"
by (metis Poly.simps(1) Poly.simps(2) mult.left_neutral mult_smult_left smult_one to_fr_mult)

lemma of_fr_to_fr_smult:
  "of_fr (to_fr (Polynomial.smult a p)) = Polynomial.smult a (of_fr (to_fr p))"
by (simp add: mod_smult_left of_fr_to_fr)


end
end