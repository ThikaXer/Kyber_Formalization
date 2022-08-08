theory Check_Prime
imports Main
  "HOL-Computational_Algebra.Primes"
  "HOL-Number_Theory.Eratosthenes"
begin

text \<open>Checking for primality by testing all numbers smaller than \<open>p div 2\<close> as divisors.\<close>

function (sequential) prime_test ::"nat \<Rightarrow> nat \<Rightarrow> bool" where
"prime_test 0 p = False" |
"prime_test (Suc 0) p = True" | 
"prime_test t p = (if p mod t = 0 then False
  else prime_test (t-1) p)"
by pat_completeness auto
termination by lexicographic_order

definition "check_prime p = prime_test (p div 2) p"

text \<open>For tricky simplification.\<close>
lemma Suc_Suc:
  assumes "x>1" 
  shows"x = Suc (Suc (x-2))"
using assms by auto

text \<open>Check the moduluses of Kyber for primeality.\<close>
text \<open>This takes 2-3 min to run\<close>
lemma check_3329:
  "check_prime (3329::nat)" unfolding check_prime_def 
apply simp apply (subst Suc_Suc, simp, subst prime_test.simps(3), auto)+ 
by (metis and_numerals(8) and_one_eq gr_zeroI numeral_2_eq_2 zero_neq_one)

lemma check_7681:
  "check_prime (7681::nat)" unfolding check_prime_def 
apply simp apply (subst Suc_Suc, simp, subst prime_test.simps(3), auto)+ 
by (metis and_numerals(8) and_one_eq gr_zeroI numeral_2_eq_2 zero_neq_one)


text \<open>Show that our \<open>check_prime\<close> function is correct and is true only for primes.\<close>
lemma prime_test_lower:
assumes "check_prime p" "t\<le>p div 2" "t\<ge>1"
shows "prime_test t p"
proof (induct rule: inc_induct[OF assms(2)])
  case 1
  then show ?case using assms(1) unfolding check_prime_def by auto
next
  case (2 n)
  then have "prime_test (Suc (Suc (n-1))) p" using assms by auto
  then show ?case using prime_test.simps(3)[of "n-1" p] 
  by (metis "2.hyps"(1) Suc_diff_le add_diff_cancel_left' assms(3) order_trans plus_1_eq_Suc)
qed

lemma check_prime_not_dividend:
assumes "p>3" "t\<le>p div 2"
  "check_prime p" "t>1"
shows "\<not> (t dvd p)"
proof (induct rule: inc_induct[OF assms(2)])
  case 1
  then have gr:"p div 2 > 1" using assms by linarith
  have "check_prime p = (if p mod (p div 2) = 0 then False
    else prime_test ((p div 2)-1) p)" 
    unfolding check_prime_def 
    apply (subst Suc_Suc[OF gr])
    apply (subst prime_test.simps(3)) 
    using Suc_Suc gr by presburger
  then show ?case using \<open>p>3\<close> \<open>check_prime p\<close> by presburger
next
  case (2 n)
  then have gr:"n > 1" using assms by linarith
  have "check_prime p = prime_test n p" 
    using prime_test_lower[OF \<open>check_prime p\<close>, of n] 2 assms by auto
  moreover have "\<dots> = (if p mod n = 0 then False
    else prime_test (n-1) p)" 
    unfolding check_prime_def 
    apply (subst Suc_Suc[OF gr])
    apply (subst prime_test.simps(3)) 
    using Suc_Suc gr by presburger
  ultimately show ?case using \<open>p>3\<close> \<open>check_prime p\<close> by presburger
qed

lemma dvd_lt_div_2:
assumes "m dvd (p::nat)" "p>1" "m\<noteq>p"
shows "m \<le> p div 2"
using assms 
by (metis Groups.mult_ac(2) One_nat_def div_less_iff_less_mult dvd_mult_div_cancel 
linorder_neqE_nat linorder_not_le mult_1_right not_less_eq numeral_2_eq_2 zero_less_Suc)

lemma not_check_prime_dvd:
assumes "check_prime p"
  "p>1"
  "m dvd p"
  "m \<noteq> p"
  "m \<noteq> 1"
shows False
proof -
  consider (2) "p=2" | (3) "p=3" | (greater) "p>3" using \<open>p>1\<close> by linarith
  then show False proof (cases)
    case 2
    then show ?thesis using assms 
    by (metis One_nat_def Suc_1 Suc_lessI dvd_antisym nat_dvd_not_less odd_pos zero_less_numeral)
  next
    case 3
    then show ?thesis using assms 
    by (metis One_nat_def Suc_lessI dvd_pos_nat eval_nat_numeral(3) nat_dvd_not_less 
      numeral_2_eq_2 odd_numeral zero_less_numeral)
  next
    case greater
    have "1 < m" using assms 
    by (metis One_nat_def Suc_lessI dvd_pos_nat not_less_eq not_less_iff_gr_or_eq)
    have m_div:"m \<le> p div 2" using dvd_lt_div_2[OF \<open>m dvd p\<close> \<open>1<p\<close> \<open>m\<noteq>p\<close>] .
    show ?thesis using check_prime_not_dividend[OF \<open>3<p\<close> m_div assms(1) \<open>1<m\<close>] 
      \<open>m dvd p\<close> by auto
  qed
qed

lemma check_prime_dvd:
assumes "check_prime p"
  "p>1"
  "m dvd p"
  "m \<noteq> p"
shows "m=1"
using not_check_prime_dvd[OF assms] assms by blast
  
lemma prime_is_check:
assumes "prime p" "t\<le>p div 2" "t\<ge>1"
shows "prime_test t p"
proof (induct rule: dec_induct[OF assms(3)])
  case (2 n)
  have Suc_n: "1 < Suc (Suc (n - 1))" by auto
  have not_mod: "\<not>(p mod Suc n = 0)" using assms(1) unfolding prime_nat_iff
  by (metis (mono_tags, lifting) "2.hyps"(1) "2.hyps"(2) One_nat_def assms(2) 
    div_less_dividend less_numeral_extra(1) mod_0_imp_dvd not_less_eq numeral_2_eq_2 
    order_less_le_trans order_less_trans)
  have "prime_test (Suc n) p = prime_test (Suc (Suc (n-1))) p" using 2 by auto
  moreover have "\<dots> = (if p mod (Suc n) = 0 then False
    else prime_test n p)"
   apply (subst prime_test.simps(3)) 
   using "2.hyps"(1) by force
  moreover have "\<dots> = prime_test n p" using not_mod by auto
  ultimately show ?case using 2(3) by auto
qed auto


lemma check_prime_checks_prime:
assumes "p>1"
shows "check_prime p \<longleftrightarrow> prime p"
proof (safe, goal_cases)
  assume p: "check_prime p"
  then show "prime p" unfolding check_prime_def prime_nat_iff using assms 
  proof (safe, goal_cases)
    case (1 m)
    show ?case using check_prime_dvd[OF p 1(2) 1(3) 1(4)] .
  qed
next
  assume p: "prime p"
  then show "check_prime p" using prime_is_check[OF p, of "p div 2"]
  by (metis assms dual_order.eq_iff dvd_lt_div_2 nat_neq_iff one_dvd check_prime_def) 
qed

text \<open>Relate primeality to 7681 and 3329.\<close>
lemma prime_3329: "prime (3329::nat)"
by (subst check_prime_checks_prime[symmetric])
   (use check_3329 in \<open>auto\<close>)

lemma prime_7681: "prime (7681::nat)"
by (subst check_prime_checks_prime[symmetric])
   (use check_7681 in \<open>auto\<close>)


end