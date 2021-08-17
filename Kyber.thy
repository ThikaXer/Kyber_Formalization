theory Kyber
imports Main "HOL-Computational_Algebra.Polynomial"
 "Berlekamp_Zassenhaus.Poly_Mod" 

begin

locale kyber_spec =
fixes n n' q::int
and R R_q
assumes
"n   = 256"
"n'  = 9"
"q   = 7681"
"R   = Z_x"
"R_q = Z_q_x"
begin

lemma q_nonzero: "q \<noteq> 0" 
by (smt (verit) kyber_spec_axioms kyber_spec_def)

lemma q_gt_zero: "q>0"
by (smt (verit, best) kyber_spec_axioms kyber_spec_def)

definition "Z_q = range (\<lambda>x. x mod q)"

text \<open>Define the polynomial ring over the integers. \<close>
definition Z_x :: "int poly set" where
"Z_x=range Poly"


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

lemma compress_no_mod:
assumes 
  "x\<in>{0..\<lceil>q-(q/2^(d+1))\<rceil>-1}" 
  "of_nat d < \<lceil>(log 2 q)::real\<rceil>"
shows "compress x d = round (real_of_int (2 ^ d * x) / real_of_int q)"
sorry

lemma compress_mod:
assumes 
  "x\<in>{\<lceil>q-(q/2^(d+1))\<rceil>..q-1}" 
  "of_nat d < \<lceil>(log 2 q)::real\<rceil>"
shows "compress x d = 0"
sorry

(*
lemma compress_id:
assumes 
  "x\<in>{0..floor (q-(q/2^(d+1)))-1}" 
  "of_nat d < \<lceil>(log 2 q)::real\<rceil>"
shows "round (real_of_int (2 ^ d * x) / real_of_int q) \<in> {0..2^d - 1}" 
proof (auto, goal_cases)
case 1
  have "d < log 2 q" using assms(2) by linarith
  have "(2::int)^d \<noteq> 0" by simp
  have "2 powr (real d) < of_int q" using less_log_iff[of 2 q d] \<open>d< log 2 q\<close> q_gt_zero by auto
  show ?case using 1(1) \<open>2 powr (real d) < q\<close> 
  by (smt (verit, best) divide_divide_eq_right divide_nonneg_nonneg of_int_0_le_iff 
    q_gt_zero round_0 round_mono zero_le_power)
next
case 2
  have "d < log 2 q" using assms(2) by linarith
  have "(2::int)^d \<noteq> 0" by simp
  have "2 powr (real d) < of_int q" using less_log_iff[of 2 q d] \<open>d< log 2 q\<close> q_gt_zero by auto
  then have "real_of_int x < real_of_int q - real_of_int q / (2 * 2 ^ d)" 
    using assms(1) 2(2) by linarith
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
  then show ?case unfolding round_def using floor_mono
    by (smt (verit, best) floor_correct of_int_add of_int_hom.hom_one 
    of_int_power_less_of_int_cancel_iff)
qed 
*)

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
    using mod_range  by auto
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