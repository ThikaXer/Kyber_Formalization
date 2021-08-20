theory Compress

imports Kyber_spec

begin

context kyber_spec begin



lemma q_nonzero: "q \<noteq> 0" 
using kyber_spec_axioms kyber_spec_def by (smt (z3))

lemma q_gt_zero: "q>0" 
using kyber_spec_axioms kyber_spec_def by (smt (z3))

lemma q_gt_two: "q>2"
using kyber_spec_axioms kyber_spec_def by (smt (z3))

lemma q_prime: "prime q"
using kyber_spec_axioms kyber_spec_def
by (metis prime_card_int)


text \<open>To define the Compress and Decompress functions, 
  we need some special form of modulo. It returns the 
  representation of the equivalence class in \<open>[-q div 2, q div 2]\<close>.\<close>

definition mod_plus_minus :: "int \<Rightarrow> int \<Rightarrow> int" (infixl "mod+-" 70) where 
  "m mod+- b = ((m + \<lfloor> real_of_int b / 2 \<rfloor>) mod b) - \<lfloor> real_of_int b / 2 \<rfloor>"
 
lemma mod_range: "b>0 \<Longrightarrow> (a::int) mod (b::int) \<in> {0..b-1}"
using range_mod by auto

lemma mod_rangeE: 
  assumes "(a::int)\<in>{0..<b}"
  shows "a = a mod b"
using assms by auto

lemma two_mid_lt_q:
  "2 * \<lfloor>real_of_int q / 2\<rfloor> < q" 
using oddE[OF prime_odd_int[OF q_prime q_gt_two]] by fastforce


lemma mod_plus_minus_range: 
  assumes "b>0"
  shows "y mod+- b \<in> {-\<lfloor>b/2\<rfloor>..\<lfloor>b/2\<rfloor>}"
unfolding mod_plus_minus_def using mod_range[OF assms, of "(y + \<lfloor>real_of_int b / 2\<rfloor>)"]
by (auto)(linarith)

lemma mod_plus_minus_range_q: 
  assumes "y \<in> {-\<lfloor>q/2\<rfloor>..\<lfloor>q/2\<rfloor>}"
  shows "y mod+- q = y"
using mod_plus_minus_range[OF q_gt_zero, of y] unfolding mod_plus_minus_def
proof (auto)
  have this': "y + \<lfloor>real_of_int q / 2\<rfloor> \<in> {0..<q}" using assms two_mid_lt_q by auto
  have "(y + \<lfloor>real_of_int q / 2\<rfloor>) mod q = (y + \<lfloor>real_of_int q / 2\<rfloor>)" 
    using mod_rangeE[OF this'] by auto
  then show "(y + \<lfloor>real_of_int q / 2\<rfloor>) mod q - \<lfloor>real_of_int q / 2\<rfloor> = y" by auto
qed
 

text \<open>Compression only works for \<open>x \<in> Z_q\<close> and outputs an integer 
  in \<open>{0,\<dots> , 2 d − 1}\<close> , where \<open>d < \<lceil>log_2 (q)\<rceil>\<close> . \<close>

definition compress :: "int \<Rightarrow> nat \<Rightarrow> int" where 
  "compress x d = round (real_of_int (2 ^ d * x) / real_of_int q) mod (2^d)"

definition decompress :: "int \<Rightarrow> nat \<Rightarrow> int" where 
  "decompress x d = round (real_of_int q * real_of_int x / real_of_int 2 ^ d)"

lemma range_compress: 
  assumes "x\<in>{0..q-1}" "of_nat d < \<lceil>(log 2 q)::real\<rceil>" 
  shows "compress x d \<in> {0..2^d - 1}" 
using compress_def by auto

lemma decompress_zero: "decompress 0 d = 0" 
unfolding decompress_def by auto

lemma d_lt_logq: 
  assumes "of_nat d < \<lceil>(log 2 q)::real\<rceil>"
  shows "d< log 2 q"
using assms by linarith

lemma twod_lt_q: 
  assumes "of_nat d < \<lceil>(log 2 q)::real\<rceil>"
  shows "2 powr (real d) < of_int q"
using assms less_log_iff[of 2 q d] d_lt_logq q_gt_zero by auto

lemma prime_half:
  assumes "prime (p::int)"
          "p > 2"
  shows "\<lceil>p / 2\<rceil> > \<lfloor>p / 2\<rfloor>"
proof -
  have "odd p" using prime_odd_int[OF assms] .
  then have "\<lceil>p / 2\<rceil> > p/2" 
    by (smt (verit, best) cos_npi_int cos_zero_iff_int le_of_int_ceiling 
      mult.commute times_divide_eq_right)
  then have "\<lfloor>p / 2\<rfloor> < p/2" 
  by (meson floor_less_iff less_ceiling_iff)
  then show ?thesis using \<open>\<lceil>p / 2\<rceil> > p/2\<close> by auto
qed


lemma break_point_gt_q_div_two:
  assumes "of_nat d < \<lceil>(log 2 q)::real\<rceil>"
  shows "\<lceil>q-(q/(2*2^d))\<rceil> > \<lfloor>q / 2\<rfloor>"
proof -
  have "1/((2::real)^d) \<le> (1::real)" using one_le_power[of 2 d] by simp
  have "\<lceil>q-(q/(2*2^d))\<rceil> \<ge> q-(q/2)* (1/(2^d))" by simp
  moreover have "q-(q/2)* (1/(2^d)) \<ge> q - q/2" using \<open>1/((2::real)^d) \<le> (1::real)\<close>  
    by (smt (z3) calculation divide_le_eq divide_nonneg_nonneg divide_self_if 
      mult_left_mono of_int_nonneg times_divide_eq_right q_gt_zero)
  ultimately have "\<lceil>q-(q/(2*2^d))\<rceil> \<ge> \<lceil>q/2\<rceil> " by linarith
  moreover have "\<lceil>q/2\<rceil> > \<lfloor>q / 2\<rfloor>" using prime_half[OF q_prime q_gt_two] .
  ultimately show ?thesis by auto
qed



lemma compress_in_range: 
  assumes "x\<in>{0..\<lceil>q-(q/(2*2^d))\<rceil>-1}" 
          "of_nat d < \<lceil>(log 2 q)::real\<rceil>" 
  shows "round (real_of_int (2 ^ d * x) / real_of_int q) < 2^d " 
proof - 
  have "(2::int)^d \<noteq> 0" by simp  
  have "real_of_int x < real_of_int q - real_of_int q / (2 * 2 ^ d)" 
    using assms(1) less_ceiling_iff by auto 
  then have "2 ^ d * real_of_int x / real_of_int q < 
             2 ^ d * (real_of_int q - real_of_int q / (2 * 2 ^ d)) / real_of_int q" 
    by (simp add: divide_strict_right_mono q_gt_zero) 
  also have "\<dots> = 2 ^ d * ((real_of_int q / real_of_int q) -
                  (real_of_int q / real_of_int q) / (2 * 2 ^ d))" 
  by (simp add:algebra_simps diff_divide_distrib) 
  also have "\<dots> = 2^d * (1 - 1/(2*2^d))" using q_nonzero by simp 
  also have "\<dots> = 2^d - 1/2" using \<open>2^d \<noteq> 0\<close> by (simp add: right_diff_distrib') 
  finally have "2 ^ d * real_of_int x / real_of_int q < 2^d - (1::real)/(2::real)" 
    by auto 
  then show ?thesis unfolding round_def using floor_less_iff by fastforce 
qed

text \<open>When does the modulo operation in the compression function change the output? 
  Only when  \<open>x \<ge> \<lceil>q-(q / (2*2^d))\<rceil>\<close>. Then we can determine that the compress function 
  maps to zero. \<close>

lemma compress_no_mod: 
  assumes "x\<in>{0..\<lceil>q-(q / (2*2^d))\<rceil>-1}" 
          "of_nat d < \<lceil>(log 2 q)::real\<rceil>" 
  shows "compress x d = round (real_of_int (2 ^ d * x) / real_of_int q)" 
unfolding compress_def using compress_in_range[OF assms] assms(1) q_gt_zero 
by (smt (z3) atLeastAtMost_iff divide_nonneg_nonneg mod_pos_pos_trivial 
  mult_less_cancel_left_pos of_int_nonneg of_nat_0_less_iff right_diff_distrib'
  round_0 round_mono zero_less_power)

lemma compress_2d: 
  assumes "x\<in>{\<lceil>q-(q/(2*2^d))\<rceil>..q-1}" 
          "of_nat d < \<lceil>(log 2 q)::real\<rceil>" 
  shows "round (real_of_int (2 ^ d * x) / real_of_int q) = 2^d " 
using assms proof - 
  have "(2::int)^d \<noteq> 0" by simp
  have "round (real_of_int (2 ^ d * x) / real_of_int q) \<ge> 2^d" 
  proof -
    have "real_of_int x \<ge> real_of_int q - real_of_int q / (2 * 2 ^ d)" 
      using assms(1) ceiling_le_iff by auto 
    then have "2 ^ d * real_of_int x / real_of_int q \<ge> 
               2 ^ d * (real_of_int q - real_of_int q / (2 * 2 ^ d)) / real_of_int q" 
      using q_gt_zero by (simp add: divide_right_mono) 
    also have "2 ^ d * (real_of_int q - real_of_int q / (2 * 2 ^ d)) / real_of_int q
             = 2 ^ d * ((real_of_int q / real_of_int q) -
               (real_of_int q / real_of_int q) / (2 * 2 ^ d))" 
      by (simp add:algebra_simps diff_divide_distrib) 
    also have "\<dots> = 2^d * (1 - 1/(2*2^d))" using q_nonzero by simp 
    also have "\<dots> = 2^d - 1/2" using \<open>2^d \<noteq> 0\<close> by (simp add: right_diff_distrib') 
    finally have "2 ^ d * real_of_int x / real_of_int q \<ge> 2^d - (1::real)/(2::real)" 
      by auto 
    then show ?thesis unfolding round_def using le_floor_iff by force
  qed
  moreover have "round (real_of_int (2 ^ d * x) / real_of_int q) \<le> 2^d" 
  proof -
    have "d < log 2 q" using assms(2) by linarith
    then have "2 powr (real d) < of_int q" 
      using less_log_iff[of 2 q d] q_gt_zero by auto

    have "x < q" using assms(1) by auto
    then have "real_of_int x/ real_of_int q < 1"
      by (simp add: q_gt_zero)
    then have "real_of_int (2 ^ d * x) / real_of_int q < real_of_int (2^d)" 
      by (auto) (smt (verit, best) divide_less_eq_1_pos nonzero_mult_div_cancel_left 
        times_divide_eq_right zero_less_power)
    then show ?thesis unfolding round_def by linarith
  qed 
  ultimately show ?thesis by auto
qed

lemma compress_mod: 
  assumes "x\<in>{\<lceil>q-(q/(2*2^d))\<rceil>..q-1}" 
          "of_nat d < \<lceil>(log 2 q)::real\<rceil>" 
  shows "compress x d = 0" 
unfolding compress_def using compress_2d[OF assms] by simp


text \<open>Error after compression and decompression of data.\<close>

lemma decompress_compress_no_mod: 
  assumes "x\<in>{0..\<lceil>q-(q/(2*2^d))\<rceil>-1}" 
          "of_nat d < \<lceil>(log 2 q)::real\<rceil>"
  shows "abs (decompress (compress x d) d - x) \<le> round ( real_of_int q / real_of_int (2^(d+1)))" 
proof - 
  have "abs (decompress (compress x d) d - x) = 
        abs (real_of_int (decompress (compress x d) d) - 
             real_of_int q / real_of_int (2^d) * 
                (real_of_int (2 ^ d * x) / real_of_int q))"
    using q_gt_zero by force
  also have "\<dots> \<le> abs (real_of_int (decompress (compress x d) d) -
                       real_of_int q / real_of_int (2^d) * real_of_int (compress x d)) +
                  abs (real_of_int q / real_of_int (2^d) * real_of_int (compress x d) -
                       real_of_int q / real_of_int (2^d) * real_of_int (2^d) / real_of_int q * x)"
    using abs_triangle_ineq[of "real_of_int (decompress (compress x d) d) -
        real_of_int q / real_of_int (2 ^ d) * real_of_int (compress x d)"
        "real_of_int q / real_of_int (2 ^ d) * real_of_int (compress x d) -
        real_of_int q / real_of_int (2 ^ d) * real_of_int (2 ^ d) / real_of_int q *
        real_of_int x"] by auto
  also have "\<dots> \<le> 1/2 + abs (real_of_int q / real_of_int (2^d) * 
                  (real_of_int (compress x d) - 
                   real_of_int (2^d) / real_of_int q * real_of_int x))"
    proof -
      have part_one: "abs (real_of_int (decompress (compress x d) d) -
                 real_of_int q / real_of_int (2^d) * real_of_int (compress x d)) \<le> 1/2"
        unfolding decompress_def using of_int_round_abs_le[of "real_of_int q * 
          real_of_int (compress x d) / real_of_int 2 ^ d"] by simp
      have "real_of_int q * real_of_int (compress x d) / 2 ^ d - real_of_int x =
        real_of_int q * (real_of_int (compress x d) - 2 ^ d * real_of_int x / real_of_int q) 
        / 2 ^ d" 
        by (smt (verit, best) divide_cancel_right nonzero_mult_div_cancel_left 
        of_int_eq_0_iff q_nonzero right_diff_distrib times_divide_eq_left zero_less_power)
      then have part_two: "abs (real_of_int q / real_of_int (2^d) * real_of_int (compress x d) -
        real_of_int q / real_of_int (2^d) * real_of_int (2^d) / real_of_int q * x) =
        abs (real_of_int q / real_of_int (2^d) * 
        (real_of_int (compress x d) - real_of_int (2^d) / real_of_int q * x)) " by auto
      show ?thesis using part_one part_two by auto
   qed
  also have "\<dots> = 1/2 + (real_of_int q / real_of_int (2^d)) * 
      abs (real_of_int (compress x d) - real_of_int (2^d) / real_of_int q * real_of_int x)"
    by (smt (verit, best) distrib_left divide_nonneg_nonneg mult_eq_0_iff 
      mult_less_cancel_left_pos of_int_nonneg q_gt_zero zero_le_power)
  also have "\<dots> \<le> 1/2 + (real_of_int q / real_of_int (2^d)) * (1 / 2) "
    using compress_no_mod[OF assms] 
    using of_int_round_abs_le[of "real_of_int (2 ^ d) * real_of_int x / real_of_int q"]
    by (smt (verit, ccfv_SIG) divide_nonneg_nonneg left_diff_distrib mult_less_cancel_left_pos 
      of_int_mult of_int_nonneg q_gt_zero times_divide_eq_left zero_le_power)
  finally have "real_of_int (abs (decompress (compress x d) d - x)) \<le> 
                real_of_int q / real_of_int (2*2^d) + 1/2" 
    by simp
  then show ?thesis unfolding round_def using le_floor_iff by fastforce
qed


lemma no_mod_plus_minus: 
  assumes "abs y \<le> round ( real_of_int q / real_of_int (2^(d+1)))"
          "d>0"
  shows "abs y = abs (y mod+- q)"
proof -
  have "round (real_of_int q / real_of_int (2^(d+1))) \<le> \<lfloor>q/2\<rfloor>" unfolding round_def 
  proof -
    have "real_of_int q/real_of_int (2^d) \<le> real_of_int q/2" using \<open>d>0\<close> 
    proof -
      have "1 / real_of_int (2^d) \<le> 1 / 2" using \<open>d>0\<close> inverse_of_nat_le[of 2 "2^d"]
        by (simp add: self_le_power)
      then show ?thesis using q_gt_zero 
        by (smt (verit, ccfv_SIG) divide_cancel_left frac_le of_int_pos zero_less_power)
    qed
    moreover have "real_of_int q / 2 + 1 \<le> real_of_int q" using q_gt_two by auto
    ultimately have "real_of_int q / real_of_int (2 ^ d) + 1 \<le> real_of_int q" 
      by linarith
    then have fact: "real_of_int q / real_of_int (2 ^ (d + 1)) + 1 / 2 \<le> real_of_int q / 2" 
      by auto
    then show "\<lfloor>real_of_int q / real_of_int (2 ^ (d + 1)) + 1 / 2\<rfloor> \<le> \<lfloor>real_of_int q / 2\<rfloor>" 
      using floor_mono[OF fact] by auto
  qed
  then have "abs y \<le> \<lfloor>q/2\<rfloor>" using assms by auto
  then show ?thesis using mod_plus_minus_range[OF q_gt_zero]
    using mod_plus_minus_def two_mid_lt_q by force 
qed


lemma decompress_compress_no_mod_plus_minus: 
  assumes "x\<in>{0..\<lceil>q-(q/(2*2^d))\<rceil>-1}" 
          "of_nat d < \<lceil>(log 2 q)::real\<rceil>"
          "d>0"
  shows "abs ((decompress (compress x d) d - x) mod+- q) \<le> 
          round ( real_of_int q / real_of_int (2^(d+1)))"
proof -
  have "abs ((decompress (compress x d) d - x) mod+- q) =
        abs ((decompress (compress x d) d - x)) " 
    using no_mod_plus_minus[OF decompress_compress_no_mod[OF assms(1) assms(2)] assms(3)] by auto
  then show ?thesis using decompress_compress_no_mod[OF assms(1) assms(2)] by auto
qed


lemma ceiling_int: 
  "\<lceil>of_int a + b\<rceil> = a + \<lceil>b\<rceil>"
unfolding ceiling_def by (simp add: add.commute)

lemma decompress_compress_mod: 
  assumes "x\<in>{\<lceil>q-(q/(2*2^d))\<rceil>..q-1}" 
          "of_nat d < \<lceil>(log 2 q)::real\<rceil>"
  shows "abs ((decompress (compress x d) d - x) mod+- q) \<le> 
         round ( real_of_int q / real_of_int (2^(d+1)))"
proof -
  have "(decompress (compress x d) d - x) = - x" 
    using compress_mod[OF assms] unfolding decompress_def by auto
  moreover have "-x mod+- q = -x+q" 
  proof -
    have "(-x + \<lfloor>q/2\<rfloor>) + q < q" using assms(1) break_point_gt_q_div_two[OF assms(2)] by force
    moreover have "(-x + \<lfloor>q/2\<rfloor>) + q \<ge> 0 " using assms(1) q_gt_zero 
      by (smt (verit, best) atLeastAtMost_iff divide_nonneg_nonneg of_int_nonneg zero_le_floor)
    ultimately have "(- x + \<lfloor>q/2\<rfloor>) mod q = - x + \<lfloor>q/2\<rfloor> + q" 
      by (metis mod_add_self2 mod_pos_pos_trivial)
    then show ?thesis unfolding mod_plus_minus_def by auto
  qed
  moreover have "abs (q - x) \<le> round ( real_of_int q / real_of_int (2^(d+1)))" 
  proof -
    have "abs (q-x) = q-x" using assms(1) by auto
    also have "\<dots> \<le> q - \<lceil>q - q/(2*2^d)\<rceil>" using assms(1) by simp
    also have "\<dots> = - \<lceil>- q/(2*2^d)\<rceil>" using ceiling_int[of q "- q/(2*2^d)"] by auto
    also have "\<dots> = \<lfloor>q/(2*2^d)\<rfloor>" by (simp add: ceiling_def)
    also have "\<dots> \<le> round (q/(2*2^d))" using floor_le_round by blast
    finally have "abs (q-x) \<le> round (q/(2^(d+1)))" by auto
    then show ?thesis by auto
  qed
  ultimately show ?thesis by auto
qed


lemma decompress_compress: 
  assumes "x\<in>{0..<q}"
          "of_nat d < \<lceil>(log 2 q)::real\<rceil>"
          "d>0"
  shows "let x' = decompress (compress x d) d in 
         abs ((x' - x) mod+- q) \<le> round ( real_of_int q / real_of_int (2^(d+1)) )" 
proof (cases "x<\<lceil>q-(q/(2*2^d))\<rceil>")
case True
  then have range_x: "x\<in>{0..\<lceil>q-(q/(2*2^d))\<rceil>-1}" using assms(1) by auto
  show ?thesis unfolding Let_def 
    using decompress_compress_no_mod_plus_minus[OF range_x assms(2) assms(3)] by auto
next
case False
  then have range_x: "x\<in>{\<lceil>q-(q/(2*2^d))\<rceil>..q-1}" using assms(1) by auto
  show ?thesis unfolding Let_def using decompress_compress_mod[OF range_x assms(2)] by auto
qed



end

end
