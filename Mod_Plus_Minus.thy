theory Mod_Plus_Minus

imports Kyber_spec

begin

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

lemma mod_plus_minus_range: 
  assumes "b>0"
  shows "y mod+- b \<in> {-\<lfloor>b/2\<rfloor>..\<lfloor>b/2\<rfloor>}"
unfolding mod_plus_minus_def using mod_range[OF assms, of "(y + \<lfloor>real_of_int b / 2\<rfloor>)"]
by (auto)(linarith)

lemma odd_smaller_b:
  assumes "odd b" 
  shows "\<lfloor> real_of_int b / 2 \<rfloor> + \<lfloor> real_of_int b / 2 \<rfloor> < b"
using assms 
by (smt (z3) floor_divide_of_int_eq odd_two_times_div_two_succ 
  of_int_hom.hom_add of_int_hom.hom_one)

lemma mod_plus_minus_rangeE:
  assumes "y \<in> {-\<lfloor>real_of_int b/2\<rfloor>..<\<lfloor>real_of_int b/2\<rfloor>}"
          "odd b"
  shows "y = y mod+- b"
proof -
  have "(y + \<lfloor> real_of_int b / 2 \<rfloor>) \<in> {0..<b}" 
    using assms(1) odd_smaller_b[OF assms(2)] by auto
  then have "(y + \<lfloor> real_of_int b / 2 \<rfloor>) mod b = (y + \<lfloor> real_of_int b / 2 \<rfloor>)" 
    using mod_rangeE by auto
  then show ?thesis unfolding mod_plus_minus_def by auto
qed

lemma mod_plus_minus_zero:
  assumes "x mod+- b = 0"
  shows "x mod b = 0"
using assms unfolding mod_plus_minus_def
by (metis add.commute add.right_neutral bits_mod_0 diff_add_cancel 
  group_cancel.add1 mod_add_left_eq)

lemma mod_plus_minus_zero':
  assumes "b>0" "odd b"
  shows "0 mod+- b = (0::int)"
using mod_plus_minus_rangeE[of 0] 
by (smt (verit, best) assms(1) assms(2) atLeastAtMost_iff 
  atLeastLessThan_iff mod_plus_minus_range)

end