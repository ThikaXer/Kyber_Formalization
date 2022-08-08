theory Crypto_Scheme

imports Kyber_spec
        Compress
        Abs_Qr

begin
section \<open>$\delta$-Correctness Proof of the Kyber Crypto Scheme\<close>
context kyber_spec
begin

text \<open>In the following the key generation, encryption and decryption algorithms 
  of Kyber are stated. Here, the variables have the meaning:
  \begin{itemize}
    \item $A$: matrix, part of Alices public key
    \item $s$: vector, Alices secret key
    \item $t$: is the key generated by Alice qrom $A$ and $s$ in \<open>key_gen\<close>
    \item $r$: Bobs "secret" key, randomly picked vector
    \item $m$: message bits, $m\in \{0,1\}^{256}$
    \item $(u,v)$: encrypted message
    \item $dt$, $du$, $dv$: the compression parameters for $t$, $u$ and $v$ respectively. 
      Notice that \<open>0 < d < \<lceil>log_2 q\<rceil>\<close>. The $d$ values are public knowledge.
    \item $e$, $e1$ and $e2$: error parameters to obscure the message. 
      We need to make certain that an eavesdropper cannot distinguish 
      the encrypted message qrom uniformly random input.
      Notice that $e$ and $e1$ are vectors while $e2$ is a mere element in \<open>\<int>_q[X]/(X^n+1).\<close>
  \end{itemize}
\<close>


definition key_gen :: 
  "nat \<Rightarrow> (('a qr, 'k) vec, 'k) vec \<Rightarrow> ('a qr, 'k) vec \<Rightarrow> 
   ('a qr, 'k) vec \<Rightarrow> ('a qr, 'k) vec" where 
"key_gen dt A s e = compress_vec dt (A *v s + e)"

definition encrypt :: 
  "('a qr, 'k) vec \<Rightarrow> (('a qr, 'k) vec, 'k) vec \<Rightarrow> 
   ('a qr, 'k) vec \<Rightarrow> ('a qr, 'k) vec \<Rightarrow> ('a qr) \<Rightarrow> 
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a qr \<Rightarrow> 
   (('a qr, 'k) vec) * ('a qr)" where
"encrypt t A r e1 e2 dt du dv m = 
  (compress_vec du ((transpose A) *v r + e1),  
   compress_poly dv (scalar_product (decompress_vec dt t) r +
    e2 + to_module (round((real_of_int q)/2)) * m)) "


definition decrypt :: 
  "('a qr, 'k) vec \<Rightarrow> ('a qr) \<Rightarrow> ('a qr, 'k) vec \<Rightarrow> 
  nat \<Rightarrow> nat \<Rightarrow> 'a qr" where
"decrypt u v s du dv = compress_poly 1 ((decompress_poly dv v) - 
  scalar_product s (decompress_vec du u))"



text \<open>Lifting a function to the quotient ring\<close>
fun f_int_to_poly :: "(int \<Rightarrow> int) \<Rightarrow> ('a qr) \<Rightarrow> ('a qr)" where
  "f_int_to_poly f = 
        to_qr \<circ>
        Poly \<circ>
        (map of_int_mod_ring) \<circ>
        (map f) \<circ>
        (map to_int_mod_ring) \<circ>
        coeffs \<circ>
        of_qr"


text \<open>Error of compression and decompression.\<close>
definition compress_error_poly :: 
  "nat \<Rightarrow> 'a qr \<Rightarrow> 'a qr" where
"compress_error_poly d y = 
  decompress_poly d (compress_poly d y) - y"

definition compress_error_vec :: 
  "nat \<Rightarrow> ('a qr, 'k) vec \<Rightarrow> ('a qr, 'k) vec" where
"compress_error_vec d y = 
  decompress_vec d (compress_vec d y) - y"


text \<open>Lemmas for scalar product\<close>
lemma scalar_product_linear_left:
  "scalar_product (a+b) c = 
   scalar_product a c + scalar_product b (c :: ('a qr, 'k) vec)"
unfolding scalar_product_def
by auto (metis (no_types, lifting) distrib_right sum.cong sum.distrib)

lemma scalar_product_linear_right:
  "scalar_product a (b+c) = 
   scalar_product a b + scalar_product a (c :: ('a qr, 'k) vec)"
unfolding scalar_product_def
by auto (metis (no_types, lifting) distrib_left sum.cong sum.distrib)

lemma scalar_product_assoc:
  "scalar_product (A *v s) (r :: ('a qr, 'k) vec ) = 
   scalar_product s (r v* A)"
unfolding scalar_product_def matrix_vector_mult_def 
  vector_matrix_mult_def
proof auto
  have "(\<Sum>i\<in>UNIV. (\<Sum>j\<in>UNIV. (vec_nth (vec_nth A i) j) * 
      (vec_nth s j)) * (vec_nth r i)) = 
    (\<Sum>i\<in>UNIV. (\<Sum>j\<in>UNIV. (vec_nth (vec_nth A i) j) * 
      (vec_nth s j) * (vec_nth r i)))"
    by (simp add: sum_distrib_right)
  also have "\<dots> = (\<Sum>j\<in>UNIV. (\<Sum>i\<in>UNIV. (vec_nth (vec_nth A i) j) * 
    (vec_nth s j) * (vec_nth r i)))"
    using sum.swap .
  also have "\<dots> = (\<Sum>j\<in>UNIV. (\<Sum>i\<in>UNIV. (vec_nth s j) * 
    (vec_nth (vec_nth A i) j) * (vec_nth r i)))"
    by (metis (no_types, lifting) mult_commute_abs sum.cong)
  also have "\<dots> = (\<Sum>j\<in>UNIV. (vec_nth s j) * 
    (\<Sum>i\<in>UNIV. (vec_nth (vec_nth A i) j) * (vec_nth r i)))"
    by (metis (no_types, lifting) mult.assoc sum.cong sum_distrib_left)
  finally show "(\<Sum>i\<in>UNIV. (\<Sum>j\<in>UNIV. (vec_nth (vec_nth A i) j) * 
    (vec_nth s j)) * (vec_nth r i)) = (\<Sum>j\<in>UNIV. (vec_nth s j) * 
    (\<Sum>i\<in>UNIV. (vec_nth (vec_nth A i) j) * (vec_nth r i)))" 
    by blast
qed

text \<open>Lemma about coeff Poly\<close>

lemma coeffs_in_coeff:
  assumes "\<forall>i. poly.coeff x i \<in> A"
  shows "set (coeffs x) \<subseteq> A"
by (simp add: assms coeffs_def image_subsetI)

lemma set_coeff_Poly: "set ((coeffs \<circ> Poly) xs) \<subseteq> set xs"
proof -
  have "x \<in> set (strip_while ((=) 0) xs) \<Longrightarrow> x \<in> set xs" 
    for x 
    by (metis append.assoc append_Cons in_set_conv_decomp 
      split_strip_while_append) 
  then show ?thesis by auto
qed

text \<open>We now want to show the deterministic correctness of the algorithm. 
  That means, after choosing the variables correctly, generating the public key, encrypting 
  and decrypting, we get back the original message.\<close>

lemma kyber_correct:
  fixes A s r e e1 e2 dt du dv ct cu cv t u v
  assumes 
      t_def:   "t = key_gen dt A s e"
  and u_v_def: "(u,v) = encrypt t A r e1 e2 dt du dv m"
  and ct_def:  "ct = compress_error_vec dt (A *v s + e)"
  and cu_def:  "cu = compress_error_vec du 
                ((transpose A) *v r + e1)"
  and cv_def:  "cv = compress_error_poly dv 
                (scalar_product (decompress_vec dt t) r + e2 + 
                 to_module (round((real_of_int q)/2)) * m)"
  and delta:   "abs_infty_poly (scalar_product e r + e2 + cv - 
                scalar_product s e1 + scalar_product ct r - 
                scalar_product s cu) < round (real_of_int q / 4)"
  and m01:     "set ((coeffs \<circ> of_qr) m) \<subseteq> {0,1}"
  shows "decrypt u v s du dv = m"
proof -
  text \<open>First, show that the calculations are performed correctly.\<close>
  have t_correct: "decompress_vec dt t = A *v s + e + ct " 
    using t_def ct_def unfolding compress_error_vec_def 
    key_gen_def by simp
  have u_correct: "decompress_vec du u = 
    (transpose A) *v r + e1 + cu" 
    using u_v_def cu_def unfolding encrypt_def 
    compress_error_vec_def by simp
  have v_correct: "decompress_poly dv v = 
    scalar_product (decompress_vec dt t) r + e2 + 
    to_module (round((real_of_int q)/2)) * m + cv"
    using u_v_def cv_def unfolding encrypt_def 
    compress_error_poly_def by simp
  have v_correct': "decompress_poly dv v = 
    scalar_product (A *v s + e) r + e2 + 
    to_module (round((real_of_int q)/2)) * m + cv + 
    scalar_product ct r"
   using t_correct v_correct 
    by (auto simp add: scalar_product_linear_left)
  let ?t = "decompress_vec dt t"
  let ?u = "decompress_vec du u"
  let ?v = "decompress_poly dv v"
  text \<open>Define w as the error term of the message encoding. 
    Have $\|w\|_{\infty ,q} < \lceil q/4 \rfloor$\<close>
  define w where "w = scalar_product e r + e2 + cv - 
    scalar_product s e1 + scalar_product ct r - 
    scalar_product s cu"
  have w_length: "abs_infty_poly w < round (real_of_int q / 4)" 
    unfolding w_def using delta by auto
  moreover have "abs_infty_poly w = abs_infty_poly (-w)" 
    unfolding abs_infty_poly_def 
    using neg_mod_plus_minus[OF q_odd q_gt_zero] 
    using abs_infty_q_def abs_infty_q_minus by auto
  ultimately have minus_w_length: 
    "abs_infty_poly (-w) < round (real_of_int q / 4)" 
    by auto
  have vsu: "?v - scalar_product s ?u = 
        w + to_module (round((real_of_int q)/2)) * m" 
    unfolding w_def by (auto simp add: u_correct v_correct' 
    scalar_product_linear_left scalar_product_linear_right 
    scalar_product_assoc)
  text \<open>Set m' as the actual result of the decryption. 
    It remains to show that $m' = m$.\<close>
  define m' where "m' = decrypt u v s du dv"
  have coeffs_m': "\<forall>i. poly.coeff (of_qr m') i \<in> {0,1}" 
    unfolding m'_def decrypt_def using compress_poly_1 by auto
  text \<open>Show $\| v - s^Tu - \lceil q/2 \rfloor m' \|_{\infty, q} 
    \leq \lceil q/4 \rfloor$\<close>
  have "abs_infty_poly (?v - scalar_product s ?u - 
    to_module (round((real_of_int q)/2)) * m')
  = abs_infty_poly (?v - scalar_product s ?u - 
    decompress_poly 1 (compress_poly 1 (?v - scalar_product s ?u)))"
    by (auto simp flip: decompress_poly_1[of m', OF coeffs_m'])
       (simp add:m'_def decrypt_def)
  also have "\<dots> \<le> round (real_of_int q / 4)" 
    using decompress_compress_poly[of 1 "?v - scalar_product s ?u"] 
      q_gt_two by fastforce
  finally have "abs_infty_poly (?v - scalar_product s ?u - 
    to_module (round((real_of_int q)/2)) * m') \<le> 
    round (real_of_int q / 4)"
    by auto
  text \<open>Show $\| \lceil q/2 \rfloor (m-m')) \|_{\infty, q} < 
    2 \lceil q/4 \rfloor $\<close>
  then have "abs_infty_poly (w + to_module 
    (round((real_of_int q)/2)) * m - to_module 
    (round((real_of_int q)/2)) * m') \<le> round (real_of_int q / 4)" 
    using vsu by auto
  then have w_mm': "abs_infty_poly (w + 
    to_module (round((real_of_int q)/2)) * (m - m'))
    \<le> round (real_of_int q / 4)" 
    by (smt (verit) add_uminus_conv_diff is_num_normalize(1) 
      right_diff_distrib')
  have "abs_infty_poly (to_module 
      (round((real_of_int q)/2)) * (m - m')) = 
    abs_infty_poly (w + to_module 
      (round((real_of_int q)/2)) * (m - m') - w)"
    by auto
  also have "\<dots> \<le> abs_infty_poly 
    (w + to_module (round((real_of_int q)/2)) * (m - m')) 
     + abs_infty_poly (- w)"
    using abs_infty_poly_triangle_ineq[of 
      "w+to_module (round((real_of_int q)/2)) * (m - m')" "-w"] 
    by auto
  also have "\<dots> < 2 * round (real_of_int q / 4)" 
    using w_mm' minus_w_length by auto
  finally have error_lt: "abs_infty_poly (to_module 
    (round((real_of_int q)/2)) * (m - m')) < 
    2 * round (real_of_int q / 4)" 
    by auto
  text \<open>Finally show that $m-m'$ is small enough, ie that it is 
    an integer smaller than one. 
    Here, we need that $q \cong 1\mod 4$.\<close>
  have coeffs_m':"set ((coeffs \<circ> of_qr) m') \<subseteq> {0,1}" 
  proof -
    have "compress 1 a \<in> {0,1}" for a 
    unfolding compress_def by auto
    then have "poly.coeff (of_qr (compress_poly 1 a)) i \<in> {0,1}" 
      for a i
      using compress_poly_1 by presburger
    then have "set (coeffs (of_qr (compress_poly 1 a))) \<subseteq> {0,1}" 
      for a 
      using coeffs_in_coeff[of "of_qr (compress_poly 1 a)" "{0,1}"] 
      by simp
    then show ?thesis unfolding m'_def decrypt_def by simp
  qed
  have coeff_0pm1: "set ((coeffs \<circ> of_qr) (m-m')) \<subseteq> 
    {of_int_mod_ring (-1),0,1}"
  proof -
    have "poly.coeff (of_qr m) i \<in> {0,1}" 
      for i using m01 coeff_in_coeffs
      by (metis comp_def insertCI le_degree subset_iff 
        zero_poly.rep_eq)
    moreover have "poly.coeff (of_qr m') i \<in> {0,1}" for i 
      using coeffs_m' coeff_in_coeffs
      by (metis comp_def insertCI le_degree subset_iff zero_poly.rep_eq)
    ultimately have "poly.coeff (of_qr m - of_qr m') i \<in> 
      {of_int_mod_ring (- 1), 0, 1}" for i
      by (metis (no_types, lifting) coeff_diff diff_zero 
        eq_iff_diff_eq_0 insert_iff of_int_hom.hom_one of_int_minus 
        of_int_of_int_mod_ring singleton_iff verit_minus_simplify(3))
    then have "set (coeffs (of_qr m - of_qr m')) \<subseteq> 
      {of_int_mod_ring (- 1), 0, 1}" 
      by (simp add: coeffs_in_coeff)
    then show ?thesis using m01 of_qr_diff[of m m'] by simp
  qed
  have "set ((coeffs \<circ> of_qr) (m-m')) \<subseteq> {0}"
  proof (rule ccontr)
    assume "\<not>set ((coeffs \<circ> of_qr) (m-m')) \<subseteq> {0}"
    then have "\<exists>i. poly.coeff (of_qr (m-m')) i \<in> 
      {of_int_mod_ring (-1),1}" 
      using coeff_0pm1 
      by (smt (z3) coeff_in_coeffs comp_apply insert_iff 
        leading_coeff_0_iff order_refl 
        set_coeffs_subset_singleton_0_iff subsetD)
    then have error_ge: "abs_infty_poly (to_module 
      (round((real_of_int q)/2)) * (m-m')) \<ge> 
      2 * round (real_of_int q / 4)" 
      using abs_infty_poly_ineq_pm_1 by simp
    show False using error_lt error_ge by simp
  qed
  then show ?thesis by (simp flip: m'_def) (metis to_qr_of_qr)
qed


end

end
