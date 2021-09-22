theory Crypto_Scheme

imports Kyber_spec
        Compress
        Abs_Gf

begin

(* This type corresponds to \<int>q = \<int>/q\<int> *) 
typ "'a mod_ring"

(* This type corresponds to \<int>q[X] *) 
typ "'a mod_ring poly"

(* This type corresponds to \<int>q[X] / (X^n + 1) *) 
typ "'a gf"


(* This type corresponds to vectors in (\<int>q[X] / (X^n + 1))^k *) 
typ "('a gf, 'k) vec"

(* This type corresponds to a \<open>k\<times>k\<close> matrix over \<int>q[X] / (X^n + 1) *) 
typ "(('a gf, 'k) vec, 'k) vec"




context kyber_spec
begin




text \<open>In the following the key generation, encryption and decryption algorithms 
  of Kyber are stated. Here , the variables have the meaning:
  \begin{itemize}
    \item $A$: matrix, part of Alices public key
    \item $s$: vector, Alices sectret key
    \item $t$: is the key generated by Alice from $A$ and $s$ in \<open>key_gen\<close>
    \item $r$: Bobs "secret" key, randomly picked vector
    \item $m$: message bits, $m\in \{0,1\}^{256}$
    \item $(u,v)$: encrypted message
    \item $dt$, $du$, $dv$: the compression parameters for $t$, $u$ and $v$ respectively. 
      Notice that \<open>0 < d < \<lceil>log_2 q\<rceil>\<close>. The $d$ values are public knowledge.
    \item $e$, $e1 and $e2$: error parametrs to obscure the message. 
      We need to make certain that an eavesdropper cannot distinguish 
      the encrypted message from uniformly random input.
      Notice that $e$ and $e1$ are vectors while $e2$ is a mere element in \<open>\<int>_q[X]/(X^n+1).\<close>
  

  \end{itemize}\<close>



definition key_gen :: "nat \<Rightarrow> (('a gf, 'k) vec, 'k) vec \<Rightarrow> ('a gf, 'k) vec \<Rightarrow> 
                ('a gf, 'k) vec \<Rightarrow> ('a gf, 'k) vec" where 
"key_gen dt A s e = compress_vec dt (A *v s + e)"

definition encrypt :: "('a gf, 'k) vec \<Rightarrow> (('a gf, 'k) vec, 'k) vec \<Rightarrow> ('a gf, 'k) vec \<Rightarrow> 
                ('a gf, 'k) vec \<Rightarrow> ('a gf) \<Rightarrow>
                nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
                'a gf \<Rightarrow> (('a gf, 'k) vec) * ('a gf)" where
"encrypt t A r e1 e2 dt du dv m = 
  (compress_vec du ((transpose A) *v r + e1),  
   compress_poly dv (scalar_product (decompress_vec dt t) r + e2 + 
      to_module (round((real_of_int q)/2)) * m)) "


definition decrypt :: "('a gf, 'k) vec \<Rightarrow> ('a gf) \<Rightarrow> ('a gf, 'k) vec \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a gf" where
  "decrypt u v s du dv = compress_poly 1 
      ((decompress_poly dv v) - scalar_product s (decompress_vec du u))"


(*TODO

the matix A, the errors and Alices and Bobs private keys s and r need to be 
randomly generated by some sampling method.
\<Rightarrow> Here stochastical interpretation comes into play!

*)

fun f_int_to_poly :: "(int \<Rightarrow> int) \<Rightarrow> ('a gf) \<Rightarrow> ('a gf)" where
  "f_int_to_poly f = 
        to_gf \<circ>
        Poly \<circ>
        (map of_int_mod_ring) \<circ>
        (map f) \<circ>
        (map to_int_mod_ring) \<circ>
        coeffs \<circ>
        of_gf"

(*
definition mod_plus_minus_poly :: "('a gf) \<Rightarrow> ('a gf)" where
  "mod_plus_minus_poly p = f_int_to_poly (\<lambda>x. x mod+- q) p"

definition mod_plus_minus_vec :: "('a gf, 'k) vec \<Rightarrow> ('a gf, 'k) vec" where
  "mod_plus_minus_vec p = map_vector mod_plus_minus_poly p"
*) 

definition compress_error_poly :: "nat \<Rightarrow> 'a gf \<Rightarrow> 'a gf" where
  "compress_error_poly d y = decompress_poly d (compress_poly d y) - y"

definition compress_error_vec :: "nat \<Rightarrow> ('a gf, 'k) vec \<Rightarrow> ('a gf, 'k) vec" where
  "compress_error_vec d y = decompress_vec d (compress_vec d y) - y"

text \<open>Lemmas for scalar product\<close>


lemma scalar_product_linear_left:
  "scalar_product (a+b) c = scalar_product a c + scalar_product b (c :: ('a gf, 'k) vec)"
unfolding scalar_product_def
by auto (metis (no_types, lifting) distrib_right sum.cong sum.distrib)

lemma scalar_product_linear_right:
  "scalar_product a (b+c) = scalar_product a b + scalar_product a (c :: ('a gf, 'k) vec)"
unfolding scalar_product_def
by auto (metis (no_types, lifting) distrib_left sum.cong sum.distrib)

lemma scalar_product_assoc:
  "scalar_product (A *v s) (r :: ('a gf, 'k) vec ) = scalar_product s (r v* A)"
unfolding scalar_product_def matrix_vector_mult_def vector_matrix_mult_def
proof auto
  have "(\<Sum>i\<in>UNIV. (\<Sum>j\<in>UNIV. (vec_nth (vec_nth A i) j) * (vec_nth s j)) * (vec_nth r i)) = 
        (\<Sum>i\<in>UNIV. (\<Sum>j\<in>UNIV. (vec_nth (vec_nth A i) j) * (vec_nth s j) * (vec_nth r i)))"
    by (simp add: sum_distrib_right)
  also have "\<dots> = (\<Sum>j\<in>UNIV. (\<Sum>i\<in>UNIV. (vec_nth (vec_nth A i) j) * (vec_nth s j) * (vec_nth r i)))"
    using sum.swap .
  also have "\<dots> = (\<Sum>j\<in>UNIV. (\<Sum>i\<in>UNIV. (vec_nth s j) * (vec_nth (vec_nth A i) j) * (vec_nth r i)))"
    by (metis (no_types, lifting) mult_commute_abs sum.cong)
  also have "\<dots> = (\<Sum>j\<in>UNIV. (vec_nth s j) * (\<Sum>i\<in>UNIV. (vec_nth (vec_nth A i) j) * (vec_nth r i)))"
    by (metis (no_types, lifting) mult.assoc sum.cong sum_distrib_left)
  finally show "(\<Sum>i\<in>UNIV. (\<Sum>j\<in>UNIV. (vec_nth (vec_nth A i) j) * (vec_nth s j)) * (vec_nth r i)) =
    (\<Sum>j\<in>UNIV. (vec_nth s j) * (\<Sum>i\<in>UNIV. (vec_nth (vec_nth A i) j) * (vec_nth r i)))" by blast
qed

text \<open>Lemma about coeff Poly\<close>

lemma set_coeff_Poly: "set ((coeffs \<circ> Poly) xs) \<subseteq> set xs" 
by auto (metis append.assoc append_Cons in_set_conv_decomp split_strip_while_append) 

text \<open>We now want to show the deterministic correctness of the algorithm. 
  That means, after choosing the variables correctly, generating the public key, encrypting 
  and decrypting, we get back the original message.\<close>



lemma kyber_correct:
  fixes A s r e e1 e2 dt du dv ct cu cv t u v
  assumes "t = key_gen dt A s e"
          "(u,v) = encrypt t A r e1 e2 dt du dv m"
          "ct = compress_error_vec dt (A *v s + e)"
          "cu = compress_error_vec du ((transpose A) *v r + e1)"
          "cv = compress_error_poly dv (scalar_product (decompress_vec dt t) r + e2 + 
            to_module (round((real_of_int q)/2)) * m)"
          "abs_infty_poly (scalar_product e r + e2 + cv - scalar_product s e1 + 
            scalar_product ct r - scalar_product s cu) < round (real_of_int q / 4)"
          "set ((coeffs \<circ> of_gf) m) \<subseteq> {0,1}"
          "degree (of_gf m) < n"
  shows "decrypt u v s du dv = m"
proof -
  text \<open>First, show that the calculations are performed correctly.\<close>
  have t_correct: "decompress_vec dt t = A *v s + e + ct " 
    using assms(1) assms(3) unfolding compress_error_vec_def key_gen_def by simp
  have u_correct: "decompress_vec du u = (transpose A) *v r + e1 + cu" 
    using assms(2) assms(4) unfolding encrypt_def compress_error_vec_def by simp
  have v_correct: "decompress_poly dv v = scalar_product (decompress_vec dt t) r + e2 + 
            to_module (round((real_of_int q)/2)) * m + cv"
    using assms(2) assms(5) unfolding encrypt_def compress_error_poly_def by simp
  have v_correct': "decompress_poly dv v = scalar_product (A *v s + e) r + e2 + 
            to_module (round((real_of_int q)/2)) * m + cv + scalar_product ct r"
   using t_correct v_correct by (auto simp add: scalar_product_linear_left)
  let ?t = "decompress_vec dt t"
  let ?u = "decompress_vec du u"
  let ?v = "decompress_poly dv v"
  text \<open>Define w as the error term of the message encoding. Have $\|w\|_{\infty ,q} < \lceil q/4 \rfloor$\<close>
  define w where "w = scalar_product e r + e2 + cv - scalar_product s e1 + 
            scalar_product ct r - scalar_product s cu"
  have w_length: "abs_infty_poly w < round (real_of_int q / 4)" 
    unfolding w_def using assms(6) by auto
  moreover have "abs_infty_poly w = abs_infty_poly (-w)" 
    unfolding abs_infty_poly_def using neg_mod_plus_minus[OF q_odd q_gt_zero] 
    using abs_infty_q_def abs_infty_q_minus by auto
  ultimately have minus_w_length: "abs_infty_poly (-w) < round (real_of_int q / 4)" by auto
  have vsu: "?v - scalar_product s ?u = 
        w + to_module (round((real_of_int q)/2)) * m" 
    unfolding w_def by (auto simp add: u_correct v_correct' scalar_product_linear_left 
                       scalar_product_linear_right scalar_product_assoc)
  text \<open>Set m' as the actual result of the decryption. It remains to show that $m' = m$.\<close>
  define m' where "m' = decrypt u v s du dv"
  have coeffs_m': "\<forall>i. poly.coeff (of_gf m') i \<in> {0,1}" 
    unfolding m'_def decrypt_def using compress_poly_1 by auto
  text \<open>Show $\| v - s^Tu - \lceil q/2 \rfloor m' \|_{\infty, q} \leq \lceil q/4 \rfloor$\<close>
  have "abs_infty_poly (?v - scalar_product s ?u - to_module (round((real_of_int q)/2)) * m')
        = abs_infty_poly (?v - scalar_product s ?u - 
          decompress_poly 1 (compress_poly 1 (?v - scalar_product s ?u)))"
    by (auto simp flip: decompress_poly_1[of m', OF coeffs_m'])(simp add:m'_def decrypt_def)
  also have "\<dots> \<le> round (real_of_int q / 4)" 
    using decompress_compress_poly[of 1 "?v - scalar_product s ?u"] q_gt_two by fastforce
  finally have "abs_infty_poly (?v - scalar_product s ?u - to_module (round((real_of_int q)/2)) * m') \<le> 
        round (real_of_int q / 4)"
    by auto
  text \<open>Show $\| \lceil q/2 \rfloor (m-m')) \|_{\infty, q} < 2 \lceil q/4 \rfloor $\<close>
  then have "abs_infty_poly (w + to_module (round((real_of_int q)/2)) * m - 
              to_module (round((real_of_int q)/2)) * m') \<le> round (real_of_int q / 4)" 
    using vsu by auto
  then have w_mm': "abs_infty_poly (w + to_module (round((real_of_int q)/2)) * (m - m')) 
    \<le> round (real_of_int q / 4)" 
    by (smt (verit) add_uminus_conv_diff is_num_normalize(1) right_diff_distrib')
  have "abs_infty_poly (to_module (round((real_of_int q)/2)) * (m - m')) = 
        abs_infty_poly (w + to_module (round((real_of_int q)/2)) * (m - m') - w)"
    by auto
  also have "\<dots> \<le> abs_infty_poly (w + to_module (round((real_of_int q)/2)) * (m - m')) 
                + abs_infty_poly (- w)"
    using abs_infty_poly_triangle_ineq[of "w+to_module (round((real_of_int q)/2)) * (m - m')" "-w"] 
    by auto
  also have "\<dots> < 2 * round (real_of_int q / 4)" using w_mm' minus_w_length by auto
  finally have "abs_infty_poly (to_module (round((real_of_int q)/2)) * (m - m')) < 
              2 * round (real_of_int q / 4)" 
    by auto

  text \<open>Finally show that $m-m'$ is small enough, ie that it is an integer smaller than one. 
    Here, we need that $q \cong 1\mod 4$.\<close>
  have "set ((coeffs \<circ> of_gf) m') \<subseteq> {0,1}" sorry
  then have coeff_0pm1: "set ((coeffs \<circ> of_gf) (m-m')) \<subseteq> {of_int_mod_ring (-1),0,1}" sorry
  have "set ((coeffs \<circ> of_gf) (m-m')) \<subseteq> {0}"
  proof (rule ccontr)
    assume "\<not>set ((coeffs \<circ> of_gf) (m-m')) \<subseteq> {0}"
    then have "\<exists>i. poly.coeff (of_gf (m-m')) i \<in> {of_int_mod_ring (-1),1}" using coeff_0pm1 sorry
    then have 

  have "abs_infty_poly (m - m') = 0" 
  proof(rule ccontr)
    assume "\<not> abs_infty_poly (m - m') = 0"
    then have "MAX x. abs_infty_q (poly.coeff (of_gf (m-m')) x) \<in> {-1,1}" 
      unfolding abs_infty_poly_def using coeff_0pm1 
    then show False
      sorry
  qed
  then have "abs_infty_poly (m-m') = 0" using abs_infty_poly_pos[of "m-m'"] by auto
  then show ?thesis by (simp flip: m'_def add: abs_infty_poly_definite)

(*(*Problem: scaling in abs_infty is only true for inequality not equality. To repair proof,
  we need to make the assumption that q=1 mod 4*)

  text \<open>Finally show that $m-m'$ is small enough. 
    Since we know that m and m' have integer coefficients, it is enough to show that 
    \<open>abs_infty_poly (m-m') <1\<close>.\<close>         
  then have "(round((real_of_int q)/2)) * abs_infty_poly (m - m') < 
              2 * round (real_of_int q / 4)" 
    using abs_infty_poly_scale[of "round((real_of_int q)/2)" "m-m'"] sorry
    by (smt (verit, best) abs_infty_poly_pos minus_mult_minus mult_minus_right)
  moreover have "round((real_of_int q)/2) > 0" using q_gt_two
    by (smt (z3) divide_less_eq_1_pos of_int_add of_int_hom.hom_one round_mono round_of_int)
  ultimately have " abs_infty_poly (m - m') < 2 * round (real_of_int q / 4)
      / (round((real_of_int q)/2))" 
    by (metis mult.commute of_int_hom.hom_mult of_int_less_iff of_int_pos pos_less_divide_eq)
  also have "\<dots> = 2 * round (real_of_int q / 4) / (q+1) * 2"
  proof -
    have one: "round((real_of_int q)/2) = (q+1)/2" using q_odd unfolding round_def
    by (smt (verit, ccfv_threshold) add_divide_distrib even_plus_one_iff of_int_1_less_iff 
      of_int_floor_cancel of_int_hom.hom_add of_int_hom.hom_one of_int_hom.hom_one 
      of_int_less_1_iff real_of_int_div)
    show ?thesis by (simp add: one)
  qed
  also have "\<dots> \<le> 4 * ((q+1) / 4) / (q+1)" 
  proof -
    have "round (real_of_int q / 4) \<le> (q+1) / 4" 
    proof -
      consider (one) "q mod 4 = 1" | (three) "q mod 4 = 3" using q_odd 
      by (smt (z3) Euclidean_Division.pos_mod_bound Euclidean_Division.pos_mod_sign 
        even_numeral int_of_integer_numeral mod2_eq_if mod_mod_cancel numeral_Bit0 
        numeral_One one_integer.rep_eq)
      then show ?thesis
      proof (cases)
      case one
        then obtain a where a_def: "q = a*4 + 1" by (simp add: q_def)
        then have q_4: "real_of_int q / 4 = \<lfloor>real_of_int q / 4\<rfloor> + 1/4" using a_def by simp
        then have "round (real_of_int q / 4) = round(\<lfloor>real_of_int q / 4\<rfloor> + 1/4)"
          by presburger
        also have "\<dots> = \<lfloor>real_of_int q / 4\<rfloor>" unfolding round_def by simp
        finally have "round (real_of_int q / 4) = (q-1)/4" unfolding round_def using q_4 by simp
        then show ?thesis by auto
      next
      case three
        then obtain a where a_def: "q = a*4 + 3" by (simp add: q_def)
        then have q_4: "real_of_int q / 4 = \<lfloor>real_of_int q / 4\<rfloor> + 3/4" using a_def by simp
        then have "round (real_of_int q / 4) = round(\<lfloor>real_of_int q / 4\<rfloor> + 3/4)"
          by presburger
        also have "\<dots> = \<lfloor>real_of_int q / 4\<rfloor> + 1" unfolding round_def by simp
        finally have "round (real_of_int q / 4) = (q+1)/4" unfolding round_def using q_4 by simp
        then show ?thesis by auto
      qed
    qed
    then show ?thesis using q_gt_zero by force
  qed
  finally have "abs_infty_poly (m - m') < 1" using q_gt_zero by simp
  then have "abs_infty_poly (m-m') = 0" using abs_infty_poly_pos[of "m-m'"] by auto
  then show ?thesis by (simp flip: m'_def add: abs_infty_poly_definite)
*)
qed





lemma kyber_one_minus_delta_correct:
  assumes "delta = P ()"








(*
fun sample_matrix where "sample_matrix k rho = TODO"

fun Sample_vector where "Sample beta_eta_k sigma = TODO"

type seed = int

fun key_gen :: "seed \<Rightarrow> seed \<Rightarrow> vector" where 
"key_gen rho sigma = (compress q (A s + e) d_t) where A
= sample_matrix q k rho and (s,e) = sample_vector beta_eta_k sigma"
*)













end

end
