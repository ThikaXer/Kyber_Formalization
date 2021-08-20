theory Key_gen

imports Kyber_spec
        Compress

begin

(* This type corresponds to ℤq = ℤ/qℤ *) 
typ "'a mod_ring"

(* This type corresponds to ℤq[X] *) 
typ "'a mod_ring poly"

(* This type corresponds to ℤq[X] / (X^n + 1) *) 
typ "'a gf"














(*
fun sample_matrix where "sample_matrix k rho = TODO"

fun Sample_vector where "Sample beta_eta_k sigma = TODO"

type seed = int

fun key_gen :: "seed ⇒ seed ⇒ vector" where 
"key_gen rho sigma = (compress q (A s + e) d_t) where A
= sample_matrix q k rho and (s,e) = sample_vector beta_eta_k sigma"
*)















end
