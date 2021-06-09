theory ETCS_Mult
  imports ETCS_Add
begin

(*Defining multiplication on N*)
  



definition mult1 :: "cfunc" where
  "mult1 = (THE v. v: \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<and>
    triangle_commutes one \<nat>\<^sub>c  (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) zero v ((zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c one))\<^sup>\<sharp>) \<and>
    square_commutes \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) v 
      ((add2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>) successor v)"



lemma mult1_property: "mult1: \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<and>
  triangle_commutes one \<nat>\<^sub>c  (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) zero mult1 ((zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c one))\<^sup>\<sharp>) \<and>
  square_commutes \<nat>\<^sub>c  (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) mult1 
    ((add2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>) successor mult1"
  unfolding mult1_def
proof (rule theI')
  have q_type: "((zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c one))\<^sup>\<sharp>) :  one \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
    by typecheck_cfuncs
  have f_type: "((add2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>) : (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<rightarrow> (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)"
    by typecheck_cfuncs
  show "\<exists>!x. x : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<and>
          triangle_commutes one \<nat>\<^sub>c  (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) zero x ((zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c one))\<^sup>\<sharp>) \<and>
         square_commutes \<nat>\<^sub>c  (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) x 
((add2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>) successor x"
    by (simp add: f_type natural_number_object_property q_type)
qed


lemma mult1_type[type_rule]: "mult1:  \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
  by (simp add: mult1_property)


lemma mult1_0_eq: "mult1 \<circ>\<^sub>c zero = ((zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c one))\<^sup>\<sharp>)"
  using mult1_property triangle_commutes_def by blast

lemma mult1_comp_succ_eq: "mult1 \<circ>\<^sub>c successor =
  ((add2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c mult1"
  using mult1_property square_commutes_def by auto


definition mult2 :: "cfunc"
  where "mult2 = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f mult1)"

lemma mult2_type[type_rule]: "mult2:  \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c"
  unfolding mult2_def
proof - 
  have "id \<nat>\<^sub>c \<times>\<^sub>f mult1 : \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<times>\<^sub>c(\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)"
    by (simp add: cfunc_cross_prod_type id_type mult1_type)
  then show "eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult1) : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    using comp_type eval_func_type by blast
qed

(*
lemma f_mult_type: "(add2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>: (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<rightarrow> (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)"
  using mult1_property square_commutes_def by auto

lemma f_mult_flat_type: "(add2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>) : (\<nat>\<^sub>c \<times>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)) \<rightarrow> \<nat>\<^sub>c"
  by (meson add2_type cfunc_prod_type comp_type eval_func_type left_cart_proj_type)
*)

definition mult :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" (infixl "\<cdot>\<^sub>\<nat>" 70)
  where "m \<cdot>\<^sub>\<nat> n = mult2\<circ>\<^sub>c\<langle>m, n\<rangle>"

lemma mult_def2:
  assumes "m\<in>\<^sub>c  \<nat>\<^sub>c" "n\<in>\<^sub>c  \<nat>\<^sub>c"
  shows "m \<cdot>\<^sub>\<nat> n = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, mult1 \<circ>\<^sub>c n\<rangle>"
  unfolding mult_def mult2_def
  using assms 
  by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod comp_associative2 id_left_unit2)


lemma mult_apply1right:
  assumes "m\<in>\<^sub>c  \<nat>\<^sub>c" "n\<in>\<^sub>c  \<nat>\<^sub>c"
  shows  "m \<cdot>\<^sub>\<nat> n = mult2 \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<circ>\<^sub>c n"
  unfolding mult_def
proof -  
  have fact1: "m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>:\<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    using assms(1) comp_type terminal_func_type by blast
  have "mult2 \<circ>\<^sub>c \<langle>m,n\<rangle> = mult2 \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c id one  ,id \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>"
    by (metis assms cfunc_type_def id_left_unit id_right_unit)
  also have "... = mult2 \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c n)  ,id \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>"
    by (metis assms(2) comp_type id_type one_unique_element terminal_func_type)
  also have "... = mult2 \<circ>\<^sub>c \<langle>(m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c n  ,id \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>"
    using assms by (typecheck_cfuncs, simp add: comp_associative2)
  also have "... = mult2 \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<circ>\<^sub>c n"
    using assms(2) cfunc_prod_comp fact1 id_type by fastforce
  then show "mult2 \<circ>\<^sub>c \<langle>m,n\<rangle> = mult2 \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c n" 
    using calculation by auto
qed

lemma mult_apply1_left:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n\<in>\<^sub>c \<nat>\<^sub>c"
  shows "m  \<cdot>\<^sub>\<nat>  n = mult2 \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<circ>\<^sub>c m"
  unfolding mult_def 
proof - 
  have fact1: "n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>:\<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    using assms(2) comp_type terminal_func_type by blast
  have "mult2 \<circ>\<^sub>c \<langle>m,n\<rangle> = mult2 \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c \<circ>\<^sub>c m, n \<circ>\<^sub>c id one\<rangle>"
    by (metis assms cfunc_type_def id_left_unit id_right_unit)
  also have "... = mult2 \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c \<circ>\<^sub>c m, n \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m)\<rangle>"
    by (metis assms(1) comp_type id_type one_unique_element terminal_func_type)
  also have "... = mult2 \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c \<circ>\<^sub>c m, (n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c m\<rangle>"
    using assms by (typecheck_cfuncs, simp add: comp_associative2)
  also have "... = mult2 \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<rangle> \<circ>\<^sub>c m"
    using assms(1) cfunc_prod_comp fact1 id_type by fastforce
  then show "mult2 \<circ>\<^sub>c \<langle>m,n\<rangle> = mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c m" 
    using calculation by auto
qed

lemma mult_closure:
  assumes "m \<in>\<^sub>c  \<nat>\<^sub>c" "n\<in>\<^sub>c  \<nat>\<^sub>c"
  shows "m \<cdot>\<^sub>\<nat> n \<in>\<^sub>c  \<nat>\<^sub>c"
  unfolding mult_def
  using assms by typecheck_cfuncs

lemma mult_respects_zero_right:
  assumes "m\<in>\<^sub>c  \<nat>\<^sub>c"
  shows "m \<cdot>\<^sub>\<nat> zero = zero"
proof - 
  have "m \<cdot>\<^sub>\<nat> zero =  mult2\<circ>\<^sub>c\<langle>m, zero\<rangle>"
    by (simp add: mult_def)
  also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, mult1 \<circ>\<^sub>c zero\<rangle>"
    using assms calculation mult_def2 zero_type by auto
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, ((zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c one))\<^sup>\<sharp>) \<rangle>"
    using mult1_property triangle_commutes_def by auto
  also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f((zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c one))\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>m, id\<^sub>c one\<rangle>"
    by (smt assms cfunc_cross_prod_comp_cfunc_prod cfunc_type_def id_left_unit id_right_unit id_type mult1_property triangle_commutes_def)
  also have "... = zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c one) \<circ>\<^sub>c \<langle>m, id\<^sub>c one\<rangle>"
    using assms by (typecheck_cfuncs , simp add: cfunc_type_def comp_associative transpose_func_def)
  also have "... = zero"
    by (metis assms cfunc_type_def id_right_unit id_type right_cart_proj_cfunc_prod zero_type)
then show ?thesis using calculation by auto
qed

(*
lemma mult1_n: 
   assumes "n\<in>\<^sub>c  \<nat>\<^sub>c"
   shows "mult1\<circ>\<^sub>c n: one \<rightarrow> (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)"
  using assms mult1_type by auto
*)

lemma mult_respects_succ_right:
  assumes "m\<in>\<^sub>c  \<nat>\<^sub>c" "n\<in>\<^sub>c  \<nat>\<^sub>c"
  shows "m \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c n) = m +\<^sub>\<nat> (m \<cdot>\<^sub>\<nat> n)"
proof - 
  have fact: "\<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m, mult1\<circ>\<^sub>c n\<rangle>: one \<rightarrow> (\<nat>\<^sub>c \<times>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>))"
    using assms by typecheck_cfuncs
  have "m \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c n) = mult2\<circ>\<^sub>c\<langle>m, (successor \<circ>\<^sub>c n)\<rangle>"
    by (simp add: mult_def)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult1)\<circ>\<^sub>c \<langle>m, (successor \<circ>\<^sub>c n)\<rangle>"
    using assms by (typecheck_cfuncs, simp add: comp_associative2 mult2_def)
  also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, mult1 \<circ>\<^sub>c (successor \<circ>\<^sub>c n)\<rangle>"
    using assms apply typecheck_cfuncs
    using calculation mult_def2 by auto
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m,((add2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>)\<circ>\<^sub>c mult1 \<circ>\<^sub>c n  \<rangle>"
    using assms apply typecheck_cfuncs
    using comp_associative2 mult1_property square_commutes_def by auto
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m,((add2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>)\<circ>\<^sub>c mult1 \<circ>\<^sub>c n  \<rangle>"
      using assms by (typecheck_cfuncs, simp add: id_left_unit2)
 also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
(add2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>)
 \<circ>\<^sub>c \<langle>m,mult1 \<circ>\<^sub>c n  \<rangle>"
   using assms by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod comp_type id_type mult1_property square_commutes_def) 
  also have "... =(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f 
(add2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>)
 )\<circ>\<^sub>c \<langle>m,mult1 \<circ>\<^sub>c n  \<rangle>"
    using assms by (typecheck_cfuncs, simp add: comp_associative2)
  also have "... = (add2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),
(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)
       \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m, mult1\<circ>\<^sub>c n\<rangle>"
    using assms by (typecheck_cfuncs, simp add: id_left_unit2 transpose_func_def)
  also have "... = add2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>))
\<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m, mult1\<circ>\<^sub>c n\<rangle>,
(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m, mult1\<circ>\<^sub>c n\<rangle> \<rangle>
       "
    using assms by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2)
  also have "...  = add2  \<circ>\<^sub>c \<langle>m,
(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m, mult1\<circ>\<^sub>c n\<rangle> \<rangle>"
    using assms by (typecheck_cfuncs, simp add: id_left_unit2 left_cart_proj_cfunc_prod)
  also have "... = add2  \<circ>\<^sub>c \<langle>m,
   (eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  mult1)\<circ>\<^sub>c \<langle>m,n\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
  also have "... = add2  \<circ>\<^sub>c \<langle>m, mult2 \<circ>\<^sub>c \<langle>m,n\<rangle>\<rangle>"
    using assms apply typecheck_cfuncs
    using comp_associative2 mult2_def by auto
  also have "... =  m +\<^sub>\<nat> (m \<cdot>\<^sub>\<nat> n)"
    by (simp add: add_def mult_def)
  then show ?thesis using calculation by auto
qed

lemma s0_is_right_id:
  assumes "m\<in>\<^sub>c  \<nat>\<^sub>c" 
  shows "m \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = m"
  by (simp add: add_respects_zero_on_right assms mult_respects_succ_right mult_respects_zero_right zero_type)
(*Proof: m \<cdot>\<^sub>\<nat> S(0) = m +\<^sub>\<nat> (m \<cdot>\<^sub>\<nat> 0) = m +\<^sub>\<nat> 0 =m*)


lemma beta_N_succ_mEqs_Id1:
  assumes "m \<in>\<^sub>c  \<nat>\<^sub>c"
  shows "\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor \<circ>\<^sub>c m  = id\<^sub>c one"
  by (metis assms id_type succ_n_type terminal_func_comp terminal_func_unique)



lemma zero_beta_N_succ_type:
  "zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
  using successor_type terminal_func_comp zero_betaN_type by auto


lemma zero_beta_succ_mEqs0:
  assumes "m\<in>\<^sub>c  \<nat>\<^sub>c"
  shows "zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor \<circ>\<^sub>c m  = zero"
  using assms beta_N_succ_mEqs_Id1 id_right_unit2 zero_type by auto




lemma  zero_beta_succ_prod_mult1_type: 
  "\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,mult1\<rangle>: \<nat>\<^sub>c \<rightarrow> (\<nat>\<^sub>c \<times>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>))"
  by (simp add: cfunc_prod_type mult1_type zero_beta_N_succ_type)


lemma mult_prod_0bs_id_type: "mult2 \<circ>\<^sub>c  \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,id\<^sub>c \<nat>\<^sub>c\<rangle>: \<nat>\<^sub>c\<rightarrow> \<nat>\<^sub>c"
  by (meson cfunc_prod_type comp_type id_type mult2_type zero_beta_N_succ_type)



lemma mult_respects_zero_left:
  assumes "m\<in>\<^sub>c  \<nat>\<^sub>c" 
  shows "zero \<cdot>\<^sub>\<nat> m = zero"
proof - 
  have triangle1: "mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c zero = zero"
  proof - 
    have "mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c zero = 
          mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero , zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c zero\<rangle>"
      by (smt cfunc_prod_comp comp_associative2 id_type successor_type terminal_func_comp terminal_func_type zero_beta_N_succ_type zero_type)
    also have "... = mult2 \<circ>\<^sub>c \<langle>zero, zero \<circ>\<^sub>c id\<^sub>c one\<rangle>"
      using calculation cart_prod_extract_left id_right_unit2 zero_type by auto
    also have "... = zero"
      using id_right_unit2 mult_def mult_respects_zero_right zero_type by auto
   then show ?thesis using calculation by auto
  qed

  have triangle2: "mult2 \<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id\<^sub>c \<nat>\<^sub>c \<rangle>  \<circ>\<^sub>c zero = zero"
  proof -
    have f1: "id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero = zero"
          by (metis (no_types) cfunc_type_def id_left_unit zero_type)
    have "mult2 \<circ>\<^sub>c \<langle>(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero,zero\<rangle> = zero"
          by (metis (no_types) comp_type mult_def mult_respects_zero_right terminal_func_type zero_type)
    then show ?thesis
        using f1 cfunc_prod_comp cfunc_type_def comp_type id_type terminal_func_type zero_type by force
  qed

  have square1: "mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c successor
               = mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
  proof (rule one_separator[where X="\<nat>\<^sub>c", where Y="\<nat>\<^sub>c"])
    show f1: "mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
      by typecheck_cfuncs
    show f2: "mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
      by typecheck_cfuncs
  next
    fix m
    assume assms: "m \<in>\<^sub>c \<nat>\<^sub>c"
    have "mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c successor \<circ>\<^sub>c m =
        mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor \<circ>\<^sub>c m, zero \<circ>\<^sub>c  \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor \<circ>\<^sub>c m\<rangle>"
      using assms cart_prod_extract_left id_left_unit2 zero_beta_succ_mEqs0
      by (typecheck_cfuncs, auto)
    also have "... = mult2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c m, zero\<rangle>"
      using beta_N_succ_mEqs_Id1
      by (metis assms cfunc_type_def codomain_comp id_left_unit id_right_unit successor_type zero_type)
    also have "... = zero"
      using assms mult_def mult_respects_zero_right by (typecheck_cfuncs, auto)
    also have "... = mult2 \<circ>\<^sub>c \<langle>m, zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m \<rangle>"
      using assms by (typecheck_cfuncs, metis id_right_unit2 id_type mult_def mult_respects_zero_right one_unique_element)
    also have "... = mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m, zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m \<rangle>"
      using assms by (typecheck_cfuncs, simp add: id_left_unit2)
    also have "... =  mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c m"
      using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
    then show "(mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c successor) \<circ>\<^sub>c m =
         (mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c m"
      using calculation comp_associative2 assms by (typecheck_cfuncs, auto)
  qed

  have square2: "mult2 \<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c \<rangle> \<circ>\<^sub>c successor  = id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c
                 mult2 \<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c \<rangle>"
  proof - 
    have "mult2 \<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c \<rangle> \<circ>\<^sub>c successor  =
        mult2 \<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,successor\<rangle> "
      by (smt cfunc_prod_comp comp_associative2 id_left_unit2 id_type successor_type terminal_func_type zero_betaN_type zero_type)
    also have "... = (eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult1) \<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,successor\<rangle>"
      using assms apply typecheck_cfuncs
      using comp_associative2 mult2_def by auto
    also have "... = (eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,mult1 \<circ>\<^sub>c successor\<rangle>"
      using assms by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_type mult1_property successor_type zero_beta_N_succ_type) 
    also have "... = (eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,
        ((add2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c mult1 \<rangle>"
      using assms apply typecheck_cfuncs
      using id_left_unit2 mult1_property square_commutes_def by auto
    also have "... = (eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>) 
        \<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,mult1\<rangle>"
      using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
    also have "... = (add2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>) \<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,mult1\<rangle>"
      using assms by( typecheck_cfuncs, simp add: comp_associative2 transpose_func_def)
    also have "... = add2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>))\<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,mult1\<rangle>,(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,mult1\<rangle> \<rangle>"
      using assms by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2)
    also have "... = add2  \<circ>\<^sub>c \<langle> zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,mult1\<rangle> \<rangle>"
      using left_cart_proj_cfunc_prod mult1_property zero_beta_N_succ_type by auto
    also have "... = add2  \<circ>\<^sub>c \<langle> zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult1) \<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,id\<^sub>c \<nat>\<^sub>c\<rangle> \<rangle>"
      by (smt cfunc_cross_prod_comp_cfunc_prod cfunc_type_def id_left_unit id_right_unit id_type mult1_property zero_beta_N_succ_type)
    also have "... =  add2  \<circ>\<^sub>c \<langle> zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c mult2 \<circ>\<^sub>c  \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,id\<^sub>c \<nat>\<^sub>c\<rangle> , mult2 \<circ>\<^sub>c  \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,id\<^sub>c \<nat>\<^sub>c\<rangle>  \<rangle> "
      using assms by (typecheck_cfuncs, simp add: comp_associative2 mult2_def terminal_func_comp)
    also have "... =  add2  \<circ>\<^sub>c \<langle> zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,  id\<^sub>c \<nat>\<^sub>c  \<rangle> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c  \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,id\<^sub>c \<nat>\<^sub>c\<rangle>) "
      using assms by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 id_left_unit2)
    also have "... =id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c \<rangle>"
      using assms apply typecheck_cfuncs
      using \<open>add2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,id\<^sub>c \<nat>\<^sub>c\<rangle>,mult2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle> = add2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,id\<^sub>c \<nat>\<^sub>c\<rangle>\<close> add2_respects_zero_on_left id_left_unit2 mult_prod_0bs_id_type successor_type terminal_func_comp by auto
    then show ?thesis using calculation by auto
  qed

  have zero_commutes: "mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> = 
      mult2 \<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c \<rangle>"
  proof (rule natural_number_object_func_unique[where f="id\<^sub>c \<nat>\<^sub>c", where X="\<nat>\<^sub>c"])
    show  f1: "mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
      by typecheck_cfuncs
    show f2: "mult2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
      by typecheck_cfuncs
    show "id\<^sub>c \<nat>\<^sub>c : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
      by (meson id_type)
    show "(mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c zero =
    (mult2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero"
      using comp_associative2 triangle1 triangle2 by (typecheck_cfuncs, auto)
    show "(mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c successor =
        id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
      using comp_associative2 id_left_unit2 square1 by (typecheck_cfuncs, auto)
    show "(mult2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor =
        id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
      using comp_associative2 square2 by (typecheck_cfuncs, auto)
  qed

  have "zero \<cdot>\<^sub>\<nat> m = m \<cdot>\<^sub>\<nat> zero"
  proof -
    have "m \<cdot>\<^sub>\<nat> zero = mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c m"
      using assms by (typecheck_cfuncs, simp add: mult_apply1_left)
    also have "... = mult2 \<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c \<rangle> \<circ>\<^sub>c m"
      using assms by (typecheck_cfuncs, simp add: cfunc_type_def comp_associative zero_commutes)
    also have "... = zero \<cdot>\<^sub>\<nat> m"
      using assms by (typecheck_cfuncs, simp add: mult_apply1right)
    then show ?thesis
      using calculation by auto
  qed
  then show ?thesis
    by (simp add: assms mult_respects_zero_right)
qed

lemma s0b_type:
  "successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
  using comp_type successor_type zero_betaN_type by blast

lemma s0b_mult_type:
 "\<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , mult1\<rangle>: \<nat>\<^sub>c \<rightarrow> (\<nat>\<^sub>c \<times>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>))"
  by (simp add: cfunc_prod_type mult1_type s0b_type)

lemma s0b_id_type:
"\<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , id\<^sub>c \<nat>\<^sub>c\<rangle>: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c\<nat>\<^sub>c"
  by (simp add: cfunc_prod_type id_type s0b_type)

lemma mult_s0b_id_type:
"mult2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , id\<^sub>c \<nat>\<^sub>c\<rangle>: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
  using comp_type mult2_type s0b_id_type by blast



lemma s0_is_left_id:
  assumes "m\<in>\<^sub>c  \<nat>\<^sub>c"
  shows  "(successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> m   = m"
proof - 
  have triangle: "(mult2 \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> ,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero = zero"
  proof - 
     have "(mult2 \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> ,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero = 
       mult2 \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> ,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c zero"
       using comp_associative2 mult2_type s0b_id_type zero_type by auto
     also have "... =  mult2 \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c zero ,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero\<rangle>"
       by (smt cfunc_prod_comp comp_associative2 id_type s0b_type successor_type terminal_func_comp terminal_func_type zero_beta_N_succ_type zero_type)
     also have "... =  mult2 \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero , zero\<rangle>"
       by (metis id_left_unit2 id_right_unit2 id_type one_unique_element terminal_func_comp terminal_func_type zero_type)
     also have "... = zero"
       using mult_def mult_respects_zero_right succ_n_type zero_type by presburger
then show ?thesis using calculation by auto
qed


 have square: "(mult2 \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> ,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor =
          successor \<circ>\<^sub>c (mult2 \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> ,id\<^sub>c \<nat>\<^sub>c\<rangle>)"
  proof - 
   have "(mult2 \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> ,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor = 
          mult2 \<circ>\<^sub>c  (\<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> ,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c successor)"
     using assms by (typecheck_cfuncs, simp add: comp_associative2)
   also have "... =    mult2 \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor , id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor\<rangle>"
      using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
   also have "... =  mult2 \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , successor\<rangle>"
      using id_left_unit2 successor_type terminal_func_comp by force
   also have "... = (eval_func  \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult1) \<circ>\<^sub>c\<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , successor\<rangle>"
      using assms by (typecheck_cfuncs, simp add: comp_associative2 mult2_def)
   also have "... =  (eval_func  \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult1) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , id\<^sub>c \<nat>\<^sub>c\<rangle>"
     by (smt cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2 id_type s0b_type successor_type)
   also have "... =  (eval_func  \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult1 \<circ>\<^sub>csuccessor))  \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , id\<^sub>c \<nat>\<^sub>c\<rangle>"
      using assms apply typecheck_cfuncs
      using \<open>eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult1) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle> = eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult1) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<close> cfunc_cross_prod_comp_cfunc_prod id_right_unit2 by auto
   also have "... =  (eval_func  \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c mult1 )  \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , id\<^sub>c \<nat>\<^sub>c\<rangle>"
     using mult1_property square_commutes_def by auto
   also have "... =  ((eval_func  \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c mult1 ))  \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , id\<^sub>c \<nat>\<^sub>c\<rangle>"
     using  comp_associative2 by (typecheck_cfuncs, blast)
   also have "... =  ((eval_func  \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>)  \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult1 ))  \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , id\<^sub>c \<nat>\<^sub>c\<rangle>"
     using assms identity_distributes_across_composition by (typecheck_cfuncs, auto)
   also have "... =  ((eval_func  \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>))  \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult1 )  \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , id\<^sub>c \<nat>\<^sub>c\<rangle>"
     using  comp_associative2 by (typecheck_cfuncs, auto)
   also have "... =  (add2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult1) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , id\<^sub>c \<nat>\<^sub>c\<rangle>"
     using  transpose_func_def by (typecheck_cfuncs, auto)
   also have "... = (add2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>) \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , mult1\<rangle>"
     by (smt cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2 id_type mult1_property s0b_type)
   also have "... =  add2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle> \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , mult1\<rangle>"
     by (typecheck_cfuncs, simp add: comp_associative2)
   also have "... = add2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>))\<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , mult1\<rangle>,(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , mult1\<rangle>\<rangle>"
    using  cfunc_prod_comp eval_func_type left_cart_proj_type s0b_mult_type by fastforce 
   also have "... = add2  \<circ>\<^sub>c \<langle> successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> ,(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , mult1\<rangle>\<rangle>"
    using left_cart_proj_cfunc_prod mult1_property s0b_type by auto
   also have "... = add2  \<circ>\<^sub>c \<langle> successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> ,(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c  \<langle>id\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , mult1 \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<rangle>\<rangle>"
      using id_left_unit2 id_right_unit2 mult1_property s0b_type by auto
  also have "... =  add2  \<circ>\<^sub>c \<langle> successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> ,(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult1) \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>"
    by (smt cfunc_cross_prod_comp_cfunc_prod id_type mult1_type s0b_type)
  also have "... =  add2  \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , mult2 \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: comp_associative2 mult2_def)
  also have "... = successor \<circ>\<^sub>c (mult2 \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> ,id\<^sub>c \<nat>\<^sub>c\<rangle>)"
    using assms by (typecheck_cfuncs, simp add: add2_commutes_succ add2_respects_zero_on_left)
    then show ?thesis using calculation by auto
qed



have id3: "mult2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id\<^sub>c \<nat>\<^sub>c\<rangle> = id\<^sub>c \<nat>\<^sub>c"
proof(rule natural_number_object_func_unique[where f="successor", where X="\<nat>\<^sub>c"])
  show "mult2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by (simp add: mult_s0b_id_type)
  show "id\<^sub>c \<nat>\<^sub>c : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by (simp add: id_type)
  show "successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by (simp add: successor_type)
  show "(mult2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero =
    id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
    using id_left_unit2 triangle zero_type by auto
  show "(mult2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor =
    successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
    using square by blast
  show "id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor = successor \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c"
    using id_left_unit2 id_right_unit2 successor_type by auto
qed

  show ?thesis
    using assms cfunc_type_def comp_associative id3 id_left_unit2 mult2_type mult_apply1right s0b_id_type succ_n_type successor_type terminal_func_type zero_type by auto
qed




lemma mult_Left_Distributivity:
  assumes "a \<in>\<^sub>c  \<nat>\<^sub>c"  "b\<in>\<^sub>c  \<nat>\<^sub>c" "c\<in>\<^sub>c  \<nat>\<^sub>c"
  shows "(a +\<^sub>\<nat> b)\<cdot>\<^sub>\<nat> c = (a \<cdot>\<^sub>\<nat> c) +\<^sub>\<nat> (b \<cdot>\<^sub>\<nat> c)"
proof -

  have p1p1_type: "(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) :  ((\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c) \<rightarrow>\<nat>\<^sub>c "
    using comp_type left_cart_proj_type by blast 
  have p2p1_type:"(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) :  ((\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c) \<rightarrow>\<nat>\<^sub>c "
    using comp_type left_cart_proj_type right_cart_proj_type by blast 
  have p1p1p2_type: "\<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>: ((\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c) \<rightarrow>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)"
    by (simp add: cfunc_prod_type p1p1_type right_cart_proj_type)
  have p2p1p2_type: "\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>: ((\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c) \<rightarrow>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)"
    by (simp add: cfunc_prod_type p2p1_type right_cart_proj_type)
  have multp1p1p2_type: "mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>: ((\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c) \<rightarrow>\<nat>\<^sub>c"
    using comp_type mult2_type p1p1p2_type by blast
  have multp2p1p2_type: "mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>: ((\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c) \<rightarrow> \<nat>\<^sub>c"
    using comp_type mult2_type p2p1p2_type by blast


  have ab_type: "\<langle>a,b\<rangle>\<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
    by (simp add: assms(1) assms(2) cfunc_prod_type)
  have abz_type: "\<langle>\<langle>a,b\<rangle>,zero\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c"
    by (simp add: ab_type cfunc_prod_type zero_type)
  have ABC_type: "\<langle>\<langle>a,b\<rangle>,c\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c"
    by (simp add: ab_type assms(3) cfunc_prod_type)
  have succ_c_type: "successor \<circ>\<^sub>c c : one \<rightarrow> \<nat>\<^sub>c"
    using assms(3) succ_n_type by blast
  have ABsC_type: "\<langle>\<langle>a,b\<rangle>,successor \<circ>\<^sub>c c\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c"
    by (simp add: ab_type cfunc_prod_type succ_c_type)
  have fact0: "(add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c): ((\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c) \<rightarrow> (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)"
    by (simp add: add2_type cfunc_cross_prod_type id_type) 
  have fact1: "mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c): ((\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c) \<rightarrow>\<nat>\<^sub>c"
    using comp_type fact0 mult2_type by blast
  have fact1_sharp: "(mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>: \<nat>\<^sub>c \<rightarrow> (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)"
    by (simp add: fact1 transpose_func_type)
  have multAddId_c_type:  "(mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c c : one \<rightarrow>(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)"
    using assms(3) comp_type fact1_sharp by blast
  have zproj_type: "zero \<circ>\<^sub>c  (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) one): ((\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one) \<rightarrow> \<nat>\<^sub>c"
        using comp_type right_cart_proj_type zero_type by blast
  have zps_type: "(zero \<circ>\<^sub>c  (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) one))\<^sup>\<sharp>:  one \<rightarrow>  (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)"
    by (simp add: transpose_func_type zproj_type)
  have add_add_id_type: "add2 \<circ>\<^sub>c (add2\<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) : ((\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c) \<rightarrow>\<nat>\<^sub>c"
    using add2_type comp_type fact0 by blast
  have add_add_id_sharp_type: "(add2 \<circ>\<^sub>c (add2\<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>: \<nat>\<^sub>c \<rightarrow> (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)"
    by (simp add: add_add_id_type transpose_func_type)
  have piEval_type: "\<langle>(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)), eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<rangle>:
            (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>) \<rightarrow>  ((\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c)"
    by (simp add: cfunc_prod_type eval_func_type left_cart_proj_type)
  have addAddIdPiEval_type: "(add2 \<circ>\<^sub>c (add2\<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c 
\<langle>(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)), eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<rangle>) : (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>) \<rightarrow> \<nat>\<^sub>c"
    using add2_type comp_type fact0 piEval_type by blast
  have addAddIdPiEvalSharp_type: 
"(add2 \<circ>\<^sub>c (add2\<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c 
\<langle>(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)), eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>:
(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>) \<rightarrow>  (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)"
    using addAddIdPiEval_type transpose_func_type by force


  have addP0_type: "add2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>) : (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>) \<rightarrow> \<nat>\<^sub>c"
    using add2_type comp_type left_cart_proj_type by blast
  have evalu_type: "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)) :  (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)\<rightarrow>\<nat>\<^sub>c"
    using eval_func_type by auto


   have left_type: 
"mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
 (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>  :((\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c) \<rightarrow> \<nat>\<^sub>c"
     by (meson cfunc_prod_type comp_type left_cart_proj_type mult2_type right_cart_proj_type)

   have right_type:
"mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle> :((\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c) \<rightarrow> \<nat>\<^sub>c"
     by (meson cfunc_prod_type comp_type left_cart_proj_type mult2_type right_cart_proj_type)


   have long_type:  
"add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
 (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle> :((\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c) \<rightarrow>\<nat>\<^sub>c"
     by (meson add2_type cfunc_prod_type comp_type left_type right_type)

   have long_sharp_type: "
(add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
 (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup> "
     using long_type transpose_func_type by blast


   have long_sharp_c_type: "(add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
 (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c c : one \<rightarrow>\<nat>\<^sub>c \<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup> "
     using assms(3) comp_type long_sharp_type by blast




  have fact3c: "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c
    (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
    (mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c zero) = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c 
            (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(
            add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero)"
  proof(rule one_separator[ where X = "(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c one", where Y = "\<nat>\<^sub>c"])
    have "id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
    (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one \<rightarrow> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)"
      using cfunc_cross_prod_type comp_type fact1_sharp id_type zero_type by auto
   then show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c
    id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
    (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one \<rightarrow> \<nat>\<^sub>c"
     using comp_type evalu_type by blast
   have "id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
    (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)  \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,
              mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> 
          \<circ>\<^sub>c zero : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one \<rightarrow> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)"
     using cfunc_cross_prod_type comp_type id_type long_sharp_type zero_type by auto
   then show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
    (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)  \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,
              mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> 
          \<circ>\<^sub>c zero : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one \<rightarrow> \<nat>\<^sub>c"
     using comp_type evalu_type by blast
   show "\<And>x. x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one \<Longrightarrow> (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
          (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
          (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,
                  mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x"
   proof-
     fix x 
     assume x_type: "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one"
     
     obtain p q where x_def: "p\<in>\<^sub>c\<nat>\<^sub>c \<and> q\<in>\<^sub>c\<nat>\<^sub>c \<and> x = \<langle>\<langle>p,q\<rangle>, id one\<rangle>"
       using x_type by (typecheck_cfuncs, metis cart_prod_decomp one_unique_element)
     have pq_type: "\<langle>p,q\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
       by (simp add: cfunc_prod_type x_def)
     then have pq0_type: "\<langle>\<langle>p,q\<rangle>,zero\<rangle>  \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c"
       by (simp add: cfunc_prod_type  zero_type) 
       
     have "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
          (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, id one\<rangle> =
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
          (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,
                  mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, id one\<rangle>"
proof-
  have "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
          (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, id one\<rangle>   = 

        ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
          (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>  )\<circ>\<^sub>c  (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero)) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, id one\<rangle>" 
    by (typecheck_cfuncs, metis inv_transpose_func_def2 inv_transpose_of_composition)
  also have "... =  (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
          (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>  )\<circ>\<^sub>c  (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, id one\<rangle>" 
    by (typecheck_cfuncs, metis comp_associative2 x_def)
  also have "... =  (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
          (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>)\<circ>\<^sub>c   \<langle>id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>p,q\<rangle>,zero \<circ>\<^sub>c  id one\<rangle>"
    by (smt cfunc_cross_prod_comp_cfunc_prod id_type pq_type zero_type) 
  also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
          (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>)\<circ>\<^sub>c   \<langle>\<langle>p,q\<rangle>,zero\<rangle>"
    using id_left_unit2 id_right_unit2 pq_type zero_type by force
  also have "... = (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c   \<langle>\<langle>p,q\<rangle>,zero\<rangle>"
    by (typecheck_cfuncs, simp add: transpose_func_def)  
  also have "... = mult2 \<circ>\<^sub>c  \<langle>add2\<circ>\<^sub>c \<langle>p,q\<rangle>,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero\<rangle>"
    by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod comp_associative2 pq_type)
  also have "... = mult2 \<circ>\<^sub>c  \<langle>add2\<circ>\<^sub>c \<langle>p,q\<rangle>, zero\<rangle>"
    using id_left_unit2 zero_type by force
  also have "... = (add2\<circ>\<^sub>c \<langle>p,q\<rangle>) \<cdot>\<^sub>\<nat> zero"
    by (simp add: mult_def)
  also have "... = zero"
    using add2_type comp_type mult_respects_zero_right pq_type by blast
 also have "... = zero +\<^sub>\<nat> zero"
   by (simp add: add_respects_zero_on_left zero_type)
 also have "... = add2 \<circ>\<^sub>c\<langle>zero, zero\<rangle>"
   by (simp add: add_def)
 also have "... = add2 \<circ>\<^sub>c\<langle>p \<cdot>\<^sub>\<nat> zero,q \<cdot>\<^sub>\<nat> zero\<rangle>"
   by (simp add: mult_respects_zero_right x_def)
 also have "... = add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>p,  zero\<rangle>, mult2 \<circ>\<^sub>c \<langle>q,  zero\<rangle>\<rangle> "
   by (simp add: mult_def)
 also have "... = add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, zero\<rangle>, 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, zero\<rangle>\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, zero\<rangle>,(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, zero\<rangle>\<rangle>\<rangle> "
   using left_cart_proj_cfunc_prod pq_type right_cart_proj_cfunc_prod x_def zero_type by auto
also have "... =
          add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle> 
 \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, zero\<rangle>"
  by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 pq_type)
also have "... =
          add2 \<circ>\<^sub>c(\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle> 
 \<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c\<langle>p,q\<rangle>, zero\<circ>\<^sub>c id one\<rangle>)"
  using id_left_unit2 id_right_unit2 pq_type zero_type by auto
also have "... =
          add2 \<circ>\<^sub>c(\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle> \<circ>\<^sub>c
            (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero) 
             \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, id one\<rangle>)"
  by (smt cfunc_cross_prod_comp_cfunc_prod id_type pq_type zero_type)
also have "... =
          add2 \<circ>\<^sub>c(\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle> \<circ>\<^sub>c
            (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero) 
             \<circ>\<^sub>c x)"
  using x_def by force
also have "... =
          (add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle> \<circ>\<^sub>c
            (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero) )
             \<circ>\<^sub>c x"
  using cfunc_type_def comp_associative x_type by (typecheck_cfuncs, auto)
  also have "... =  ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c 
            (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(
            add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> )) \<circ>\<^sub>c
            (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero) 
             \<circ>\<^sub>c x"
    using cfunc_type_def comp_associative transpose_func_def x_type by (typecheck_cfuncs, auto)
  also have "... =  (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
          (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,
                  mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, id one\<rangle>"
    using  x_def  by (typecheck_cfuncs, smt comp_associative2 inv_transpose_func_def2 inv_transpose_of_composition)
  show "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, id one\<rangle> = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>, mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, id one\<rangle>"
    by (simp add: \<open>(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero) \<circ>\<^sub>c x = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,id\<^sub>c one\<rangle>\<close> calculation)
qed
  then show "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x =
 (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,
right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,
right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x"
    using   x_def by blast
qed
qed




  have main_result: "(mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> = 
(add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>"
  proof(rule natural_number_object_func_unique[where X ="\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>", where f = "(add2 \<circ>\<^sub>c (add2\<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c 
\<langle>(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)), eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>"])
    show "(mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
      by (simp add: fact1_sharp)
    show "(add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,
                   mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
      using long_sharp_type by fastforce
    show "(add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> : \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup> \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
      using addAddIdPiEvalSharp_type by blast
    show "(mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero =
    (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,
              mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero"
    proof(rule same_evals_equal[where Z = one,where X= "\<nat>\<^sub>c", where A = "\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"])
      show "(mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero \<in>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
        by (meson comp_type fact1_sharp zero_type)
      show "(add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,
                      mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> 
\<circ>\<^sub>c zero \<in>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
        by (meson comp_type long_sharp_type zero_type)
      show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero =
    eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
    (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,
          right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,
mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,
right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero"
        using fact3c by fastforce
    qed
    show "(mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor =
    (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)
       (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
    proof(rule same_evals_equal[where Z ="\<nat>\<^sub>c",where X= "\<nat>\<^sub>c", where A = "\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"])
      show "(mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
        by (meson comp_type fact1_sharp successor_type)
      show "(add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
        by (meson addAddIdPiEvalSharp_type comp_type fact1_sharp)
      show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor = eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
      proof(rule one_separator[where X ="(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c\<nat>\<^sub>c", where Y= "\<nat>\<^sub>c"])
        show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
          using \<open>(mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>\<close> flat_type inv_transpose_func_def2 by force
        show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c(mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
          using \<open>(add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>\<close> flat_type inv_transpose_func_def2 by force
        show "\<And>x. x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c(mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c x"
        proof - 
          fix x 
          assume x_type: "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c"
          obtain p q r where x_def: "p\<in>\<^sub>c \<nat>\<^sub>c\<and> q \<in>\<^sub>c \<nat>\<^sub>c \<and> r \<in>\<^sub>c \<nat>\<^sub>c \<and> x = \<langle>\<langle>p,q\<rangle>,r\<rangle>"
            using cart_prod_decomp x_type by blast
          have pq_type: "\<langle>p,q\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
            by (simp add: cfunc_prod_type x_def)
          have pqsr_type: "\<langle>\<langle>p,q\<rangle>,successor \<circ>\<^sub>c r\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c"
            by (simp add: cfunc_prod_type succ_n_type x_def)
          have sr_type: "successor \<circ>\<^sub>c r \<in>\<^sub>c \<nat>\<^sub>c"
            by (simp add: succ_n_type x_def)
          have pq22idr_type: "\<langle>\<langle>p,q\<rangle>, (mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c r\<rangle>  \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)"
            using cfunc_prod_type comp_type fact1_sharp x_def by auto

        (*Now we show the first function makes the square commute.*)
            have fact5: "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
          ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c 
                    (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c successor))
        \<circ>\<^sub>c   \<langle>\<langle>p,q\<rangle>,r\<rangle>"
              using x_def by blast

also have "... = ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c 
                    (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>) \<circ>\<^sub>c 
                    (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f     successor)
        )\<circ>\<^sub>c   \<langle>\<langle>p,q\<rangle>,r\<rangle>"
               using fact1_sharp identity_distributes_across_composition successor_type by auto
             also have "... = ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c 
                    (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)  
        )\<circ>\<^sub>c   \<langle>\<langle>p,q\<rangle>,successor \<circ>\<^sub>c r\<rangle>"
            using x_def  by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod comp_associative2 id_left_unit2)
          also have "... = mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c   \<langle>\<langle>p,q\<rangle>,successor \<circ>\<^sub>c r\<rangle>"
            using pqsr_type comp_associative2 fact0 fact1 mult2_type transpose_func_def by auto
          also have "... = mult2 \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>p,q\<rangle>, id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor \<circ>\<^sub>c r\<rangle>"
               using pq_type add2_type cfunc_cross_prod_comp_cfunc_prod id_type sr_type by fastforce
             also have "... =  (p +\<^sub>\<nat> q) \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c r)"
               using add_def id_left_unit2 mult_def sr_type by auto
             also have "... = (p +\<^sub>\<nat> q)  +\<^sub>\<nat>  ((p +\<^sub>\<nat> q) \<cdot>\<^sub>\<nat> r)"
               by (simp add: add_type mult_respects_succ_right x_def)
          also have "... =  add2 \<circ>\<^sub>c \<langle> add2 \<circ>\<^sub>c  \<langle>p,q\<rangle>,
                  mult2 \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c  \<langle>p,q\<rangle>, id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c r\<rangle>\<rangle>"
            using add_def id_left_unit2 mult_def x_def by auto
          also have "... = add2 \<circ>\<^sub>c \<langle> add2 \<circ>\<^sub>c  \<langle>p,q\<rangle>,  
            mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle>\<rangle>"
            by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod x_def)
          also have "... = add2 \<circ>\<^sub>c \<langle> add2 \<circ>\<^sub>c  \<langle>p,q\<rangle>,  
            (mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle>\<rangle>"
            by (typecheck_cfuncs, metis comp_associative2 x_def)
          also have "... = add2 \<circ>\<^sub>c \<langle> add2 \<circ>\<^sub>c  \<langle>p,q\<rangle>,
            ((id\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle>\<rangle>"
            by (typecheck_cfuncs, simp add: id_left_unit2)
          also have "... =  add2 \<circ>\<^sub>c \<langle> add2 \<circ>\<^sub>c  \<langle>p,q\<rangle>,  
        (id\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle>\<rangle>"
            by (typecheck_cfuncs, metis id_left_unit2 x_def)
          also have "... = add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f (id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c 
        \<langle>\<langle>p,q\<rangle>, (mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle>\<rangle>"
            by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod x_def)
          also have "... = add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f (id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c 
                  \<langle>\<langle>p,q\<rangle>, eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle>\<rangle>"
            by (typecheck_cfuncs, smt comp_associative2 flat_cancels_sharp inv_transpose_func_def2 x_def x_type)
          also have "... = add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f (id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c 
                  \<langle> \<langle>p,q\<rangle>,  eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>p,q\<rangle>, (mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c r\<rangle>\<rangle>"
            by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod x_def)
          also have "... = add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f (id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c 
                  \<langle> \<langle>p,q\<rangle>,  eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, (mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c r\<rangle>\<rangle>"
            using id_left_unit2 pq_type by (typecheck_cfuncs, auto)
          also have "... = add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f (id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c 
         \<langle>(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>))\<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, (mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c r\<rangle>,
         eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, (mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c r\<rangle>\<rangle>"
            by (typecheck_cfuncs, metis left_cart_proj_cfunc_prod x_def)          
          also have "... = add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f (id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c
        \<langle>(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)), eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<rangle> 
      \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, (mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c r\<rangle>"
            using cfunc_prod_comp pq22idr_type by (typecheck_cfuncs, force )
          also have "... = (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f (id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c
          \<langle>(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)), eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<rangle>) 
        \<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c  \<langle>p,q\<rangle>, (mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c r\<rangle>"
            using cfunc_type_def comp_associative id_left_unit2 pq22idr_type pq_type by (typecheck_cfuncs, auto)
          also have "... =  ( (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c 
                            (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f (id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c
                  \<langle>(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)), eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>))\<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c  \<langle>p,q\<rangle>, (mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c r\<rangle>"
            by (typecheck_cfuncs, simp add: transpose_func_def)        
          also have "... = ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c 
                    (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f (id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c
          \<langle>(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)), eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>)\<circ>\<^sub>c
        (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>f (mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)
        ) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle>"
            by (typecheck_cfuncs , smt cfunc_cross_prod_comp_cfunc_prod cfunc_type_def comp_associative pq_type x_def x_type)
          also have "... = ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c 
                    (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f (id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c
          \<langle>(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)), eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
          (mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle>"
            using addAddIdPiEvalSharp_type fact1_sharp identity_distributes_across_composition by auto
also have "... = ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c  (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c
          \<langle>(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)), eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
          (mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>) ) \<circ>\<^sub>c x"
                   using x_def by blast
     show "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c(mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c x"
       using calculation x_def by blast
   qed
 qed
qed

  show "(add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor = 
(add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>"
  proof(rule same_evals_equal[where Z = "\<nat>\<^sub>c", where X = "\<nat>\<^sub>c", where A = "\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c"])
    show type2: "(add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
      using comp_type long_sharp_type successor_type by blast
    show type3: "(add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
      using addAddIdPiEvalSharp_type comp_type long_sharp_type by blast
    show  " eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor = eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>"
    proof(rule one_separator[where X = "(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c", where Y = "\<nat>\<^sub>c"])
      show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
        using flat_type inv_transpose_func_def2 type2 by force
      show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
        using flat_type inv_transpose_func_def2 type3 by force
      show "\<And>x. x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c x"
      proof - 
        fix x 
        assume x_typ: "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c"
        obtain p q r where x_defn :"p \<in>\<^sub>c \<nat>\<^sub>c \<and> q \<in>\<^sub>c \<nat>\<^sub>c \<and> r \<in>\<^sub>c \<nat>\<^sub>c \<and> x = \<langle>\<langle>p,q\<rangle>,r\<rangle>"
          using x_typ cart_prod_decomp by blast
        have pq_type: "\<langle>p,q\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
          by (simp add: cfunc_prod_type x_defn)
        
        have "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)  \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>),  (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<rangle>)\<^sup>\<sharp>  \<circ>\<^sub>c (add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>))\<circ>\<^sub>c x =  ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c  (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)  \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>),  (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<rangle>)\<^sup>\<sharp>  \<circ>\<^sub>c (add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle>"
          using x_defn by blast
        also have "... =  ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c 
                  (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) 
       \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>), 
      (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<rangle>)\<^sup>\<sharp>  ) \<circ>\<^sub>c  
       (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
                   (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
                  (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
      (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle> "
          using addAddIdPiEvalSharp_type identity_distributes_across_composition long_sharp_type by auto
        also have "... = ((add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) 
       \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>), 
      (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<rangle>) \<circ>\<^sub>c
      (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
                   (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
                  (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
      (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle> "
          using assms by (typecheck_cfuncs, simp add: comp_associative2 transpose_func_def)    
          also have "... =  (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)
       \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>), 
      (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<rangle>) \<circ>\<^sub>c
      (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
                   (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
                  (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
      (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle> "
            by (typecheck_cfuncs , smt comp_associative2 x_defn x_typ)
           also have "... = (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) 
       \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>), 
      (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<rangle>)  \<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>p,q\<rangle>,
      (add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
                   (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
                  (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
      (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
      r\<rangle> "
          using pq_type x_defn cfunc_cross_prod_comp_cfunc_prod id_type long_sharp_type by fastforce
       
        also have "... =  (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)
       \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>), 
      (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<rangle>)  \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,
      (add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
                   (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
                  (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
      (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
      r\<rangle> "
          using pq_type id_left_unit2 by auto
        also have "... =  add2 \<circ>\<^sub>c (
      (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) 
       \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>), 
      (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<rangle> ) \<circ>\<^sub>c \<langle>
      \<langle>p,q\<rangle>,
      (add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
                   (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
                  (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
      (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
      r\<rangle> "
          using x_typ x_defn pq_type  by (typecheck_cfuncs, smt comp_associative2 x_defn)
 also have "... =
       add2 \<circ>\<^sub>c \<langle>
      add2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>),  id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))  \<rangle>  
       \<circ>\<^sub>c \<langle>
      \<langle>p,q\<rangle>,
      (add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
                   (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
                  (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
      (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
      r\<rangle> "
          by (smt add2_type cfunc_cross_prod_comp_cfunc_prod eval_func_type id_type left_cart_proj_type)
        also have "... = 
       add2 \<circ>\<^sub>c \<langle>
      add2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>),  (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))  \<rangle>  
       \<circ>\<^sub>c \<langle>
      \<langle>p,q\<rangle>,
      (add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
                   (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
                  (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
      (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
      r\<rangle> "
          by (metis eval_func_type id_left_unit2)
        also have "... =  
      add2 \<circ>\<^sub>c \<langle>
      add2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)
       \<circ>\<^sub>c \<langle>
      \<langle>p,q\<rangle>,
      (add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
                   (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
                  (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
      (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
      r\<rangle>
      ,  (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)) 
       \<circ>\<^sub>c \<langle>
      \<langle>p,q\<rangle>,
      (add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
                   (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
                  (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
      (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
      r\<rangle>
       \<rangle>"
          using pq_type by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 x_defn)
          
        also have "... =add2 \<circ>\<^sub>c \<langle>
      add2 \<circ>\<^sub>c \<langle>p,q\<rangle>
      ,  (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)) 
       \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,
      (add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
                   (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c 
      \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
                  (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
      (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
      r\<rangle>
       \<rangle>" 
 by (typecheck_cfuncs, metis left_cart_proj_cfunc_prod x_defn)

    also have "... = add2 \<circ>\<^sub>c \<langle>
      add2 \<circ>\<^sub>c \<langle>p,q\<rangle>
      ,  (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)) 
       \<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>p,q\<rangle>,
      (add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
                   (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c 
      \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
                  (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
      (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
      r\<rangle>
       \<rangle>"
          using pq_type id_left_unit2 by auto
        also have "... = 
      add2 \<circ>\<^sub>c \<langle>
      add2 \<circ>\<^sub>c \<langle>p,q\<rangle>
      ,  (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)) 
       \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
                   (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c 
      \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
                  (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
      (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle> \<langle>p,q\<rangle>,r\<rangle> \<rangle>"
          using pq_type x_defn cfunc_cross_prod_comp_cfunc_prod id_type long_sharp_type by fastforce
        also have "... = 
      add2 \<circ>\<^sub>c \<langle>
      add2 \<circ>\<^sub>c \<langle>p,q\<rangle>
      ,  (add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
                   (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c 
      \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
                  (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
      (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>) \<circ>\<^sub>c \<langle> \<langle>p,q\<rangle>,r\<rangle> \<rangle>"
          by (typecheck_cfuncs , smt comp_associative2 transpose_func_def x_defn x_typ)
        
          also have "... = add2 \<circ>\<^sub>c \<langle>
      add2 \<circ>\<^sub>c \<langle>p,q\<rangle>
      ,  add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
                   (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>
      
      , mult2 \<circ>\<^sub>c
      \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
                  (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
      (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle> \<circ>\<^sub>c \<langle> \<langle>p,q\<rangle>,r\<rangle> \<rangle>"
            by (typecheck_cfuncs , smt comp_associative2 x_defn)

            also have "... = add2 \<circ>\<^sub>c \<langle>
      add2 \<circ>\<^sub>c \<langle>p,q\<rangle>
      ,  add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
                   (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c \<langle> \<langle>p,q\<rangle>,r\<rangle>
      
      , mult2 \<circ>\<^sub>c
      \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
                  (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
      (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>   \<circ>\<^sub>c \<langle> \<langle>p,q\<rangle>,r\<rangle> \<rangle>  \<rangle>"
            using  x_defn x_typ by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2)
      
        also have "... =add2 \<circ>\<^sub>c \<langle>
      add2 \<circ>\<^sub>c \<langle>p,q\<rangle>
      ,  add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
                   (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c \<langle> \<langle>p,q\<rangle>,r\<rangle>
      
      , mult2 \<circ>\<^sub>c
      \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
                  (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle> \<langle>p,q\<rangle>,r\<rangle> ,
      (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle> \<langle>p,q\<rangle>,r\<rangle>\<rangle>   \<rangle>  \<rangle>"
          by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 x_defn x_typ)


        also have "... =
      add2 \<circ>\<^sub>c \<langle>
      add2 \<circ>\<^sub>c \<langle>p,q\<rangle>
      ,  add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle> \<langle>p,q\<rangle>,r\<rangle>, 
                   (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle> \<langle>p,q\<rangle>,r\<rangle>\<rangle>
      
      , mult2 \<circ>\<^sub>c
      \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
                  \<langle>p,q\<rangle>,
      r\<rangle>   \<rangle>  \<rangle>"
          using pq_type  x_defn by (typecheck_cfuncs, smt cart_prod_eq comp_associative2 left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
        also have "... = 
      add2 \<circ>\<^sub>c \<langle>
      add2 \<circ>\<^sub>c \<langle>p,q\<rangle>
      ,  add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c 
      \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c   \<langle>p,q\<rangle>, r\<rangle>,
       mult2 \<circ>\<^sub>c\<langle>q,r\<rangle>\<rangle>\<rangle>"
          using pq_type x_defn left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod by auto
        also have "... =
      add2 \<circ>\<^sub>c \<langle>
      add2 \<circ>\<^sub>c \<langle>p,q\<rangle>
      ,  add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>p, r\<rangle>, mult2 \<circ>\<^sub>c\<langle>q,r\<rangle>\<rangle>\<rangle>"
          using x_defn left_cart_proj_cfunc_prod by auto
        also have "... = (p +\<^sub>\<nat> q) +\<^sub>\<nat> (p \<cdot>\<^sub>\<nat> r +\<^sub>\<nat> q \<cdot>\<^sub>\<nat> r)"
          by (simp add: add_def mult_def)
        also have "... = p +\<^sub>\<nat> (q +\<^sub>\<nat> (p \<cdot>\<^sub>\<nat> r +\<^sub>\<nat> q \<cdot>\<^sub>\<nat> r))"
          using x_defn by (typecheck_cfuncs, metis add_associates mult_closure)
        also have "... = p +\<^sub>\<nat> ((q +\<^sub>\<nat> p \<cdot>\<^sub>\<nat> r) +\<^sub>\<nat> q \<cdot>\<^sub>\<nat> r)"
          using x_defn by (typecheck_cfuncs, simp add: add_associates mult_closure)
        also have "... = p +\<^sub>\<nat> ((p \<cdot>\<^sub>\<nat> r  +\<^sub>\<nat> q) +\<^sub>\<nat> q \<cdot>\<^sub>\<nat> r)"
         using x_defn by (typecheck_cfuncs, simp add: add_commutes mult_closure)
        also have "... = p +\<^sub>\<nat> (p \<cdot>\<^sub>\<nat> r  +\<^sub>\<nat> (q +\<^sub>\<nat> q \<cdot>\<^sub>\<nat> r))"
          using x_defn by (typecheck_cfuncs, simp add: add_associates mult_closure)
        also have "... = (p +\<^sub>\<nat> p \<cdot>\<^sub>\<nat> r)  +\<^sub>\<nat> (q +\<^sub>\<nat> q \<cdot>\<^sub>\<nat> r)"
          using x_defn by (typecheck_cfuncs, meson add_associates mult_closure)
        also have "... = (p \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c r)) +\<^sub>\<nat> (q \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c r))"
          by (simp add: x_defn mult_respects_succ_right)
        also have "... = add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>p , (successor \<circ>\<^sub>c r) \<rangle>  , mult2 \<circ>\<^sub>c \<langle>q,successor \<circ>\<^sub>c r  \<rangle> \<rangle> "
          by (simp add: add_def mult_def)
        also have "... = add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c  \<langle>p,q\<rangle> , 
            (successor \<circ>\<^sub>c r) \<rangle>  , mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
             \<langle>p,q\<rangle> , successor \<circ>\<^sub>c r \<rangle>\<rangle> "
          using left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod x_defn by force
        also have "... = add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,successor \<circ>\<^sub>c r\<rangle> ,
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,successor \<circ>\<^sub>c r\<rangle> \<rangle>  , mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,successor \<circ>\<^sub>c r\<rangle> ,(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,successor \<circ>\<^sub>c r\<rangle> \<rangle>   \<rangle> "
          using left_cart_proj_cfunc_prod pq_type right_cart_proj_cfunc_prod succ_n_type x_defn by auto
        also have "... = add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,successor \<circ>\<^sub>c r\<rangle>  , mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,successor \<circ>\<^sub>c r\<rangle>   \<rangle> "
          using pq_type x_defn  by (typecheck_cfuncs , smt cfunc_prod_comp comp_associative2 x_defn)

    also have "... = add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle> \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,successor \<circ>\<^sub>c r\<rangle>"
          using pq_type x_defn by (typecheck_cfuncs , smt cfunc_prod_comp comp_associative2 x_defn)

  also have  "... = (
            add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,successor \<circ>\<^sub>c r\<rangle>"
            using pq_type comp_associative2 x_defn by (typecheck_cfuncs, blast)

  also have "... = ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c
            (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(
            add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> )) 
\<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,successor \<circ>\<^sub>c r\<rangle>"
           using  transpose_func_def by (typecheck_cfuncs, presburger)
  also have "... = ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c
            (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(
            add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> )) 
\<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>p,q\<rangle>,successor \<circ>\<^sub>c r\<rangle>"
    using id_left_unit2 pq_type by presburger
  also have "... = ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c
            (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(
            add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> )) 
\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor) \<circ>\<^sub>c  \<langle> \<langle>p,q\<rangle>, r\<rangle>"
    using cfunc_cross_prod_comp_cfunc_prod id_type pq_type successor_type x_defn by fastforce
  also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c  \<langle> \<langle>p,q\<rangle>, r\<rangle>"
    by (typecheck_cfuncs, smt comp_associative2 inv_transpose_func_def2 inv_transpose_of_composition x_defn x_typ)
  also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c  x"
    using x_defn by blast
  show "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c x"
    using calculation x_defn by auto
qed
qed
qed
qed

  then have flat_main_result: "mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) = 
add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>"
    by (metis fact1 flat_cancels_sharp long_type)

  have main_equation: "(a +\<^sub>\<nat> b)\<cdot>\<^sub>\<nat> c = mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
    using assms by (typecheck_cfuncs, smt ab_type add2_type add_def cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_type mult_def)
  also have "... = add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle> \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_type_def comp_associative flat_main_result)
  also have "... =  (a \<cdot>\<^sub>\<nat> c) +\<^sub>\<nat> (b \<cdot>\<^sub>\<nat> c)"
    using assms by (typecheck_cfuncs, smt add_def cfunc_prod_comp comp_associative2 left_cart_proj_cfunc_prod mult_def right_cart_proj_cfunc_prod)

  then show ?thesis
    by (simp add: calculation) 
qed





lemma mult_commutative:
  assumes "a \<in>\<^sub>c  \<nat>\<^sub>c"  "b\<in>\<^sub>c  \<nat>\<^sub>c" 
  shows "a \<cdot>\<^sub>\<nat> b = b \<cdot>\<^sub>\<nat> a"

proof - 
 
    
  have p1p0_type:  "\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>: (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<rightarrow>  (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)"
    by (simp add: cfunc_prod_type left_cart_proj_type right_cart_proj_type)
  have multp1p0_tye: "mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>: (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<rightarrow> \<nat>\<^sub>c"
    using comp_type mult2_type p1p0_type by blast 
  have multp1p0sharp_type: "(mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
    by (simp add: multp1p0_tye transpose_func_type)
  have  multp1p0sharp0_type: "(mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>\<circ>\<^sub>c zero: one \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
    using comp_type multp1p0sharp_type zero_type by blast
  have  pi0eval_type: "\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>), eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>: \<nat>\<^sub>c\<times>\<^sub>c(\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<rightarrow> (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)"
    by (simp add: cfunc_prod_type eval_func_type left_cart_proj_type)
  have addpi0eval_type: "add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>), eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>: \<nat>\<^sub>c\<times>\<^sub>c(\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<rightarrow> \<nat>\<^sub>c"
    using add2_type comp_type pi0eval_type by blast
  have addpi0evalsharp_type:  "(add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>), eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>: (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<rightarrow> (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)"
    by (simp add: addpi0eval_type transpose_func_type)




  have main_result: "(mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> = (mult2)\<^sup>\<sharp>"
  proof(rule natural_number_object_func_unique[where X = "\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>", where f = "(add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>), eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>"])
    show type1:"(mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
      by (simp add: multp1p0sharp_type)
    show type2: "mult2\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
      by (simp add: mult2_type transpose_func_type)
    show type3: "(add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> : \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
      using addpi0evalsharp_type by blast
    show triangle: "(mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero = mult2\<^sup>\<sharp> \<circ>\<^sub>c zero"
    proof(rule same_evals_equal[where Z = "one", where X = "\<nat>\<^sub>c", where A = "\<nat>\<^sub>c"])
      show type4: "(mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero : one \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
        by (simp add: multp1p0sharp0_type)
      show type5: "mult2\<^sup>\<sharp> \<circ>\<^sub>c zero \<in>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
        using comp_type type2 zero_type by blast
      show equation1: "eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c
    id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
    (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero =
    eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2\<^sup>\<sharp> \<circ>\<^sub>c zero"
      proof(rule one_separator[where X = "\<nat>\<^sub>c\<times>\<^sub>c one", where Y = "\<nat>\<^sub>c"])
        show type6: "eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c
    id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
    (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
    zero : \<nat>\<^sub>c \<times>\<^sub>c one \<rightarrow> \<nat>\<^sub>c"
          using flat_type inv_transpose_func_def2 multp1p0sharp0_type by auto
        show type7: "eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2\<^sup>\<sharp> \<circ>\<^sub>c zero : \<nat>\<^sub>c \<times>\<^sub>c one \<rightarrow> \<nat>\<^sub>c"
          using flat_type inv_transpose_func_def2 type5 by auto
        show "\<And>x. x \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c one \<Longrightarrow>
         (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c
          id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
          (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
          zero) \<circ>\<^sub>c
         x =
         (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x"
        proof - 
          fix x 
          assume x_type: "x \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c one"
          obtain p where x_def: "p \<in>\<^sub>c \<nat>\<^sub>c \<and> x = \<langle>p, id one\<rangle>"
            by (metis beta_N_succ_mEqs_Id1 cart_prod_decomp comp_type successor_type terminal_func_comp terminal_func_unique x_type)
        
          have "(eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c
          id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
          zero) \<circ>\<^sub>c x =  (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c
          id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
          zero) \<circ>\<^sub>c\<langle>p, id one\<rangle>"
            using x_def by blast
          also have "... =  eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c
       \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>\<circ>\<^sub>c zero)\<circ>\<^sub>c \<langle>p,id\<^sub>c one\<rangle>"
            by (typecheck_cfuncs, metis comp_associative2 x_def)
          also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c
       \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero)\<circ>\<^sub>c \<langle>p,id\<^sub>c one\<rangle>"
            by (smt cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2 id_type multp1p0sharp0_type multp1p0sharp_type x_def zero_type)
          also have "... = (mult2 \<circ>\<^sub>c
       \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero)\<circ>\<^sub>c \<langle>p,id\<^sub>c one\<rangle>"
            using x_def by (typecheck_cfuncs, metis cfunc_type_def comp_associative transpose_func_def)
          also have "... = (mult2 \<circ>\<^sub>c
       \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c\<circ>\<^sub>c  p, zero \<circ>\<^sub>c id\<^sub>c one\<rangle>"
            by (smt x_def cfunc_cross_prod_comp_cfunc_prod id_type zero_type)
          also have "... =  mult2 \<circ>\<^sub>c
       \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>p, zero\<rangle>"
            by (typecheck_cfuncs, metis (full_types) comp_associative2 id_left_unit2 id_right_unit2 x_def)
          also have "... =  mult2 \<circ>\<^sub>c
       \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>p, zero\<rangle> ,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>p, zero\<rangle> \<rangle>"
            by (typecheck_cfuncs , metis cfunc_prod_comp x_def)
           also have "... =  mult2 \<circ>\<^sub>c \<langle>zero , p\<rangle>"
            using x_def left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod zero_type by auto
          also have "... = zero"
            using x_def mult_def mult_respects_zero_left by (typecheck_cfuncs, force)
          also have "... = p \<cdot>\<^sub>\<nat> zero"
            by (simp add: mult_respects_zero_right x_def)
          also have "... = mult2 \<circ>\<^sub>c  \<langle>p,zero\<rangle>"
            by (simp add: mult_def)
          also have "... = mult2 \<circ>\<^sub>c  \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c p,zero \<circ>\<^sub>cid one\<rangle>"
            using beta_N_succ_mEqs_Id1 id_left_unit2 x_def zero_beta_succ_mEqs0 by auto
          also have "... = (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2\<^sup>\<sharp>)  \<circ>\<^sub>c  \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c p,zero \<circ>\<^sub>cid one\<rangle>"
            using mult2_type transpose_func_def by auto
          also have "... = (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2\<^sup>\<sharp>)  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero) \<circ>\<^sub>c \<langle>p, id one\<rangle>"
            using cfunc_cross_prod_comp_cfunc_prod x_def by (typecheck_cfuncs, auto)
          also have "... = (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c \<langle>p, id one\<rangle>"
            by (typecheck_cfuncs, smt cfunc_type_def comp_associative inv_transpose_func_def2 inv_transpose_of_composition x_def)
          also have "... = (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x"
              using x_def by auto     
          show "(eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x = (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x"
            using calculation x_def by auto
        qed
      qed
    qed
    show square1: "(mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
    successor = (add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
    (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>"
    proof(rule same_evals_equal[where Z = "\<nat>\<^sub>c", where X = "\<nat>\<^sub>c", where A = "\<nat>\<^sub>c"])
      show type8: "(mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
        using comp_type successor_type type1 by blast
      show type9: "(add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
        using comp_type type1 type3 by blast
      show eqn2: "eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c
    id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
    (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
    successor =
    eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c
    id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
    (add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
    (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>"
      proof(rule one_separator[where X ="\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c ", where Y = "\<nat>\<^sub>c"])
        show type10: "eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor : \<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c  \<rightarrow> \<nat>\<^sub>c"
          using flat_type inv_transpose_func_def2 type8 by force
        show type11: "eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
          using flat_type inv_transpose_func_def2 type9 by auto
        show "\<And>x. x \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
         (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c x"
        proof - 
          fix x 
          assume x_type: "x \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
          obtain p q where x_defn: "p \<in>\<^sub>c \<nat>\<^sub>c \<and> q \<in>\<^sub>c \<nat>\<^sub>c \<and> x = \<langle>p,q\<rangle>"
            using cart_prod_decomp x_type by blast
          have psq_type: "\<langle>p,successor \<circ>\<^sub>cq\<rangle> \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
            by (simp add: cfunc_prod_type succ_n_type x_defn)

          have "(eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
                ((eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor)) \<circ>\<^sub>c x"
            by (typecheck_cfuncs , simp add: sharp_comp transpose_func_def)
          also have "... =  (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c \<langle>p,q\<rangle>"
            by (typecheck_cfuncs , metis comp_associative2 x_defn)
          also have "... =  (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>)  \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c p,successor \<circ>\<^sub>cq\<rangle>" 
            using cfunc_cross_prod_comp_cfunc_prod x_defn by (typecheck_cfuncs, auto)
          also have "... =  (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>)  \<circ>\<^sub>c \<langle>p,successor \<circ>\<^sub>cq\<rangle>"
            using id_left_unit2 x_defn by force
          also have "... =  (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)  \<circ>\<^sub>c \<langle>p,successor \<circ>\<^sub>cq\<rangle>"
            by (typecheck_cfuncs, simp add: transpose_func_def)
          also have "... =  mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>  \<circ>\<^sub>c \<langle>p,successor \<circ>\<^sub>cq\<rangle>"
            using comp_associative2 psq_type by (typecheck_cfuncs, auto)
          also have "... =  mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>p,successor \<circ>\<^sub>cq\<rangle> ,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>p,successor \<circ>\<^sub>cq\<rangle>\<rangle>"
            using cfunc_prod_comp psq_type by (typecheck_cfuncs, auto)
          also have "... =  mult2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c q ,p\<rangle>"
            using left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod succ_n_type x_defn by auto
          also have "... = (successor \<circ>\<^sub>c q) \<cdot>\<^sub>\<nat> p"
            by (simp add: mult_def)
          also have "... = p +\<^sub>\<nat> (q \<cdot>\<^sub>\<nat> p)"
            by (metis mult_Left_Distributivity mult_respects_succ_right s0_is_left_id succ_n_type x_defn zero_type)
          also have "... =  add2 \<circ>\<^sub>c\<langle>p,  mult2 \<circ>\<^sub>c \<langle>q,p\<rangle>\<rangle>"
            by (simp add: add_def mult_def)
          also have "... =  add2 \<circ>\<^sub>c\<langle>p,  mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>p,q\<rangle>,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>p,q\<rangle>\<rangle>\<rangle>"
            by (typecheck_cfuncs, metis left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod x_defn)
           also have "... =  add2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>p,q\<rangle>, 
              mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>p,q\<rangle> \<rangle>  "
             by (typecheck_cfuncs , smt cfunc_prod_comp id_left_unit2 left_cart_proj_cfunc_prod x_defn x_type)
           also have "... = add2 \<circ>\<^sub>c
 \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c , 
    mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>  \<circ>\<^sub>c \<langle>p,q\<rangle>"
             by (typecheck_cfuncs , smt cfunc_prod_comp comp_associative2 x_defn x_type)
          also have "... = add2 \<circ>\<^sub>c
 \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c , 
    mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>  \<circ>\<^sub>c x"
            using x_defn by blast
          also have "... = (add2 \<circ>\<^sub>c
 \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c , 
    mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)  \<circ>\<^sub>c x"  
            using comp_associative2 x_type by (typecheck_cfuncs, blast)
          also have "... = (add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>)\<rangle>) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_cross_prod transpose_func_def)
          also have "... = (add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>)) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, simp add: cfunc_prod_comp)
          also have "... = add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c x"
            using comp_associative2 x_type by (typecheck_cfuncs, auto)
          also have "... = (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>)) \<circ>\<^sub>c x"
            using \<open>(add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c x = add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c x\<close>
            cfunc_type_def comp_associative transpose_func_def by (typecheck_cfuncs, auto)
          also have "... = (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c x"
            by (typecheck_cfuncs,  simp add: identity_distributes_across_composition)
          then show "(eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c x"
            by (simp add: calculation)
        qed
      qed
    qed
    show "mult2\<^sup>\<sharp> \<circ>\<^sub>c successor =
    (add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c mult2\<^sup>\<sharp>"
    proof(rule same_evals_equal[where Z = "\<nat>\<^sub>c", where X = "\<nat>\<^sub>c", where A = "\<nat>\<^sub>c"])
      show type12: "mult2\<^sup>\<sharp> \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
        using comp_type successor_type type2 by blast
      show type13: "(add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c mult2\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
        using comp_type type2 type3 by blast
      show "eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2\<^sup>\<sharp> \<circ>\<^sub>c successor =
    eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c
    id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f
    (add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c mult2\<^sup>\<sharp>"
      proof(rule one_separator[where X ="\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c ", where Y = "\<nat>\<^sub>c"])
        show type14: "eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2\<^sup>\<sharp> \<circ>\<^sub>c successor : \<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c  \<rightarrow> \<nat>\<^sub>c"
          using flat_type inv_transpose_func_def2 type12 by auto
        show type15: "eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c mult2\<^sup>\<sharp> : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
          using flat_type inv_transpose_func_def2 type13 by auto
        show eqn4: "\<And>x. x \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
         (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c mult2\<^sup>\<sharp>) \<circ>\<^sub>c x"

        proof - 
          fix x 
          assume x_type: "x \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
          obtain p q where x_def: "p \<in>\<^sub>c \<nat>\<^sub>c \<and> q \<in>\<^sub>c \<nat>\<^sub>c \<and> x = \<langle>p,q\<rangle>"
            using cart_prod_decomp x_type by blast
          have p2q_type: "\<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c p, mult2\<^sup>\<sharp> \<circ>\<^sub>c  q\<rangle> \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)"
            using x_def by (typecheck_cfuncs, blast)
          have "(eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
                ((eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor)) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, metis inv_transpose_func_def2 inv_transpose_of_composition)
          also have "... = (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c x"
            using comp_associative2 x_type by (typecheck_cfuncs, auto)
          also have "... = mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c x"
            by (typecheck_cfuncs , simp add: transpose_func_def)
          also have "... = mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c \<langle>p,q\<rangle>"
            by (simp add: x_def)
          also have "... = mult2 \<circ>\<^sub>c  \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c p,successor \<circ>\<^sub>c q\<rangle>"
            using cfunc_cross_prod_comp_cfunc_prod x_def by (typecheck_cfuncs, auto)
          also have "... = mult2 \<circ>\<^sub>c  \<langle>p,successor \<circ>\<^sub>c q\<rangle>"
            using id_left_unit2 x_def by auto
          also have "... = p \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c q)"
            by (simp add: mult_def)
          also have "... = p +\<^sub>\<nat> (p \<cdot>\<^sub>\<nat>  q)"
            by (simp add: mult_respects_succ_right x_def)
          also have "... = add2 \<circ>\<^sub>c \<langle>p ,(p\<cdot>\<^sub>\<nat>q)\<rangle>"
            by (simp add: add_def)
          also have "... = add2 \<circ>\<^sub>c \<langle>p , mult2 \<circ>\<^sub>c\<langle>p,q\<rangle>\<rangle>"
            by (simp add: mult_def)
          also have "... = add2 \<circ>\<^sub>c \<langle>p ,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2\<^sup>\<sharp>)  \<circ>\<^sub>c \<langle>p,   q\<rangle>\<rangle>"
            by (typecheck_cfuncs , smt comp_associative2 transpose_func_def x_def)
          also have "... = add2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c p ,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2\<^sup>\<sharp>)  \<circ>\<^sub>c \<langle>p,   q\<rangle>\<rangle>"
            using id_left_unit2 x_def by force
          also have "... = add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c p, mult2\<^sup>\<sharp> \<circ>\<^sub>c  q\<rangle> ,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c p, mult2\<^sup>\<sharp> \<circ>\<^sub>c  q\<rangle>\<rangle>"
            by (typecheck_cfuncs , smt cfunc_cross_prod_comp_cfunc_prod left_cart_proj_cfunc_prod x_def)
          also have "... = add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>  \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c p, mult2\<^sup>\<sharp> \<circ>\<^sub>c  q\<rangle>"
            using cfunc_prod_comp p2q_type by (typecheck_cfuncs, auto)           
          also have "... = add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>fmult2\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>p,q\<rangle>"
            using cfunc_cross_prod_comp_cfunc_prod x_def by (typecheck_cfuncs, auto)
          also have "... = add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>fmult2\<^sup>\<sharp>) \<circ>\<^sub>c x"
            using x_def by auto
          also have "... = (add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c ((id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>fmult2\<^sup>\<sharp>) \<circ>\<^sub>c x)"
            by (typecheck_cfuncs, metis cfunc_type_def comp_associative x_type)
          also have "... = (add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>fmult2\<^sup>\<sharp>)) \<circ>\<^sub>c x"
            using comp_associative2 x_type by (typecheck_cfuncs, auto)
          also have "... = ((add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c ((id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>fmult2\<^sup>\<sharp>)) \<circ>\<^sub>c x)"
            by (typecheck_cfuncs , simp add: \<open>(add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2\<^sup>\<sharp>) \<circ>\<^sub>c x = (add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2\<^sup>\<sharp>) \<circ>\<^sub>c x\<close>)
          also have "... =   ((eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c ((id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>fmult2\<^sup>\<sharp>)) \<circ>\<^sub>c x)"
            by (typecheck_cfuncs , simp add: transpose_func_def)
          also have "... = (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c mult2\<^sup>\<sharp>) \<circ>\<^sub>c x"        
            by (typecheck_cfuncs, metis calculation mult1_comp_succ_eq mult1_type mult2_def transpose_func_unique)
          then  show "(eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c mult2\<^sup>\<sharp>) \<circ>\<^sub>c x"
            by (simp add: calculation)
        qed
      qed
    qed
  qed
  then have main_result_flat: "mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> = mult2"
    by (metis mult2_type multp1p0_tye transpose_func_def)
  have "a \<cdot>\<^sub>\<nat> b = mult2 \<circ>\<^sub>c \<langle>a,b\<rangle>"
    by (simp add: mult_def)
  also have "... = (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c \<langle>a,b\<rangle>"
    by (simp add: main_result_flat)
  also have "... = mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>a,b\<rangle>"
    using assms by (typecheck_cfuncs, simp add: comp_associative2)
  also have "... = mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a,b\<rangle> ,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a,b\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs , simp add: cfunc_prod_comp)
  also have "... = mult2 \<circ>\<^sub>c \<langle>b, a\<rangle>"
    using assms left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod by force
  also have "... = b \<cdot>\<^sub>\<nat> a"
    by (simp add: mult_def)
  then show ?thesis using calculation by auto
qed




lemma mult_associative:
  assumes "a \<in>\<^sub>c  \<nat>\<^sub>c"  "b\<in>\<^sub>c  \<nat>\<^sub>c"  "c\<in>\<^sub>c  \<nat>\<^sub>c"
  shows "a \<cdot>\<^sub>\<nat> ( b \<cdot>\<^sub>\<nat> c)   = (a \<cdot>\<^sub>\<nat> b) \<cdot>\<^sub>\<nat> c"
proof -
   
  have multId_type: "mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c : (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c\<rightarrow> (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)"
    by (simp add: cfunc_cross_prod_type id_type mult2_type)
 
  have multmultId_type: "mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) : (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c\<rightarrow> \<nat>\<^sub>c"
    using comp_type multId_type mult2_type by blast
  have multIdmult_type: "(mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2)): \<nat>\<^sub>c\<times>\<^sub>c( \<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<rightarrow> \<nat>\<^sub>c"
    by (smt comp_type flat_type inv_transpose_func_def2 inv_transpose_of_composition mult1_type mult2_def)
  have multmultIdSharp_type: "(mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> :  \<nat>\<^sub>c\<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
    by (simp add: multmultId_type transpose_func_type)
  have mmIdSharp0_type: "(mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>\<circ>\<^sub>c zero : one \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
    using comp_type multmultIdSharp_type zero_type by blast
  have mmIdSharpS_type: "(mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>\<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
    using comp_type multmultIdSharp_type successor_type by auto
 have p0rho0_type: "(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) : (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c\<rightarrow> \<nat>\<^sub>c"
    using comp_type left_cart_proj_type by blast
  have p1rho0_type: "(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) : (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c\<rightarrow> \<nat>\<^sub>c"
    using comp_type left_cart_proj_type right_cart_proj_type by blast
  have p1rho0rho1_type: "\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle> :  (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c \<rightarrow>  (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)"
    by (simp add: cfunc_prod_type p1rho0_type right_cart_proj_type)
  have p0p0p1p0p1_type: "\<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>: (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c \<rightarrow>   \<nat>\<^sub>c \<times>\<^sub>c(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)"
    by (simp add: cfunc_prod_type p0rho0_type p1rho0rho1_type)
  have multIdxMultp0p0p1p0p1_type: "mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle> : (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c \<rightarrow>\<nat>\<^sub>c"
    by (metis (no_types) associate_right_def associate_right_type cfunc_cross_prod_type comp_type id_type mult2_type)
  have multIdxMultp0p0p1p0p1_Sharp_type: "(mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>: \<nat>\<^sub>c\<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>"
    using multIdxMultp0p0p1p0p1_type transpose_func_type by blast
 then have multIdxMultp0p0p1p0p0_Sharp0_type: "(mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero :  one \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>"
    using comp_type zero_type by blast
  have multIdxMultp0p0p1p0p0_SharpSucc_type: "(mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor :  \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>"
    using comp_type multIdxMultp0p0p1p0p1_Sharp_type successor_type by blast
  have zbsharp_type: "(zero \<circ>\<^sub>c \<beta>\<^bsub>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>cone\<^esub>)\<^sup>\<sharp>: one \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>"
    by (simp add: transpose_func_type zero_betaN_type)
  have multsigma0_type: "mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)):  ((\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>))\<rightarrow> \<nat>\<^sub>c"
    using comp_type left_cart_proj_type mult2_type by blast
  have multsigma0Eval_type: "\<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<rangle> : ((\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>))\<rightarrow> (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)"
    by (simp add: cfunc_prod_type eval_func_type multsigma0_type)
  then have addMultSigma0Eval_type: "add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<rangle> : ((\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>))\<rightarrow> \<nat>\<^sub>c"
    using add2_type comp_type by blast
  then have addMultSigma0EvalSharp_type: "(add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> : (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)\<rightarrow> (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)"
    using transpose_func_type by blast
  have id_multmultidsharp_type: "(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)): (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
    by (meson cfunc_cross_prod_type id_type multmultIdSharp_type)
  
  
  have main_result: "(mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> = 
(mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>"
    proof(rule natural_number_object_func_unique[where X = "\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>", where f = "(add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>"])
      show "(mult2 \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
        by (simp add: multmultIdSharp_type)
      show "(mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
        using multIdxMultp0p0p1p0p1_Sharp_type by blast
      show "(add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> : \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup> \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
        by (simp add: addMultSigma0EvalSharp_type)
      show "(mult2 \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero =
    (mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero"
      proof(rule same_evals_equal[where Z = one, where X = "\<nat>\<^sub>c", where A = "(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"])
        show "(mult2 \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero \<in>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
          by (simp add: mmIdSharp0_type)
        show "(mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero \<in>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
          using multIdxMultp0p0p1p0p0_Sharp0_type by blast
        show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero =
    eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero"
        proof(rule one_separator[where X = "(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c one", where Y = "\<nat>\<^sub>c"])
          show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one \<rightarrow> \<nat>\<^sub>c"
            using flat_type inv_transpose_func_def2 mmIdSharp0_type by force
          show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one \<rightarrow> \<nat>\<^sub>c"
            using flat_type inv_transpose_func_def2 multIdxMultp0p0p1p0p0_Sharp0_type by auto
          show "\<And>x. x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one \<Longrightarrow>
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c
          id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c
          id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
          (mult2 \<circ>\<^sub>c
           (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c
           \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x"
          proof - 
            fix x 
            assume x_type: "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one"
            obtain y where x_def: "y \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<and> x = \<langle>y, id one\<rangle>"
              using cart_prod_decomp id_type one_unique_element x_type by blast
            obtain p q where y_def: "p \<in>\<^sub>c \<nat>\<^sub>c \<and> q \<in>\<^sub>c \<nat>\<^sub>c \<and> y = \<langle>p,q\<rangle>"
              using cart_prod_decomp x_def by blast
            have y1_type: "x = \<langle>\<langle>p,q\<rangle>, id one\<rangle>"
              by (simp add: x_def y_def)

            have "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c
          id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x = 
            (((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c
          id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>)) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f  zero)) \<circ>\<^sub>c x"
              


(*
  have f1: "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>\<circ>\<^sub>c zero)))\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle> = zero" 
  proof - 
    have "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>\<circ>\<^sub>c zero)))\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle> = 
(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>\<circ>\<^sub>c zero))\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>"
    using assms by (typecheck_cfuncs, simp add: comp_associative2)
   also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>))\<circ>\<^sub>c ((id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f zero)) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>"
        using assms by (typecheck_cfuncs, smt comp_associative2 flat_cancels_sharp inv_transpose_func_def2 inv_transpose_of_composition)
    also have "... = (mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c   \<langle> id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>a,b\<rangle>, zero \<circ>\<^sub>c id\<^sub>c one\<rangle>"
        using assms by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod comp_associative2 transpose_func_def)
    also have "... = mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)  \<circ>\<^sub>c   \<langle>\<langle>a,b\<rangle>, zero\<rangle>"
        using assms by (typecheck_cfuncs, simp add: comp_associative2 id_left_unit2 id_right_unit2)
    also have "... = mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>a,b\<rangle>, zero\<rangle> "
      using ab_type cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_type mult2_type zero_type by fastforce
    also have "... = zero"
      using mult_def mult_respects_zero_right multab_type by auto
then show ?thesis using calculation by auto
qed


  have f2: "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero))) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle> = zero" 
  proof - 
    have "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero))) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle> = 
   (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero)) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>"
    using assms by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> )) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f zero)  \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>"
      using assms by (typecheck_cfuncs, smt comp_associative2 inv_transpose_func_def2 inv_transpose_of_composition transpose_func_def)
    also have "... = (mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f zero)  \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>"
       using assms by (typecheck_cfuncs, smt comp_associative2 transpose_func_def)
    also have "... = mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>\<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>a,b\<rangle>,zero \<circ>\<^sub>cid\<^sub>c one\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod comp_associative2)

    also have "... = mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,zero\<rangle>"
      using ab_type id_left_unit2 id_right_unit2 zero_type by auto
    also have "... = mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,zero\<rangle>,
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,zero\<rangle>  \<rangle>"
     using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
   also have "... = mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,zero\<rangle>,
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,zero\<rangle>  , (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,zero\<rangle>  \<rangle>  \<rangle>"
         using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
   also have "... = mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c  \<langle>a,b\<rangle>,
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c  \<langle>a,b\<rangle>  ,zero  \<rangle>  \<rangle>"
     using ab_type left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod zero_type by auto
   also have "... = mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>a , \<langle>b,zero\<rangle>  \<rangle>"
     using assms(1) assms(2) left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod by auto
   also have "... = mult2 \<circ>\<^sub>c  \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c a ,mult2 \<circ>\<^sub>c \<langle>b,zero\<rangle>  \<rangle>"
     using assms(1) b0_type id_type mult2_type cfunc_cross_prod_comp_cfunc_prod by fastforce
   also have "... = zero"
     using assms(1) assms(2) id_left_unit2 mult_def mult_respects_zero_right by auto
        then show ?thesis using calculation by auto
qed

 (*Moreover,...*)

     have f3: "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f (zero \<circ>\<^sub>c \<beta>\<^bsub>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>cone\<^esub>)\<^sup>\<sharp>))  \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle> = zero"
     proof - 
       have "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f (zero \<circ>\<^sub>c \<beta>\<^bsub>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>cone\<^esub>)\<^sup>\<sharp>))  \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle> =
(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f (zero \<circ>\<^sub>c \<beta>\<^bsub>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>cone\<^esub>)\<^sup>\<sharp>)  \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>"
          using assms apply typecheck_cfuncs
          using comp_associative2 by auto
       also have "... =  (zero \<circ>\<^sub>c \<beta>\<^bsub>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>cone\<^esub>) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>"
         by (metis calculation transpose_func_def zero_betaN_type)
       also have "... = zero \<circ>\<^sub>c (\<beta>\<^bsub>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>cone\<^esub> \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>)"
          using assms by (typecheck_cfuncs, simp add: comp_associative2)
       also have "... = zero"
          using assms by (typecheck_cfuncs, metis id_right_unit2 one_unique_element)
      then show ?thesis using calculation by auto
qed

(*Equation before "Likewise..." on page 19*)
  have f4: "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>\<circ>\<^sub>c successor) )
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle> = (a \<cdot>\<^sub>\<nat> b)  \<cdot>\<^sub>\<nat> (successor  \<circ>\<^sub>c c)"
  proof - 
    have "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>\<circ>\<^sub>c successor) )
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle> = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>\<circ>\<^sub>c successor) 
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
          using assms by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f successor) 
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
          using assms by (typecheck_cfuncs, smt comp_associative2 flat_cancels_sharp inv_transpose_func_def2 inv_transpose_of_composition)

    also have "... = mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f successor) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
          using assms by (typecheck_cfuncs, metis cfunc_type_def comp_associative transpose_func_def)
    also have "... = mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<circ>\<^sub>c  \<langle>a,b\<rangle>,successor \<circ>\<^sub>c c\<rangle>"
      using ab_type assms(3) cfunc_cross_prod_comp_cfunc_prod id_type successor_type by fastforce
    also have "... = mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c  (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<circ>\<^sub>c  \<langle>a,b\<rangle>),id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (successor \<circ>\<^sub>c c)\<rangle>"
      using id_ab_type sc_type mult2_type id_type cfunc_cross_prod_comp_cfunc_prod by fastforce
    also have "... =  mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c  (\<langle>a,b\<rangle>),(successor \<circ>\<^sub>c c)\<rangle>"
      using ab_type id_left_unit2 sc_type by auto
    also have "... = (a \<cdot>\<^sub>\<nat> b)  \<cdot>\<^sub>\<nat> (successor  \<circ>\<^sub>c c)"
      by (simp add: mult_def)
then show ?thesis using calculation by auto
qed

(*Likewise ...*)

  have f5: "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor)))
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle> = a \<cdot>\<^sub>\<nat> (b  \<cdot>\<^sub>\<nat> (successor  \<circ>\<^sub>c c))"
  proof - 
    have "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor)))
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle> =(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor))
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
          using assms by (typecheck_cfuncs, simp add: comp_associative2)
     also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>))
\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f  successor)
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
           using assms by (typecheck_cfuncs, smt comp_associative2 flat_cancels_sharp inv_transpose_func_def2 inv_transpose_of_composition)
    also have "... = (mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)
\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f  successor)
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
          using assms by (typecheck_cfuncs, smt comp_associative2 transpose_func_def)
    also have "... = (mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)
\<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>a,b\<rangle>,successor  \<circ>\<^sub>c c\<rangle>"
      using ab_type assms(3) cfunc_cross_prod_comp_cfunc_prod id_type successor_type by fastforce
    also have "... = (mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,successor  \<circ>\<^sub>c c\<rangle>"
      using ab_type id_left_unit2 by auto
    also have "... = mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,successor  \<circ>\<^sub>c c\<rangle>"
          using assms by (typecheck_cfuncs, simp add: comp_associative2)
          
    also have "... = mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,successor  \<circ>\<^sub>c c\<rangle> ,
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>    \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,successor  \<circ>\<^sub>c c\<rangle>   \<rangle>"
          using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
    also have "... = mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>a,b\<rangle> ,
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,successor  \<circ>\<^sub>c c\<rangle>  , (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,successor  \<circ>\<^sub>c c\<rangle>\<rangle>\<rangle>"
          using assms by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 left_cart_proj_cfunc_prod)
    also have "... = mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>a ,
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>a,b\<rangle>  , successor  \<circ>\<^sub>c c  \<rangle>  \<rangle>"
      using ab_type assms(1) assms(2) left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod sc_type by auto
    also have "... = mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>a,\<langle>b,successor  \<circ>\<^sub>c c\<rangle>\<rangle>"
      using assms(1) assms(2) right_cart_proj_cfunc_prod by auto
    also have "... = mult2 \<circ>\<^sub>c  \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c a, mult2 \<circ>\<^sub>c \<langle>b,successor  \<circ>\<^sub>c c\<rangle>\<rangle>"
      using assms(1) bSc_type id_type mult2_type cfunc_cross_prod_comp_cfunc_prod by fastforce
    also have "... =   a \<cdot>\<^sub>\<nat> (b  \<cdot>\<^sub>\<nat> (successor  \<circ>\<^sub>c c))"
      using assms(1) id_left_unit2 mult_def by auto
then show ?thesis using calculation by auto
qed

(*Now we compute this pair... *)

  have f6: "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>)
\<circ>\<^sub>c ((mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)
))  \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle> = (a \<cdot>\<^sub>\<nat> b)  \<cdot>\<^sub>\<nat> (successor  \<circ>\<^sub>c c)"
  proof - 
    have "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>)
\<circ>\<^sub>c ((mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)
))  \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle> = 
 (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>)
\<circ>\<^sub>c ((mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)
)  \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
          using assms by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>)) \<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>))\<circ>\<^sub>c
\<langle>\<langle>a,b\<rangle>,c\<rangle>"
          using assms by (typecheck_cfuncs, smt comp_associative2 inv_transpose_func_def2 inv_transpose_of_composition transpose_func_def)
    also have "... = (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<rangle>) \<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>))\<circ>\<^sub>c
\<langle>\<langle>a,b\<rangle>,c\<rangle>"
          using assms by (typecheck_cfuncs, smt comp_associative2 transpose_func_def)
    also have "... = ((add2 \<circ>\<^sub>c
\<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)),
eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<rangle>) 
\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)))
\<circ>\<^sub>c\<langle>\<langle>a,b\<rangle>,c\<rangle>"
                using assms by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = (
add2 \<circ>\<^sub>c
\<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>))
\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)),
eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)
\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>))\<rangle> 
)
\<circ>\<^sub>c\<langle>\<langle>a,b\<rangle>,c\<rangle>"
          using assms by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2)
    also have "... = (
add2 \<circ>\<^sub>c
\<langle>mult2 \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<nat>\<^sub>c) ,
eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)
\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>))\<rangle> 
)
\<circ>\<^sub>c\<langle>\<langle>a,b\<rangle>,c\<rangle>"
          using assms by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_cross_prod)
    also have "... = 
add2 \<circ>\<^sub>c
\<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<nat>\<^sub>c ,
eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)
\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>))\<rangle> 
\<circ>\<^sub>c\<langle>\<langle>a,b\<rangle>,c\<rangle>"
          using assms by (typecheck_cfuncs, simp add: comp_associative2 id_left_unit2)
also have "... = add2 \<circ>\<^sub>c
\<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c\<langle>\<langle>a,b\<rangle>,c\<rangle> ,
eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)
\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>))\<circ>\<^sub>c\<langle>\<langle>a,b\<rangle>,c\<rangle>   \<rangle>"
         apply(subst cfunc_prod_comp[where X = "one", where Y= "(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c",
                    where A = "\<nat>\<^sub>c", where B= "\<nat>\<^sub>c"])
          using abc_type apply force
          using comp_type left_cart_proj_type mult2_type apply blast
          using multmultId_type transpose_func_def apply auto[1]
          using assms by (typecheck_cfuncs, simp add: comp_associative2)

also have "... =  add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c  \<langle>a,b\<rangle> ,(mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c\<langle>\<langle>a,b\<rangle>,c\<rangle>   \<rangle>"
          using assms by (typecheck_cfuncs, simp add: comp_associative2 left_cart_proj_cfunc_prod transpose_func_def)
  also have "... = add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c  \<langle>a,b\<rangle> ,mult2  \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c\<langle>a,b\<rangle>,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c c\<rangle>   \<rangle>"
          using assms by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod comp_associative2)
  also have "... = (a \<cdot>\<^sub>\<nat> b) +\<^sub>\<nat> ((a \<cdot>\<^sub>\<nat> b)\<cdot>\<^sub>\<nat> c)"
    using add_def assms(3) id_left_unit2 mult_def by auto
  also have "... =  (a \<cdot>\<^sub>\<nat> b)  \<cdot>\<^sub>\<nat> (successor  \<circ>\<^sub>c c)"
    using assms(3) mult_def mult_respects_succ_right multab_type by auto
then show ?thesis using calculation by auto
qed


(*Next to last on page 20*)



  have f7: "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>)
\<circ>\<^sub>c  (mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>
))  \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle> = a \<cdot>\<^sub>\<nat> (b  \<cdot>\<^sub>\<nat> (successor  \<circ>\<^sub>c c))"
  proof - 
    have "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>)
\<circ>\<^sub>c  (mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>
))  \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle> =   
((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>)
))
\<circ>\<^sub>c ( id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f  (mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>)
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
          using assms by (typecheck_cfuncs, smt comp_associative2 inv_transpose_func_def2 inv_transpose_of_composition)
    also have "... = add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>))
, eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)
\<rangle>
\<circ>\<^sub>c ( id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f  (mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>)
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
          using assms by (typecheck_cfuncs, smt cfunc_type_def comp_associative transpose_func_def)
    also have "...  = (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>))
, eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)
\<rangle>
\<circ>\<^sub>c ( id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f  (mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>)
)\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
      using assms apply typecheck_cfuncs
      using comp_associative2 by auto
    also have "... = (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>))
\<circ>\<^sub>c ( id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f  (mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>)
, eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)
\<circ>\<^sub>c ( id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f  (mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>)\<rangle>
)\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
      apply (subst cfunc_prod_comp[where X ="(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c",
          where Y = "(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)", where A= "\<nat>\<^sub>c", where B="\<nat>\<^sub>c"])
      apply (simp add: cfunc_cross_prod_type id_type multIdxMultp0p0p1p0p1_Sharp_type)
      using multsigma0_type apply blast
      using eval_func_type apply force
      using assms by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>))
\<circ>\<^sub>c ( id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f  (mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>)
, 
  mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>\<rangle>
)\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
      using multIdxMultp0p0p1p0p1_type transpose_func_def by auto
    also have "... = 
(add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<nat>\<^sub>c)  
, 
  mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>\<rangle>
)\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
      by (smt id_type left_cart_proj_cfunc_cross_prod multIdxMultp0p0p1p0p1_Sharp_type)
    also have "... = 
     (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<nat>\<^sub>c)  
, 
  mult2  \<circ>\<^sub>c
 \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>
\<rangle>
\<rangle>
)\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
      using cfunc_cross_prod_comp_cfunc_prod id_type mult2_type p0rho0_type p1rho0rho1_type by fastforce
    also have "... = add2 \<circ>\<^sub>c 
\<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<nat>\<^sub>c)  
, 
  mult2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>
\<rangle>
\<rangle>
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
          using assms by (typecheck_cfuncs,simp add: comp_associative2 id_left_unit2)
    also have "... = add2 \<circ>\<^sub>c 
\<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<nat>\<^sub>c)  
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>
,
  mult2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>
\<rangle>
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle> \<rangle>"
      apply (subst cfunc_prod_comp[where X = "one", where Y = "(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c",
            where A = "\<nat>\<^sub>c", where B= "\<nat>\<^sub>c"])
      using abc_type apply blast
      using comp_type left_cart_proj_type mult2_type apply blast
      apply (smt cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_type multIdxMultp0p0p1p0p1_type mult2_type p0rho0_type p1rho0rho1_type)
      using assms by (typecheck_cfuncs, simp add: comp_associative2)

    also have "... =add2 \<circ>\<^sub>c 
\<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<nat>\<^sub>c)  
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>
,
  mult2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>
,
mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>
\<rangle>
 \<rangle>"
      apply (subst cfunc_prod_comp [where X = "one", where Y = "(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c",
            where  A = "\<nat>\<^sub>c", where B = "\<nat>\<^sub>c"])
      using abc_type apply blast
      using p0rho0_type apply fastforce
      using comp_type mult2_type p1rho0rho1_type apply blast
      using assms by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = add2 \<circ>\<^sub>c 
\<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<nat>\<^sub>c)  
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>
,
  mult2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>
,
mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>
, (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>  \<rangle>
\<rangle>
 \<rangle>"
      using assms apply typecheck_cfuncs
      using cfunc_prod_comp comp_associative2 by auto
    also have "... = add2 \<circ>\<^sub>c
\<langle>mult2 \<circ>\<^sub>c 
 \<langle>a,b\<rangle>
,
  mult2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>a,b\<rangle>
,
mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c  \<langle>a,b\<rangle>
, (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>  \<rangle>
\<rangle>
 \<rangle>"
      using ab_type assms(3) left_cart_proj_cfunc_prod by auto
    also have "... = add2 \<circ>\<^sub>c 
\<langle>mult2 \<circ>\<^sub>c \<langle>a,b\<rangle> ,mult2  \<circ>\<^sub>c \<langle>a, mult2 \<circ>\<^sub>c \<langle>b, c \<rangle>\<rangle>\<rangle>"
      using ab_type assms left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod by auto
    also have "... =  (a \<cdot>\<^sub>\<nat> b) +\<^sub>\<nat> a \<cdot>\<^sub>\<nat> (b \<cdot>\<^sub>\<nat> c)"
      by (simp add: add_def mult_def)
    also have "... = a \<cdot>\<^sub>\<nat> b  +\<^sub>\<nat> (b \<cdot>\<^sub>\<nat> c) \<cdot>\<^sub>\<nat> a"

HERE
*)





(* Don't forget to do Right Distributivity *)


lemma mult_right_distributivity:
  assumes "a \<in>\<^sub>c  \<nat>\<^sub>c"  "b\<in>\<^sub>c  \<nat>\<^sub>c"  "c\<in>\<^sub>c  \<nat>\<^sub>c"
  shows "a \<cdot>\<^sub>\<nat> ( b +\<^sub>\<nat> c)   = (a \<cdot>\<^sub>\<nat> b) +\<^sub>\<nat>  (a \<cdot>\<^sub>\<nat> c)"
  oops

lemma mult_pie_type: "mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>: \<nat>\<^sub>c \<times>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<rightarrow>  \<nat>\<^sub>c"
  by (meson cfunc_prod_type comp_type eval_func_type left_cart_proj_type mult2_type)

lemma mult_pie_sharp_type: "(mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>: \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
  by (simp add: mult_pie_type transpose_func_type)

end