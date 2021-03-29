theory ETCS_Exp
  imports ETCS_Mult
begin

(*Defining exponentiation on N*)

definition exp_curried :: "cfunc" where
   "exp_curried = (THE w. w: \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<and>
   triangle_commutes one \<nat>\<^sub>c  (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) zero w ((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>) \<and>
   square_commutes \<nat>\<^sub>c  (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) w ((mult_uncurried \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) successor w)"

lemma exp_curried_property: "(exp_curried: \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<and>
   triangle_commutes one \<nat>\<^sub>c  (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) zero exp_curried ((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>) \<and>
   square_commutes \<nat>\<^sub>c  (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) exp_curried ((mult_uncurried \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) successor exp_curried)"
  unfolding exp_curried_def
proof (rule theI')
  have q_type: "((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>) :  one \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
    by (meson comp_type right_cart_proj_type successor_type transpose_func_def zero_type)
  have f_type: "((mult_uncurried \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) : (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<rightarrow> (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)"
    using add_uncurried_type cfunc_type_def codomain_comp compatible_comp_ETCS_func domain_comp f_mult_flat_type mult_uncurried_type transpose_func_def by auto
  show "\<exists>!x. x : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<and>
         triangle_commutes one \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) zero x
          ((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>) \<and>
         square_commutes \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) x
          ((mult_uncurried \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>)
          successor x"
    by (simp add: f_type natural_number_object_property q_type)
qed

lemma exp_curried_type: "exp_curried:  \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
  by (simp add: exp_curried_property)
 
lemma exp_curried_0_eq: "exp_curried \<circ>\<^sub>c zero = ((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>)"
  using exp_curried_property triangle_commutes_def by blast

lemma exp_curried_comp_succ_eq: "exp_curried \<circ>\<^sub>c successor = ((mult_uncurried \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c exp_curried"
  using exp_curried_property square_commutes_def by auto

definition exp_uncurried :: "cfunc"
  where "exp_uncurried = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f exp_curried)"

lemma exp_uncurried_type: "exp_uncurried:  \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c"
  unfolding exp_uncurried_def
proof - 
  have "id \<nat>\<^sub>c \<times>\<^sub>f exp_curried : \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<times>\<^sub>c(\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)"
    by (simp add: exp_curried_property cfunc_cross_prod_type id_type)
  then show "eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f exp_curried : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    using comp_type eval_func_type by blast
qed

lemma exp_uncurried_apply:
  assumes "m : X \<rightarrow> \<nat>\<^sub>c" "n : X \<rightarrow> \<nat>\<^sub>c"
  shows "exp_uncurried \<circ>\<^sub>c \<langle>m, n\<rangle> = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, exp_curried \<circ>\<^sub>c n\<rangle>"
  by (smt exp_curried_property exp_uncurried_def assms cfunc_cross_prod_comp_cfunc_prod comp_associative id_left_unit2 id_type)


definition exp :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" (infixl "^\<^sub>\<nat>" 75)
  where "m ^\<^sub>\<nat> n = exp_uncurried\<circ>\<^sub>c\<langle>m, n\<rangle>"

lemma exp_def2:
  assumes "m\<in>\<^sub>c  \<nat>\<^sub>c" "n\<in>\<^sub>c  \<nat>\<^sub>c"
  shows "m ^\<^sub>\<nat> n = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, exp_curried \<circ>\<^sub>c n\<rangle>"
  unfolding exp_def exp_uncurried_def
  by (smt exp_curried_type assms cfunc_cross_prod_comp_cfunc_prod cfunc_type_def comp_associative id_left_unit id_type)



lemma exp_apply1:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n\<in>\<^sub>c \<nat>\<^sub>c"
  shows "m ^\<^sub>\<nat> n = exp_uncurried \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<circ>\<^sub>c n"
  unfolding add_def 
proof - 
  have fact1: "m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>:\<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    using assms(1) comp_type terminal_func_type by blast
  have "exp_uncurried \<circ>\<^sub>c \<langle>m,n\<rangle> = exp_uncurried \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c id one  ,id \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>"
    by (metis assms cfunc_type_def id_left_unit id_right_unit)
  also have "... = exp_uncurried \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c n)  ,id \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>"
    by (metis assms(2) comp_type id_type one_unique_element terminal_func_type)
  also have "... = exp_uncurried \<circ>\<^sub>c \<langle>(m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c n  ,id \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>"
    using comp_associative by auto
  also have "... = exp_uncurried \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<circ>\<^sub>c n"
    using assms(2) cfunc_prod_comp fact1 id_type by fastforce
  then show ?thesis
    by (simp add: calculation exp_def)
qed



lemma exp_apply1_left:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n\<in>\<^sub>c \<nat>\<^sub>c"
  shows "m ^\<^sub>\<nat> n = exp_uncurried \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<circ>\<^sub>c m"
  unfolding add_def 
proof - 
  have fact1: "n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>:\<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    using assms(2) comp_type terminal_func_type by blast
  have "exp_uncurried \<circ>\<^sub>c \<langle>m,n\<rangle> = exp_uncurried \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c \<circ>\<^sub>c m, n \<circ>\<^sub>c id one\<rangle>"
    by (metis assms cfunc_type_def id_left_unit id_right_unit)
  also have "... = exp_uncurried \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c \<circ>\<^sub>c m, n \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m)\<rangle>"
    by (metis assms(1) comp_type id_type one_unique_element terminal_func_type)
  also have "... = exp_uncurried \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c \<circ>\<^sub>c m, (n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c m\<rangle>"
    using comp_associative by auto
  also have "... = exp_uncurried \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<rangle> \<circ>\<^sub>c m"
    using assms(1) cfunc_prod_comp fact1 id_type by fastforce
  then show ?thesis
    by (simp add: calculation exp_def)
qed

lemma s0proj_type: "successor \<circ>\<^sub>c zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c one): \<nat>\<^sub>c \<times>\<^sub>c one \<rightarrow> \<nat>\<^sub>c"
    using comp_type right_cart_proj_type successor_type zero_type by blast
lemma s0projSharp_type: "(successor \<circ>\<^sub>c zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c one))\<^sup>\<sharp>: one \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
  by (simp add: s0proj_type transpose_func_def)


lemma exp_respects_Zero_Left:
  assumes "n \<in>\<^sub>c  \<nat>\<^sub>c"
  shows "n ^\<^sub>\<nat> zero = successor \<circ>\<^sub>c zero"
proof -
  have "n ^\<^sub>\<nat> zero =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n, exp_curried \<circ>\<^sub>c zero\<rangle>"
    by (simp add: assms exp_def2 zero_type)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>n,((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>)\<rangle>"
    by (simp add: exp_curried_0_eq)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c n,((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>) \<circ>\<^sub>c id\<^sub>c one\<rangle>"
    by (metis assms comp_associative exp_curried_0_eq id_left_unit2 id_right_unit2 zero_type)
  also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>n,id\<^sub>c one\<rangle>" 
    using assms exp_curried_property triangle_commutes_def id_type
    by (smt cfunc_cross_prod_comp_cfunc_prod)
  also have "... = successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one \<circ>\<^sub>c \<langle>n,id\<^sub>c one\<rangle>"
    using comp_associative s0proj_type transpose_func_def by auto
  also have "... = successor \<circ>\<^sub>c zero \<circ>\<^sub>c id\<^sub>c one"
    using assms id_type right_cart_proj_cfunc_prod by fastforce
  also have "... =  successor \<circ>\<^sub>c zero"
    using id_right_unit2 zero_type by auto
  then show ?thesis
    using calculation by auto
qed

(*Notice, in particular that 0^0 = 1*)


lemma exp_respects_one_right:
  assumes "n \<in>\<^sub>c  \<nat>\<^sub>c"
  shows "n ^\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = n" 
proof -
  have "n ^\<^sub>\<nat> (successor \<circ>\<^sub>c zero) =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n, exp_curried \<circ>\<^sub>c(successor \<circ>\<^sub>c zero) \<rangle>"
    using assms comp_type exp_def2 successor_type zero_type by blast
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n, ((mult_uncurried \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>cexp_curried \<circ>\<^sub>c zero \<rangle>"
    using comp_associative exp_curried_comp_succ_eq by auto
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n, ((mult_uncurried \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c ((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>)\<rangle>"
    by (simp add: exp_curried_0_eq)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c n, ((mult_uncurried \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c ((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>)\<rangle>"
    using assms id_left_unit2 by auto
  also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ((mult_uncurried \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>n,((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>)\<rangle>"
    by (smt assms cfunc_cross_prod_comp_cfunc_prod exp_curried_property id_type square_commutes_def triangle_commutes_def)
  also have "... = mult_uncurried \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>n,((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>)\<rangle>"
    using add_uncurried_type cfunc_type_def codomain_comp comp_associative compatible_comp_ETCS_func domain_comp f_mult_flat_type mult_uncurried_type transpose_func_def by auto
  also have "... = mult_uncurried \<circ>\<^sub>c
\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)
\<circ>\<^sub>c \<langle>n,((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>)\<rangle>,
eval_func \<nat>\<^sub>c \<nat>\<^sub>c 
\<circ>\<^sub>c \<langle>n,((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>)\<rangle> \<rangle> "
    using assms cfunc_prod_type s0projSharp_type left_cart_proj_type eval_func_type
    by (metis cfunc_prod_comp)
  also have "... =  mult_uncurried \<circ>\<^sub>c
\<langle>n ,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>)\<rangle> \<rangle> "
    using assms left_cart_proj_cfunc_prod s0projSharp_type by auto
  also have "... = mult_uncurried \<circ>\<^sub>c
\<langle>n ,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c n,((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>) \<circ>\<^sub>c id\<^sub>c one  \<rangle> \<rangle> "
    using assms id_left_unit2 id_right_unit2 s0projSharp_type by auto
  also have "... = mult_uncurried \<circ>\<^sub>c
\<langle>n ,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>))\<circ>\<^sub>c \<langle>n, id\<^sub>c one  \<rangle> \<rangle> "
    by (smt assms cfunc_cross_prod_comp_cfunc_prod id_type s0projSharp_type)
  also have "... = mult_uncurried \<circ>\<^sub>c \<langle>n ,successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one \<circ>\<^sub>c \<langle>n, id\<^sub>c one  \<rangle>\<rangle>"
    using comp_associative flat_cancels_sharp inv_transpose_func_def2 s0projSharp_type s0proj_type by fastforce
  also have "... = mult_uncurried \<circ>\<^sub>c \<langle>n ,successor \<circ>\<^sub>c zero \<circ>\<^sub>c id\<^sub>c one \<rangle>"
    by (metis (no_types) assms id_type right_cart_proj_cfunc_prod)
  also have "... = n"
    using assms id_right_unit2 mult_def s0_is_right_id zero_type by auto
  then show ?thesis
    using calculation by auto
qed

 lemma exp_respects_one_right:
   assumes "n \<in>\<^sub>c  \<nat>\<^sub>c"
   shows "zero ^\<^sub>\<nat> (successor \<circ>\<^sub>c n) = zero" 
 proof - 
   have zbz: "zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c zero = zero"
     using comp_associative successor_type terminal_func_comp zero_beta_succ_mEqs0 zero_type by auto
   have Exp0betaSucc0Eqs0: "exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, successor\<rangle> \<circ>\<^sub>c zero = zero"
     by (smt cfunc_prod_comp comp_associative exp_def exp_respects_one_right successor_type terminal_func_comp zbz zero_beta_N_succ_type zero_type)
   have zbsn: "(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor)\<circ>\<^sub>c n  = zero"
     by (metis assms comp_associative successor_type terminal_func_comp zbz zero_type)
   have zbzbn: "(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>)\<circ>\<^sub>c(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>)\<circ>\<^sub>c n = zero"
     using comp_associative successor_type terminal_func_comp zbsn zbz by auto

   have square_el: "(exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, successor\<rangle> \<circ>\<^sub>c successor)\<circ>\<^sub>c n = zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>"
   proof - 
     have "(exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, successor\<rangle> \<circ>\<^sub>c successor)\<circ>\<^sub>c n = 
     eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, exp_curried \<circ>\<^sub>c successor \<rangle> \<circ>\<^sub>c successor \<circ>\<^sub>c n"
       using comp_associative exp_uncurried_apply successor_type terminal_func_comp zero_beta_N_succ_type by auto
     also have "... =  eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c 
\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, ((mult_uncurried \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c exp_curried\<rangle> \<circ>\<^sub>c successor \<circ>\<^sub>c n"
       using exp_curried_comp_succ_eq by auto
     also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c 
\<langle>id\<^sub>c\<nat>\<^sub>c \<circ>\<^sub>c  zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, ((mult_uncurried \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c exp_curried\<rangle> \<circ>\<^sub>c successor \<circ>\<^sub>c n"
       using id_left_unit2 successor_type terminal_func_comp zero_beta_N_succ_type by auto
     also have "... =  eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c  (id\<^sub>c\<nat>\<^sub>c \<times>\<^sub>f ((mult_uncurried \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>)) 
\<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, exp_curried\<rangle> \<circ>\<^sub>c successor \<circ>\<^sub>c n"
       by (smt cfunc_cross_prod_comp_cfunc_prod comp_associative exp_curried_property id_type square_commutes_def terminal_func_comp zero_beta_N_succ_type)
     also have "... = (mult_uncurried \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, exp_curried\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c n"
       using add_uncurried_type cfunc_type_def codomain_comp comp_associative compatible_comp_ETCS_func domain_comp f_mult_flat_type mult_uncurried_type transpose_func_def by auto
     also have "... =  (mult_uncurried \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, exp_curried\<rangle> ,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, exp_curried\<rangle> \<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c n"
       apply(subst cfunc_prod_comp[where X = "\<nat>\<^sub>c", where Y = "\<nat>\<^sub>c \<times>\<^sub>c(\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)", where A= "\<nat>\<^sub>c", where B="\<nat>\<^sub>c"])
       apply (simp add: cfunc_prod_type exp_curried_property zero_betaN_type)
       apply (simp add: left_cart_proj_type)
       using eval_func_type apply blast
       by simp
     also have "... = (mult_uncurried \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, exp_curried\<rangle> ,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id\<^sub>c\<nat>\<^sub>c \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, exp_curried \<circ>\<^sub>c id\<^sub>c\<nat>\<^sub>c\<rangle> \<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c n"
       using exp_curried_type id_left_unit2 id_right_unit2 successor_type terminal_func_comp zero_beta_N_succ_type by auto
     also have "... = (mult_uncurried \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, exp_curried\<rangle> ,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c\<nat>\<^sub>c \<times>\<^sub>f exp_curried) \<circ>\<^sub>c  \<langle> zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,  id\<^sub>c\<nat>\<^sub>c\<rangle> \<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c n"
       by (smt cfunc_cross_prod_comp_cfunc_prod exp_curried_property id_type successor_type terminal_func_comp zero_beta_N_succ_type)
     also have "... = (mult_uncurried \<circ>\<^sub>c\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c\<nat>\<^sub>c \<times>\<^sub>f exp_curried) \<circ>\<^sub>c  \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,  id\<^sub>c\<nat>\<^sub>c\<rangle> \<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c n"
       by (metis (no_types) exp_curried_property left_cart_proj_cfunc_prod zero_betaN_type)
     also have "... = (mult_uncurried \<circ>\<^sub>c\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,  id\<^sub>c\<nat>\<^sub>c\<rangle> \<rangle>)\<circ>\<^sub>c successor \<circ>\<^sub>c n"
       by (simp add: comp_associative exp_uncurried_def)
     also have "... = zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor \<circ>\<^sub>c n"
       oops

(*
lemma exp_respects_one_left:
   assumes "n \<in>\<^sub>c  \<nat>\<^sub>c"
   shows "(successor \<circ>\<^sub>c zero)^\<^sub>\<nat> n = (successor \<circ>\<^sub>c zero)" 
proof - 
  have s0b0Eqs0: "((successor \<circ>\<^sub>c zero)\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero = (successor \<circ>\<^sub>c zero)"
    by (metis comp_associative successor_type terminal_func_comp zero_beta_succ_mEqs0 zero_type)
  have ExpS0b1z: "(exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c zero)\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id\<^sub>c\<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero = (successor \<circ>\<^sub>c zero)"
    by (metis (no_types, hide_lams) cfunc_type_def comp_associative compatible_comp_ETCS_func exp_apply1 exp_respects_Zero_Left s0b_type zero_type)
  have szbs_n: "(((successor \<circ>\<^sub>c zero)\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor) \<circ>\<^sub>c  n = ((successor \<circ>\<^sub>c zero)\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c  n"
    by (metis comp_associative successor_type terminal_func_comp)
  have expSzbIdsnEqsIdExpS0bIdn: "(exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id\<^sub>c\<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c (successor \<circ>\<^sub>c n)
                                   = (id\<^sub>c\<nat>\<^sub>c \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id\<^sub>c\<nat>\<^sub>c\<rangle>)\<circ>\<^sub>c n"
  (*
  proof -

    have s0_type: "successor \<circ>\<^sub>c zero : one \<rightarrow> \<nat>\<^sub>c"
      using successor_type zero_type by auto
    have sn_type: "successor \<circ>\<^sub>c n : one \<rightarrow> \<nat>\<^sub>c"
      by (meson assms comp_type successor_type)
    have "(exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id\<^sub>c\<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c (successor \<circ>\<^sub>c n) =exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id\<^sub>c\<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (successor \<circ>\<^sub>c n)"
      by (simp add: comp_associative)
    also have "... = exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c (successor \<circ>\<^sub>c n),  successor \<circ>\<^sub>c n\<rangle>"
      by (smt assms cfunc_prod_comp comp_associative id_left_unit2 id_type s0b_type successor_type terminal_func_comp)
    also have "... =  exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero, successor \<circ>\<^sub>c n\<rangle>"
      using assms zero_beta_succ_mEqs0 by auto
    also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id\<^sub>c\<nat>\<^sub>c \<times>\<^sub>f exp_curried) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero, successor \<circ>\<^sub>c n\<rangle>"
      by (simp add: comp_associative exp_uncurried_def)
    also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id\<^sub>c\<nat>\<^sub>c \<times>\<^sub>f (id\<^sub>c(\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c exp_curried)) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero, successor \<circ>\<^sub>c n\<rangle>"
      using exp_curried_property id_left_unit2 by auto
    also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id\<^sub>c\<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c(\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero, exp_curried \<circ>\<^sub>c successor \<circ>\<^sub>c n\<rangle>"
      by (metis \<open>eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f exp_curried) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero,successor \<circ>\<^sub>c n\<rangle> = eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c exp_curried) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero,successor \<circ>\<^sub>c n\<rangle>\<close> \<open>exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero,successor \<circ>\<^sub>c n\<rangle> = eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f exp_curried) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero,successor \<circ>\<^sub>c n\<rangle>\<close> comp_associative eval_func_type exp_uncurried_apply id_cross_prod id_right_unit2 s0_type sn_type)
    also have "... =  eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id\<^sub>c\<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c(\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero, ((mult_uncurried \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>)     \<circ>\<^sub>c  exp_curried  \<circ>\<^sub>c n\<rangle>"
      by (simp add: comp_associative exp_curried_comp_succ_eq)
    also have "... =  eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id\<^sub>c\<nat>\<^sub>c \<times>\<^sub>f (id\<^sub>c(\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c ((mult_uncurried \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) ) ) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero,    exp_curried  \<circ>\<^sub>c n\<rangle>"
      oops
    *)
*)

lemma exp_respects_successor:
   assumes "m \<in>\<^sub>c  \<nat>\<^sub>c" "n \<in>\<^sub>c  \<nat>\<^sub>c"
   shows "m^\<^sub>\<nat>(successor \<circ>\<^sub>c n) = m \<cdot>\<^sub>\<nat> (m^\<^sub>\<nat> n) "
proof - 
  have "m^\<^sub>\<nat>(successor \<circ>\<^sub>c n) = exp_uncurried \<circ>\<^sub>c \<langle>m,successor \<circ>\<^sub>c n\<rangle>"
    by (simp add: exp_def)
  also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f exp_curried) \<circ>\<^sub>c  \<langle>m,successor \<circ>\<^sub>c n\<rangle>"
    by (simp add: comp_associative exp_uncurried_def)
  also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f exp_curried) \<circ>\<^sub>c  \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m,successor \<circ>\<^sub>c n\<rangle>"
    using assms(1) id_left_unit2 by auto
  also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f exp_curried \<circ>\<^sub>c successor) \<circ>\<^sub>c  \<langle>m, n\<rangle>"
    apply (subst cfunc_cross_prod_comp_cfunc_prod[where A = one, where W ="\<nat>\<^sub>c", 
          where X ="\<nat>\<^sub>c",  where Y ="\<nat>\<^sub>c", where Z = "\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"])
    using assms(1) id_left_unit2 apply auto[1]
    using assms(2) comp_type successor_type apply blast
    using id_type apply auto[1]
    apply (simp add: exp_curried_type)
    oops

end