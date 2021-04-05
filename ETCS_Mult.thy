theory ETCS_Mult
  imports ETCS_Add
begin

(*Defining multiplication on N*)
  oops



definition mult_curried :: "cfunc" where
   "mult_curried = (THE v. v: \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<and>
   triangle_commutes one \<nat>\<^sub>c  (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) zero v ((zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c one))\<^sup>\<sharp>) \<and>
   square_commutes \<nat>\<^sub>c  (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) v 
((add_uncurried  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>) successor v)"



lemma mult_curried_property: "(mult_curried: \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<and>
   triangle_commutes one \<nat>\<^sub>c  (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) zero mult_curried ((zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c one))\<^sup>\<sharp>) \<and>
   square_commutes \<nat>\<^sub>c  (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) mult_curried 
((add_uncurried  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>) successor mult_curried)"
  unfolding mult_curried_def
proof (rule theI')
  have q_type: "((zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c one))\<^sup>\<sharp>) :  one \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
    using comp_type right_cart_proj_type transpose_func_def zero_type by blast
  have f_type: "((add_uncurried  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>) : (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<rightarrow> (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)"
    by (meson add_uncurried_type cfunc_prod_type comp_type eval_func_type left_cart_proj_type transpose_func_def)
  show "\<exists>!x. x : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<and>
          triangle_commutes one \<nat>\<^sub>c  (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) zero x ((zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c one))\<^sup>\<sharp>) \<and>
         square_commutes \<nat>\<^sub>c  (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) x 
((add_uncurried  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>) successor x"
    by (simp add: f_type natural_number_object_property q_type)
qed


lemma mult_curried_type: "mult_curried:  \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
  by (simp add: mult_curried_property)
 
lemma mult_curried_0_eq: "mult_curried \<circ>\<^sub>c zero = ((zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c one))\<^sup>\<sharp>)"
  using mult_curried_property triangle_commutes_def by blast

lemma mult_curried_comp_succ_eq: "mult_curried \<circ>\<^sub>c successor =
  ((add_uncurried  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c mult_curried"
  using mult_curried_property square_commutes_def by auto

definition mult_uncurried :: "cfunc"
  where "mult_uncurried = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f mult_curried)"

lemma mult_uncurried_type: "mult_uncurried:  \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c"
  unfolding mult_uncurried_def
proof - 
  have "id \<nat>\<^sub>c \<times>\<^sub>f mult_curried : \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<times>\<^sub>c(\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)"
    by (simp add: cfunc_cross_prod_type id_type mult_curried_type)
  then show "eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult_curried) : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    using comp_type eval_func_type by blast
qed

lemma f_mult_type: "(add_uncurried  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>: (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<rightarrow> (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)"
  using mult_curried_property square_commutes_def by auto

lemma f_mult_flat_type: "(add_uncurried  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>) : (\<nat>\<^sub>c \<times>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)) \<rightarrow> \<nat>\<^sub>c"
  by (meson add_uncurried_type cfunc_prod_type comp_type eval_func_type left_cart_proj_type)

definition mult :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" (infixl "\<cdot>\<^sub>\<nat>" 70)
  where "m \<cdot>\<^sub>\<nat> n = mult_uncurried\<circ>\<^sub>c\<langle>m, n\<rangle>"

lemma mult_def2:
  assumes "m\<in>\<^sub>c  \<nat>\<^sub>c" "n\<in>\<^sub>c  \<nat>\<^sub>c"
  shows "m \<cdot>\<^sub>\<nat> n = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, mult_curried \<circ>\<^sub>c n\<rangle>"
  unfolding mult_def mult_uncurried_def
  by (smt assms(1) assms(2) cfunc_cross_prod_comp_cfunc_prod cfunc_type_def comp_associative id_left_unit id_type mult_curried_property)

lemma mult_apply1right:
  assumes "m\<in>\<^sub>c  \<nat>\<^sub>c" "n\<in>\<^sub>c  \<nat>\<^sub>c"
  shows  "m \<cdot>\<^sub>\<nat> n = mult_uncurried \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<circ>\<^sub>c n"
  unfolding mult_def
proof -  
  have fact1: "m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>:\<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    using assms(1) comp_type terminal_func_type by blast
  have "mult_uncurried \<circ>\<^sub>c \<langle>m,n\<rangle> = mult_uncurried \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c id one  ,id \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>"
    by (metis assms cfunc_type_def id_left_unit id_right_unit)
  also have "... = mult_uncurried \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c n)  ,id \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>"
    by (metis assms(2) comp_type id_type one_unique_element terminal_func_type)
  also have "... = mult_uncurried \<circ>\<^sub>c \<langle>(m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c n  ,id \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>"
    using comp_associative by auto
  also have "... = mult_uncurried \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<circ>\<^sub>c n"
    using assms(2) cfunc_prod_comp fact1 id_type by fastforce
  then show "mult_uncurried \<circ>\<^sub>c \<langle>m,n\<rangle> = mult_uncurried \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c n" 
    using calculation by auto
qed

lemma mult_apply1_left:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n\<in>\<^sub>c \<nat>\<^sub>c"
  shows "m  \<cdot>\<^sub>\<nat>  n = mult_uncurried \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<circ>\<^sub>c m"
  unfolding mult_def 
proof - 
  have fact1: "n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>:\<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    using assms(2) comp_type terminal_func_type by blast
  have "mult_uncurried \<circ>\<^sub>c \<langle>m,n\<rangle> = mult_uncurried \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c \<circ>\<^sub>c m, n \<circ>\<^sub>c id one\<rangle>"
    by (metis assms cfunc_type_def id_left_unit id_right_unit)
  also have "... = mult_uncurried \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c \<circ>\<^sub>c m, n \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m)\<rangle>"
    by (metis assms(1) comp_type id_type one_unique_element terminal_func_type)
  also have "... = mult_uncurried \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c \<circ>\<^sub>c m, (n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c m\<rangle>"
    using comp_associative by auto
  also have "... = mult_uncurried \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<rangle> \<circ>\<^sub>c m"
    using assms(1) cfunc_prod_comp fact1 id_type by fastforce
  then show "mult_uncurried \<circ>\<^sub>c \<langle>m,n\<rangle> = mult_uncurried \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c m" 
    using calculation by auto
qed


lemma mult_respects_zero_right:
  assumes "m\<in>\<^sub>c  \<nat>\<^sub>c"
  shows "m \<cdot>\<^sub>\<nat> zero = zero"
proof - 
  have "m \<cdot>\<^sub>\<nat> zero =  mult_uncurried\<circ>\<^sub>c\<langle>m, zero\<rangle>"
    by (simp add: mult_def)
  also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, mult_curried \<circ>\<^sub>c zero\<rangle>"
    using assms calculation mult_def2 zero_type by auto
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, ((zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c one))\<^sup>\<sharp>) \<rangle>"
    by (simp add: mult_curried_0_eq)
  also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f((zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c one))\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>m, id\<^sub>c one\<rangle>"
    by (smt assms cfunc_cross_prod_comp_cfunc_prod cfunc_type_def id_left_unit id_right_unit id_type mult_curried_property triangle_commutes_def)
  also have "... = zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c one) \<circ>\<^sub>c \<langle>m, id\<^sub>c one\<rangle>"
    by (metis comp_associative comp_type right_cart_proj_type transpose_func_def zero_type)
  also have "... = zero"
    by (metis assms cfunc_type_def id_right_unit id_type right_cart_proj_cfunc_prod zero_type)
then show ?thesis using calculation by auto
qed

lemma mult_curried_n: 
   assumes "n\<in>\<^sub>c  \<nat>\<^sub>c"
   shows "mult_curried\<circ>\<^sub>c n: one \<rightarrow> (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)"
  using assms mult_curried_type by auto




lemma mult_respects_succ_right:
  assumes "m\<in>\<^sub>c  \<nat>\<^sub>c" "n\<in>\<^sub>c  \<nat>\<^sub>c"
  shows "m \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c n) = m +\<^sub>\<nat> (m \<cdot>\<^sub>\<nat> n)"
proof - 
  have fact: "\<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m, mult_curried\<circ>\<^sub>c n\<rangle>: one \<rightarrow> (\<nat>\<^sub>c \<times>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>))"
    using assms(1) assms(2) cfunc_prod_type id_type mult_curried_n by auto
  have "m \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c n) = mult_uncurried\<circ>\<^sub>c\<langle>m, (successor \<circ>\<^sub>c n)\<rangle>"
    by (simp add: mult_def)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult_curried)\<circ>\<^sub>c \<langle>m, (successor \<circ>\<^sub>c n)\<rangle>"
    using comp_associative mult_uncurried_def by auto
  also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, mult_curried \<circ>\<^sub>c (successor \<circ>\<^sub>c n)\<rangle>"
    using assms(1) assms(2) calculation mult_def2 successor_type by auto
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m,((add_uncurried  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>)\<circ>\<^sub>c mult_curried \<circ>\<^sub>c n  \<rangle>"
    by (simp add: comp_associative mult_curried_comp_succ_eq)
   also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m,((add_uncurried  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>)\<circ>\<^sub>c mult_curried \<circ>\<^sub>c n  \<rangle>"
     using add_apply1 add_respects_zero_on_left assms(1) comp_associative id_N_def2 zero_type by auto
  also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f 
(add_uncurried  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>)
 \<circ>\<^sub>c \<langle>m,mult_curried \<circ>\<^sub>c n  \<rangle>"
    using cfunc_cross_prod_comp_cfunc_prod
    by (smt assms(1) assms(2) f_mult_type id_type mult_curried_n)
  also have "... =(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f 
(add_uncurried  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>)
 )\<circ>\<^sub>c \<langle>m,mult_curried \<circ>\<^sub>c n  \<rangle>"
    using comp_associative by auto
  also have "... = (add_uncurried  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),
(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)
       \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m, mult_curried\<circ>\<^sub>c n\<rangle>"
    using f_mult_flat_type transpose_func_def
    by (metis assms(1) cfunc_type_def id_left_unit)
  also have "... = add_uncurried  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>))
\<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m, mult_curried\<circ>\<^sub>c n\<rangle>,
(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m, mult_curried\<circ>\<^sub>c n\<rangle> \<rangle>
       "
    using cfunc_prod_comp
    by (metis comp_associative eval_func_type fact left_cart_proj_type)
  also have "...  = add_uncurried  \<circ>\<^sub>c \<langle>m,
(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m, mult_curried\<circ>\<^sub>c n\<rangle> \<rangle>"
    by (metis assms(1) assms(2) cfunc_type_def id_left_unit left_cart_proj_cfunc_prod mult_curried_n)
  also have "... = add_uncurried  \<circ>\<^sub>c \<langle>m, 
   (eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  mult_curried)\<circ>\<^sub>c \<langle>m,n\<rangle>\<rangle>"
    using assms(1) assms(2) cfunc_cross_prod_comp_cfunc_prod id_type mult_curried_property by fastforce
  also have "... = add_uncurried  \<circ>\<^sub>c \<langle>m, mult_uncurried \<circ>\<^sub>c \<langle>m,n\<rangle>\<rangle>"
    by (simp add: comp_associative mult_uncurried_def)
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
  by (metis (mono_tags, hide_lams) assms comp_type id_type one_unique_element successor_type terminal_func_type)

lemma zero_beta_N_succ_type:
  "zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
  using cfunc_type_def codomain_comp compatible_comp_ETCS_func domain_comp successor_type zero_betaN_type by auto

lemma zero_beta_succ_mEqs0:
  assumes "m\<in>\<^sub>c  \<nat>\<^sub>c"
  shows "zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor \<circ>\<^sub>c m  = zero"
  by (metis assms beta_N_succ_mEqs_Id1 cfunc_type_def id_right_unit zero_type)



lemma  zero_beta_succ_prod_mult_curried_type: 
  "\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,mult_curried\<rangle>: \<nat>\<^sub>c \<rightarrow> (\<nat>\<^sub>c \<times>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>))"
  by (simp add: cfunc_prod_type mult_curried_type zero_beta_N_succ_type)

lemma mult_prod_0bs_id_type: "mult_uncurried \<circ>\<^sub>c  \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,id\<^sub>c \<nat>\<^sub>c\<rangle>: \<nat>\<^sub>c\<rightarrow> \<nat>\<^sub>c"
proof -
  have f1: "\<forall>c ca. ((ca \<circ>\<^sub>c c : domain c \<rightarrow> codomain ca \<or> domain ca \<noteq> codomain c) \<or> c \<notin> ETCS_func) \<or> ca \<notin> ETCS_func"
    using cfunc_type_def codomain_comp compatible_comp_ETCS_func domain_comp by presburger
  have f2: "codomain successor = \<nat>\<^sub>c"
    using cfunc_type_def successor_type by blast
have f3: "domain successor = \<nat>\<^sub>c"
  using cfunc_type_def successor_type by presburger
  have f4: "successor \<in> ETCS_func"
    using cfunc_type_def successor_type by blast
  have f5: "\<forall>c. domain (\<beta>\<^bsub>c\<^esub>) = c"
  by (meson cfunc_type_def terminal_func_type)
  have f6: "\<forall>c. codomain (\<beta>\<^bsub>c\<^esub>) = one"
    using cfunc_type_def terminal_func_type by presburger
  have f7: "\<forall>c. \<beta>\<^bsub>c\<^esub> \<in> ETCS_func"
    using cfunc_type_def terminal_func_type by presburger
  have f8: "domain mult_uncurried = domain add_uncurried"
    using add_uncurried_type cfunc_type_def mult_uncurried_type by auto
have f9: "codomain mult_uncurried = \<nat>\<^sub>c"
using cfunc_type_def mult_uncurried_type by blast
have "mult_uncurried \<in> ETCS_func"
  using cfunc_type_def mult_uncurried_type by blast
  then show ?thesis
    using f9 f8 f7 f6 f5 f4 f3 f2 f1 by (metis (no_types) compatible_comp_ETCS_func domain_comp id_ETCS_func id_N_def2 id_domain terminal_func_unique)
qed


lemma mult_respects_zero_left:
  assumes "m\<in>\<^sub>c  \<nat>\<^sub>c" 
  shows "zero \<cdot>\<^sub>\<nat> m = zero"
proof - 
  
  have triangle1: "mult_uncurried \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c zero = zero"
  proof - 
    have "mult_uncurried \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c zero = 
          mult_uncurried \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero , zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c zero\<rangle>"
      by (smt cfunc_prod_comp comp_associative id_type zero_betaN_type zero_type)
    also have "... = mult_uncurried \<circ>\<^sub>c \<langle>zero, zero \<circ>\<^sub>c id\<^sub>c one\<rangle>"
      by (metis cfunc_type_def id_left_unit id_type natural_number_object_property terminal_func_unique triangle_commutes_def)
    also have "... = zero"
      by (metis cfunc_type_def id_right_unit mult_def mult_respects_zero_right zero_type)
then show ?thesis using calculation by auto
qed



  have triangle2: "mult_uncurried \<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id\<^sub>c \<nat>\<^sub>c \<rangle>  \<circ>\<^sub>c zero = zero"
      proof -
            have f1: "id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero = zero"
            by (metis (no_types) cfunc_type_def id_left_unit zero_type)
              have "mult_uncurried \<circ>\<^sub>c \<langle>(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero,zero\<rangle> = zero"
            by (metis (no_types) comp_type mult_def mult_respects_zero_right terminal_func_type zero_type)
              then show ?thesis
                using f1 cfunc_prod_comp cfunc_type_def comp_type id_type terminal_func_type zero_type by force
  qed




have square1: "mult_uncurried \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c successor
               = mult_uncurried \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
proof (rule one_separator[where X="\<nat>\<^sub>c", where Y="\<nat>\<^sub>c"])
  show f1: "mult_uncurried \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by (metis (mono_tags, lifting) cfunc_type_def codomain_comp compatible_comp_ETCS_func domain_comp successor_type triangle1 zero_type)
  show f2: "mult_uncurried \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    using cfunc_type_def codomain_comp compatible_comp_ETCS_func domain_comp f1 successor_type by auto
next
  fix m
  assume assms: "m \<in>\<^sub>c \<nat>\<^sub>c"
  have "mult_uncurried \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c successor \<circ>\<^sub>c m =
        mult_uncurried \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor \<circ>\<^sub>c m, zero \<circ>\<^sub>c  \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor \<circ>\<^sub>c m\<rangle>"
    using assms cfunc_prod_comp cfunc_type_def comp_associative compatible_comp_ETCS_func domain_comp id_type successor_type zero_betaN_type by auto
  also have "... = mult_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c m, zero\<rangle>"
    using beta_N_succ_mEqs_Id1
    by (metis assms cfunc_type_def codomain_comp id_left_unit id_right_unit successor_type zero_type)
  also have "... = zero"
    using assms mult_def mult_respects_zero_right successor_type by auto
  also have "... = mult_uncurried \<circ>\<^sub>c \<langle>m, zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m \<rangle>"
    by (metis assms cfunc_type_def comp_type id_right_unit id_type mult_def mult_respects_zero_right one_unique_element terminal_func_type zero_type)
  also have "... = mult_uncurried \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m, zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m \<rangle>"
    using add_apply1 add_respects_zero_on_left assms comp_associative id_N_def2 zero_type by auto
  also have "... =  mult_uncurried \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c m"
    by (smt assms cfunc_prod_comp comp_associative id_type zero_betaN_type)
  then show "(mult_uncurried \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c successor) \<circ>\<^sub>c m =
         (mult_uncurried \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c m"
    using calculation comp_associative by auto
qed

have square2: "mult_uncurried \<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c \<rangle> \<circ>\<^sub>c successor  = id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c
               mult_uncurried \<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c \<rangle>"
proof - 
   have "mult_uncurried \<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c \<rangle> \<circ>\<^sub>c successor  =
        mult_uncurried \<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,successor\<rangle> "
    by (smt cfunc_prod_comp cfunc_type_def comp_associative id_left_unit id_type successor_type zero_betaN_type)
  also have "... = (eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult_curried) \<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,successor\<rangle>"
    using comp_associative mult_uncurried_def by auto
  also have "... = (eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,mult_curried \<circ>\<^sub>c successor\<rangle>"
    by (smt cfunc_cross_prod_comp_cfunc_prod cfunc_prod_comp cfunc_type_def comp_associative id_left_unit id_right_unit id_type mult_curried_property successor_type zero_betaN_type)
  also have "... = (eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,
  ((add_uncurried  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c mult_curried \<rangle>"
    using mult_curried_comp_succ_eq
    by (metis cfunc_type_def comp_associative id_left_unit zero_type)
  also have "... = (eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add_uncurried  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>) 
  \<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,mult_curried\<rangle>"
    using  cfunc_cross_prod_comp_cfunc_prod
    by (smt comp_associative f_mult_type id_type mult_curried_property zero_beta_N_succ_type)
  also have "... = (add_uncurried  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>) \<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,mult_curried\<rangle>"
    using comp_associative f_mult_flat_type transpose_func_def by auto
  also have "... = add_uncurried  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>))\<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,mult_curried\<rangle>,(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,mult_curried\<rangle> \<rangle>"
       using cfunc_prod_comp
       by (metis comp_associative eval_func_type left_cart_proj_type zero_beta_succ_prod_mult_curried_type)
  also have "... = add_uncurried  \<circ>\<^sub>c \<langle> zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,mult_curried\<rangle> \<rangle>"
    using left_cart_proj_cfunc_prod mult_curried_property zero_beta_N_succ_type by auto
  also have "... = add_uncurried  \<circ>\<^sub>c \<langle> zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult_curried) \<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,id\<^sub>c \<nat>\<^sub>c\<rangle> \<rangle>"
    by (smt cfunc_cross_prod_comp_cfunc_prod cfunc_type_def id_left_unit id_right_unit id_type mult_curried_property zero_beta_N_succ_type)
  also have "... =  add_uncurried  \<circ>\<^sub>c \<langle> zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c mult_uncurried \<circ>\<^sub>c  \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,id\<^sub>c \<nat>\<^sub>c\<rangle> , mult_uncurried \<circ>\<^sub>c  \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,id\<^sub>c \<nat>\<^sub>c\<rangle>  \<rangle> "
    by (metis comp_associative mult_prod_0bs_id_type mult_uncurried_def successor_type terminal_func_comp)
  also have "... =  add_uncurried  \<circ>\<^sub>c \<langle> zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,  id\<^sub>c \<nat>\<^sub>c  \<rangle> \<circ>\<^sub>c (mult_uncurried \<circ>\<^sub>c  \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor,id\<^sub>c \<nat>\<^sub>c\<rangle>) "
    by (smt cfunc_prod_comp comp_associative id_left_unit2 id_type mult_prod_0bs_id_type successor_type terminal_func_comp zero_beta_N_succ_type)
  also have "... =id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c
             mult_uncurried \<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c \<rangle>"
    using comp_associative id_N_def2 successor_type terminal_func_comp by auto
  then show ?thesis using calculation by auto
qed

  have "mult_uncurried \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> = mult_uncurried \<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c \<rangle>"
  proof (rule natural_number_object_func_unique[where f="id\<^sub>c \<nat>\<^sub>c", where X="\<nat>\<^sub>c"])
    show  f1: "mult_uncurried \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
      by (metis (mono_tags, lifting) cfunc_type_def codomain_comp compatible_comp_ETCS_func domain_comp triangle1 zero_type)
    show f2: "mult_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
      using mult_prod_0bs_id_type successor_type terminal_func_comp by auto
    show "id\<^sub>c \<nat>\<^sub>c : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
      by (meson id_type)
    show "(mult_uncurried \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c zero =
    (mult_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero"
      using comp_associative triangle1 triangle2 by presburger
    show "(mult_uncurried \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c successor =
    id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c mult_uncurried \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
      by (metis comp_associative f1 id_left_unit2 square1)
    show "(mult_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor =
    id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c mult_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
      using comp_associative square2 by auto
  qed
  then show ?thesis
    using assms comp_associative mult_apply1_left mult_apply1right mult_respects_zero_right zero_type by auto
qed

lemma s0b_type:
  "successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
  using comp_type successor_type zero_betaN_type by blast

lemma s0b_mult_type:
 "\<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , mult_curried\<rangle>: \<nat>\<^sub>c \<rightarrow> (\<nat>\<^sub>c \<times>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>))"
  by (simp add: cfunc_prod_type mult_curried_type s0b_type)

lemma s0b_id_type:
"\<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , id\<^sub>c \<nat>\<^sub>c\<rangle>: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c\<nat>\<^sub>c"
  by (simp add: cfunc_prod_type id_type s0b_type)

lemma mult_s0b_id_type:
"mult_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , id\<^sub>c \<nat>\<^sub>c\<rangle>: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
  using mult_uncurried_type s0b_id_type by auto

lemma s0_is_left_id:
  assumes "m\<in>\<^sub>c  \<nat>\<^sub>c"
  shows  "(successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> m   = m"
proof - 
  have triangle: "(mult_uncurried \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> ,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero = zero"
    using comp_associative mult_apply1right mult_respects_zero_right successor_type zero_type by auto
  have square: "(mult_uncurried \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> ,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor = 
          successor \<circ>\<^sub>c (mult_uncurried \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> ,id\<^sub>c \<nat>\<^sub>c\<rangle>)"
  proof - 
   have "(mult_uncurried \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> ,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor = 
          mult_uncurried \<circ>\<^sub>c  (\<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> ,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c successor)"
      by (simp add: comp_associative)
   also have "... =    mult_uncurried \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor , id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor\<rangle>"
      using  cfunc_prod_comp
      by (smt comp_associative id_type s0b_type successor_type)
   also have "... =  mult_uncurried \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , successor\<rangle>"
      using id_left_unit2 successor_type terminal_func_comp by force
   also have "... = (eval_func  \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult_curried) \<circ>\<^sub>c\<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , successor\<rangle>"
     by (simp add: comp_associative mult_uncurried_def)
   also have "... =  (eval_func  \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult_curried) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , id\<^sub>c \<nat>\<^sub>c\<rangle>"
     by (smt cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2 id_type s0b_type successor_type)
   also have "... =  (eval_func  \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult_curried \<circ>\<^sub>csuccessor))  \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , id\<^sub>c \<nat>\<^sub>c\<rangle>"
     using comp_associative identity_distributes_across_composition mult_curried_type successor_type by auto
   also have "... =  (eval_func  \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add_uncurried  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c mult_curried )  \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , id\<^sub>c \<nat>\<^sub>c\<rangle>"
     using mult_curried_comp_succ_eq by auto
   also have "... =  (eval_func  \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add_uncurried  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp> )  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult_curried) \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , id\<^sub>c \<nat>\<^sub>c\<rangle>"
     using comp_associative f_mult_type identity_distributes_across_composition mult_curried_property by auto
   also have "... =  (add_uncurried  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult_curried) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , id\<^sub>c \<nat>\<^sub>c\<rangle>"
     using comp_associative f_mult_flat_type transpose_func_def by auto
   also have "... = (add_uncurried  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>) \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , mult_curried\<rangle>"
     by (smt cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2 id_type mult_curried_property s0b_type)
   also have "... =  add_uncurried  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle> \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , mult_curried\<rangle>"
     by (simp add: comp_associative)
   also have "... = add_uncurried  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>))\<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , mult_curried\<rangle>,(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , mult_curried\<rangle>\<rangle>"
    using  cfunc_prod_comp eval_func_type left_cart_proj_type s0b_mult_type by fastforce 
   also have "... = add_uncurried  \<circ>\<^sub>c \<langle> successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> ,(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , mult_curried\<rangle>\<rangle>"
    using left_cart_proj_cfunc_prod mult_curried_property s0b_type by auto
   also have "... = add_uncurried  \<circ>\<^sub>c \<langle> successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> ,(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c  \<langle>id\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , mult_curried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<rangle>\<rangle>"
      using id_left_unit2 id_right_unit2 mult_curried_property s0b_type by auto
  also have "... =  add_uncurried  \<circ>\<^sub>c \<langle> successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> ,(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult_curried) \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>"
    by (smt cfunc_cross_prod_comp_cfunc_prod id_type mult_curried_type s0b_type)
  also have "... =  add_uncurried  \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , mult_uncurried \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>"
    by (simp add: comp_associative mult_uncurried_def)
  also have "... = successor \<circ>\<^sub>c (mult_uncurried \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> ,id\<^sub>c \<nat>\<^sub>c\<rangle>)"
    using add_uncurried_commutes_succ add_uncurried_respects_succ_right add_uncurried_respects_zero_on_left mult_s0b_id_type zero_betaN_type by auto
  then show ?thesis using calculation by auto
qed



have id3: "mult_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id\<^sub>c \<nat>\<^sub>c\<rangle> = id\<^sub>c \<nat>\<^sub>c"
proof(rule natural_number_object_func_unique[where f="successor", where X="\<nat>\<^sub>c"])
  show "mult_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by (simp add: mult_s0b_id_type)
  show "id\<^sub>c \<nat>\<^sub>c : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by (simp add: id_type)
  show "successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by (simp add: successor_type)
  show "(mult_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero =
    id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
    using id_left_unit2 triangle zero_type by auto
  show "(mult_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor =
    successor \<circ>\<^sub>c mult_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
    using square by blast
  show "id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor = successor \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c"
    using id_left_unit2 id_right_unit2 successor_type by auto
qed

  show ?thesis
    using assms comp_associative id3 id_left_unit2 mult_apply1right successor_type zero_type by auto
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
  have multp1p1p2_type: "mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>: ((\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c) \<rightarrow>\<nat>\<^sub>c"
    using comp_type mult_uncurried_type p1p1p2_type by blast
  have multp2p1p2_type: "mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>: ((\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c) \<rightarrow> \<nat>\<^sub>c"
    using comp_type mult_uncurried_type p2p1p2_type by blast



  have ab_type: "\<langle>a,b\<rangle>\<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
    by (simp add: assms(1) assms(2) cfunc_prod_type)
  have abz_type: "\<langle>\<langle>a,b\<rangle>,zero\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c"
    by (simp add: ab_type cfunc_prod_type zero_type)
  have ABC_type: "\<langle>\<langle>a,b\<rangle>,c\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c"
    by (simp add: ab_type assms(3) cfunc_prod_type)
  have succ_c_type: "successor \<circ>\<^sub>c c : one \<rightarrow> \<nat>\<^sub>c"
    using assms(3) successor_type by auto
  have ABsC_type: "\<langle>\<langle>a,b\<rangle>,successor \<circ>\<^sub>c c\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c"
    by (simp add: ab_type cfunc_prod_type succ_c_type)
  have fact0: "(add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c): ((\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c) \<rightarrow> (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)"
    by (simp add: add_uncurried_type cfunc_cross_prod_type id_type) 
  have fact1: "mult_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c): ((\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c) \<rightarrow>\<nat>\<^sub>c"
    using comp_type fact0 mult_uncurried_type by blast
  have fact1_sharp: "(mult_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>: \<nat>\<^sub>c \<rightarrow> (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)"
    by (simp add: fact1 transpose_func_def)
  have multAddId_c_type:  "(mult_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c c : one \<rightarrow>(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)"
    using assms(3) comp_type fact1_sharp by blast
  have zproj_type: "zero \<circ>\<^sub>c  (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) one): ((\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one) \<rightarrow> \<nat>\<^sub>c"
        using comp_type right_cart_proj_type zero_type by blast
  have zps_type: "(zero \<circ>\<^sub>c  (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) one))\<^sup>\<sharp>:  one \<rightarrow>  (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)"
    by (simp add: transpose_func_def zproj_type)
  have add_add_id_type: "add_uncurried \<circ>\<^sub>c (add_uncurried\<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) : ((\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c) \<rightarrow>\<nat>\<^sub>c"
    using add_uncurried_type comp_type fact0 by blast
  have add_add_id_sharp_type: "(add_uncurried \<circ>\<^sub>c (add_uncurried\<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>: \<nat>\<^sub>c \<rightarrow> (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)"
    by (simp add: add_add_id_type transpose_func_def)
  have piEval_type: "\<langle>(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)), eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<rangle>:
            (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>) \<rightarrow>  ((\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c)"
    by (simp add: cfunc_prod_type eval_func_type left_cart_proj_type)
  have addAddIdPiEval_type: "(add_uncurried \<circ>\<^sub>c (add_uncurried\<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c 
\<langle>(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)), eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<rangle>) : (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>) \<rightarrow> \<nat>\<^sub>c"
    using add_uncurried_type comp_type fact0 piEval_type by blast
  have addAddIdPiEvalSharp_type: 
"(add_uncurried \<circ>\<^sub>c (add_uncurried\<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c 
\<langle>(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)), eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>:
(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>) \<rightarrow>  (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)"
    by (simp add: addAddIdPiEval_type transpose_func_def)
  have veryLongType: " \<langle>\<langle>a,b\<rangle>, (mult_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c c\<rangle>: one  \<rightarrow> (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)"
    by (simp add: ab_type cfunc_prod_type multAddId_c_type) 
  have multAddIdABC_type: "(mult_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle> : one \<rightarrow>\<nat>\<^sub>c"
    using ABC_type fact1 by auto
  have addP0_type: "add_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>) : (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>) \<rightarrow> \<nat>\<^sub>c"
    using add_uncurried_type comp_type left_cart_proj_type by blast
  have evalu_type: "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)) :  (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)\<rightarrow>\<nat>\<^sub>c"
    using eval_func_type by auto


 (*Top of page 16*)
  have fact2a: "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c
    (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
    (mult_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c zero)) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>  = zero"
    proof - 
      have "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c
    (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
    (mult_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c zero)) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>  =(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c
    (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
(mult_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>"
        using comp_associative by auto 
        also have "... = 
  (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c
    (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
(mult_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> ) \<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero) \<circ>\<^sub>c 
\<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>"
      using identity_distributes_across_composition comp_associative fact1_sharp zero_type by auto
    also have "... = (mult_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero) \<circ>\<^sub>c 
\<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>"
      using comp_associative fact1 transpose_func_def by presburger
     also have "... = (mult_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>a,b\<rangle>,zero \<circ>\<^sub>c id\<^sub>c one\<rangle>"
       by (smt ab_type cfunc_cross_prod_comp_cfunc_prod id_type zero_type)
     also have "... = (mult_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,zero\<rangle>"
       using ab_type id_left_unit2 id_right_unit2 zero_type by auto
     also have "... = mult_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,zero\<rangle>"
       by (simp add: comp_associative)
     also have "... = mult_uncurried \<circ>\<^sub>c \<langle>add_uncurried \<circ>\<^sub>c \<langle>a,b\<rangle>,  zero\<rangle>"
       by (smt ab_type add_uncurried_type cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_type zero_type)
     also have "... = zero"
       using ab_type add_uncurried_type mult_def mult_respects_zero_right by force
     then show ?thesis using calculation by auto
   qed

(*"Similarly...." on page 16*)

   have left_type: 
"mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
 (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>  :((\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c) \<rightarrow> \<nat>\<^sub>c"
     by (meson cfunc_prod_type comp_type left_cart_proj_type mult_uncurried_type right_cart_proj_type)

   have right_type:
"mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle> :((\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c) \<rightarrow> \<nat>\<^sub>c"
     by (meson cfunc_prod_type comp_type left_cart_proj_type mult_uncurried_type right_cart_proj_type)


   have long_type:  
"add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
 (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle> :((\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c) \<rightarrow>\<nat>\<^sub>c"
     by (meson add_uncurried_type cfunc_prod_type comp_type left_type right_type)

   have long_sharp_type: "
(add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
 (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup> "
     using long_type transpose_func_def by blast

   have long_sharp_c_type: "(add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
 (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c c : one \<rightarrow>\<nat>\<^sub>c \<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup> "
     using assms(3) comp_type long_sharp_type by blast

   have very_long_type: "
 \<langle>
\<langle>a,b\<rangle>,
(add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
c\<rangle> : one \<rightarrow>  (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c (\<nat>\<^sub>c \<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)"
     using ab_type assms(3) cfunc_prod_type long_sharp_type by auto




   have fact3a: "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c 
            (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(
            add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero))
             \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle> = zero"
   proof-
     have "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c 
            (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(
            add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero))
             \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>
             = ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c 
            (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(
            add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> )) \<circ>\<^sub>c
            (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero) 
             \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>"
    using comp_associative identity_distributes_across_composition long_sharp_type zero_type by auto
  also have "... = 
          (add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>) \<circ>\<^sub>c
            (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero) 
             \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>"
    using long_type transpose_func_def by auto
  also have "... = (add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>) \<circ>\<^sub>c
          \<langle>\<langle>a,b\<rangle>,zero\<rangle>"
    by (smt ab_type cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2 id_type zero_type)
  also have "... =  add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c\<langle>\<langle>a,b\<rangle>,zero\<rangle>, mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<circ>\<^sub>c\<langle>\<langle>a,b\<rangle>,zero\<rangle> \<rangle>"
    by (smt abz_type cfunc_prod_comp comp_associative left_type right_type)
  also have "... = add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<circ>\<^sub>c\<langle>\<langle>a,b\<rangle>,zero\<rangle>, 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<circ>\<^sub>c\<langle>\<langle>a,b\<rangle>,zero\<rangle>\<rangle> , mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<circ>\<^sub>c\<langle>\<langle>a,b\<rangle>,zero\<rangle>,(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<circ>\<^sub>c\<langle>\<langle>a,b\<rangle>,zero\<rangle>\<rangle> \<rangle>"
    by (smt abz_type cfunc_prod_comp comp_associative p1p1_type p2p1_type right_cart_proj_type)
  also have "... = add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c\<langle>a,b\<rangle>, 
            zero\<rangle> , mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
           \<langle>a,b\<rangle>, zero\<rangle> \<rangle>"
    using ab_type left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod zero_type by auto
  also have "... = add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>a,zero\<rangle> , mult_uncurried \<circ>\<^sub>c \<langle>b,zero\<rangle>\<rangle>"
    using assms(1) assms(2) left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod by auto
  also have "... = zero"
    using add_def add_respects_zero_on_right assms(1) assms(2) mult_def mult_respects_zero_right zero_type by auto
   then show ?thesis using calculation by auto
 qed


(*Now we show the first function makes the square commute.*)

   have fact4a: "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c 
            (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(mult_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c successor))
\<circ>\<^sub>c   \<langle>\<langle>a,b\<rangle>,c\<rangle> = (a +\<^sub>\<nat> b) \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c c)"
   proof - 
     have "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c 
            (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(mult_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c successor))
\<circ>\<^sub>c   \<langle>\<langle>a,b\<rangle>,c\<rangle> =
((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c 
            (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(mult_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>) \<circ>\<^sub>c 
            (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f     successor)
)\<circ>\<^sub>c   \<langle>\<langle>a,b\<rangle>,c\<rangle>"
       using fact1_sharp identity_distributes_across_composition successor_type by auto
     also have "... = ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c 
            (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(mult_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)  
)\<circ>\<^sub>c   \<langle>\<langle>a,b\<rangle>,successor \<circ>\<^sub>c c\<rangle>"
       by (smt ab_type assms(3) cfunc_cross_prod_comp_cfunc_prod comp_associative id_left_unit2 id_type successor_type)
     also have "... = mult_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c   \<langle>\<langle>a,b\<rangle>,successor \<circ>\<^sub>c c\<rangle>"
       using fact1 transpose_func_def comp_associative by auto
     also have "... = mult_uncurried \<circ>\<^sub>c \<langle>add_uncurried \<circ>\<^sub>c \<langle>a,b\<rangle>, id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor \<circ>\<^sub>c c\<rangle>"
       using ab_type add_uncurried_type cfunc_cross_prod_comp_cfunc_prod id_type succ_c_type by fastforce
     also have "... =  (a +\<^sub>\<nat> b) \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c c)"
       using add_def id_left_unit2 mult_def succ_c_type by auto
then show ?thesis using calculation by auto
qed

(*Bottom of page 16 *)
  have fact5a: 
"(
(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c 
            (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c
  \<langle>(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)), eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
  (mult_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)
) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle> = (a +\<^sub>\<nat> b) \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c c)"
  proof-  
    have "(
(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c 
            (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f (add_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f (id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c
  \<langle>(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)), eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
  (mult_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)
) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle> = 
(
(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c 
            (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f (id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c
  \<langle>(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)), eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>)\<circ>\<^sub>c
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>f (mult_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)
) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
      using addAddIdPiEvalSharp_type fact1_sharp identity_distributes_across_composition by auto
    also have "... = 
(
(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c 
            (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f (id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c
  \<langle>(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)), eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>)
 )\<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c  \<langle>a,b\<rangle>, (mult_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c c\<rangle>"
      by (smt ab_type assms(3) cfunc_cross_prod_comp_cfunc_prod comp_associative fact1_sharp id_type)
    also have "... = (add_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f (id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c
  \<langle>(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)), eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<rangle>) 
\<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c  \<langle>a,b\<rangle>, (mult_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c c\<rangle>"
      using addAddIdPiEval_type transpose_func_def by auto
    also have "... = (add_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f (id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c
  \<langle>(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)), eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<rangle>) 
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, (mult_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c c\<rangle>"
      using ab_type id_left_unit2 by auto
    also have "... = add_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f (id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c 
 \<langle>(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>))\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, (mult_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c c\<rangle>,
 eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, (mult_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c c\<rangle>\<rangle>"
      using cfunc_prod_comp
      by (smt comp_associative eval_func_type left_cart_proj_type veryLongType)
    also have "... = add_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f (id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c 
\<langle> \<langle>a,b\<rangle>,  eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, (mult_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c c\<rangle>\<rangle>"
      using ab_type left_cart_proj_cfunc_prod multAddId_c_type by auto
    also have "... = add_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f (id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c 
\<langle> \<langle>a,b\<rangle>,  eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>a,b\<rangle>, (mult_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c c\<rangle>\<rangle>"
      using ab_type id_left_unit2 by auto
    also have "... = add_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f (id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c 
\<langle>\<langle>a,b\<rangle>, eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>\<rangle>"
      using ab_type assms(3) cfunc_cross_prod_comp_cfunc_prod fact1_sharp id_type by fastforce
    also have "... = add_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f (id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c 
\<langle>\<langle>a,b\<rangle>, (mult_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>\<rangle>"
      using comp_associative fact1 transpose_func_def by auto
    also have "... = add_uncurried \<circ>\<^sub>c \<langle> add_uncurried \<circ>\<^sub>c  \<langle>a,b\<rangle>,  
(id\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (mult_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>\<rangle>"
      using ab_type add_uncurried_type cfunc_cross_prod_comp_cfunc_prod id_type multAddIdABC_type by fastforce
    also have "... =  add_uncurried \<circ>\<^sub>c \<langle> add_uncurried \<circ>\<^sub>c  \<langle>a,b\<rangle>,
mult_uncurried \<circ>\<^sub>c \<langle>add_uncurried \<circ>\<^sub>c  \<langle>a,b\<rangle>, id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c c\<rangle>\<rangle>"
      by (smt ab_type add_uncurried_type assms(3) cfunc_cross_prod_comp_cfunc_prod comp_associative id_left_unit2 id_type multAddIdABC_type)
    also have "... = (a +\<^sub>\<nat> b)  +\<^sub>\<nat>  ((a +\<^sub>\<nat> b) \<cdot>\<^sub>\<nat> c)"
      using add_def assms(3) id_left_unit2 mult_def by auto
    also have "... = (a +\<^sub>\<nat> b) \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c c)"
      using ab_type add_def add_uncurried_type assms(3) mult_respects_succ_right by auto
then show ?thesis using calculation by auto
qed

(*Top of page 17*)
  have fact6a:  "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c 
            (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(
            add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor))
             \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle> = (a \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c c)) +\<^sub>\<nat> (b \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c c))"
  proof - 
    have "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c 
            (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(
            add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor))
             \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle> =
((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c 
            (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(
            add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> )) 
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,successor \<circ>\<^sub>c c\<rangle>"
      by (smt ab_type assms(3) cfunc_cross_prod_comp_cfunc_prod comp_associative id_left_unit2 id_type identity_distributes_across_composition long_sharp_type successor_type)
    also have  "... = (
            add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,successor \<circ>\<^sub>c c\<rangle>"
      using long_type transpose_func_def by auto
    also have "... = add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle> \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,successor \<circ>\<^sub>c c\<rangle>"
      by (simp add: comp_associative)
    also have "... = add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,successor \<circ>\<^sub>c c\<rangle>  , mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,successor \<circ>\<^sub>c c\<rangle>   \<rangle> "
      using ABsC_type cfunc_prod_comp comp_associative multp1p1p2_type right_type by auto
    also have "... = add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,successor \<circ>\<^sub>c c\<rangle> , 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,successor \<circ>\<^sub>c c\<rangle> \<rangle>  , mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,successor \<circ>\<^sub>c c\<rangle> ,(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,successor \<circ>\<^sub>c c\<rangle> \<rangle>   \<rangle> "
      by (smt ABsC_type cfunc_prod_comp comp_associative p1p1_type p2p1_type right_cart_proj_type)
    also have "... = add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c  \<langle>a,b\<rangle> , 
            (successor \<circ>\<^sub>c c) \<rangle>  , mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
             \<langle>a,b\<rangle> , successor \<circ>\<^sub>c c \<rangle>   \<rangle> "
      using ab_type left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod succ_c_type by auto
    also have "... = add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>a , (successor \<circ>\<^sub>c c) \<rangle>  , mult_uncurried \<circ>\<^sub>c \<langle>b,successor \<circ>\<^sub>c c  \<rangle> \<rangle> "
      using assms(1) assms(2) left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod by auto
    also have "... =  (a \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c c)) +\<^sub>\<nat> (b \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c c))"
      by (simp add: add_def mult_def)
then show ?thesis using calculation by auto
qed

(*And... *)

have fact7a:  "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c 
            (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(add_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) 
 \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>), 
(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<rangle>)\<^sup>\<sharp>  \<circ>\<^sub>c (add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>))
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle> = (a \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c c)) +\<^sub>\<nat> (b \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c c))"


proof - 
  have "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c 
            (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(add_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) 
 \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>), 
(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<rangle>)\<^sup>\<sharp>  \<circ>\<^sub>c (add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>))
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle> =
((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c 
            (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(add_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) 
 \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>), 
(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<rangle>)\<^sup>\<sharp>  ) \<circ>\<^sub>c  
 (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle> "
    using addAddIdPiEvalSharp_type identity_distributes_across_composition long_sharp_type by auto
  also have "... = ((add_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) 
 \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>), 
(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<rangle>) \<circ>\<^sub>c
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle> "
    using addAddIdPiEval_type comp_associative transpose_func_def by auto
  also have "... =  (add_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) 
 \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>), 
(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<rangle>) \<circ>\<^sub>c
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle> "
    using comp_associative by auto
  also have "... = (add_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) 
 \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>), 
(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<rangle>)  \<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>a,b\<rangle>,
(add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
c\<rangle> "
    using ab_type assms(3) cfunc_cross_prod_comp_cfunc_prod id_type long_sharp_type by fastforce
  also have "... =  (add_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) 
 \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>), 
(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<rangle>)  \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,
(add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
c\<rangle> "
    using ab_type id_left_unit2 by auto
  also have "... =  add_uncurried \<circ>\<^sub>c (
(add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) 
 \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>), 
(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<rangle> ) \<circ>\<^sub>c \<langle>
\<langle>a,b\<rangle>,
(add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
c\<rangle> "
    by (simp add: comp_associative)
  also have "... = 
 add_uncurried \<circ>\<^sub>c \<langle>
add_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>),  id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))  \<rangle>  
 \<circ>\<^sub>c \<langle>
\<langle>a,b\<rangle>,
(add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
c\<rangle> "
    by (smt add_uncurried_type cfunc_cross_prod_comp_cfunc_prod eval_func_type id_type left_cart_proj_type)
  also have "... = 
 add_uncurried \<circ>\<^sub>c \<langle>
add_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>),  (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))  \<rangle>  
 \<circ>\<^sub>c \<langle>
\<langle>a,b\<rangle>,
(add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
c\<rangle> "
    by (metis eval_func_type id_left_unit2)
  also have "... =  
add_uncurried \<circ>\<^sub>c \<langle>
add_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)
 \<circ>\<^sub>c \<langle>
\<langle>a,b\<rangle>,
(add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
c\<rangle>
,  (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)) 
 \<circ>\<^sub>c \<langle>
\<langle>a,b\<rangle>,
(add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
c\<rangle>
 \<rangle>"
    using cfunc_prod_comp addP0_type comp_associative evalu_type very_long_type by auto
  also have "... =add_uncurried \<circ>\<^sub>c \<langle>
add_uncurried \<circ>\<^sub>c \<langle>a,b\<rangle>
,  (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)) 
 \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,
(add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult_uncurried \<circ>\<^sub>c 
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
c\<rangle>
 \<rangle>" 
    using left_cart_proj_cfunc_prod ab_type long_sharp_c_type by auto
  also have "... = add_uncurried \<circ>\<^sub>c \<langle>
add_uncurried \<circ>\<^sub>c \<langle>a,b\<rangle>
,  (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)) 
 \<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>a,b\<rangle>,
(add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult_uncurried \<circ>\<^sub>c 
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
c\<rangle>
 \<rangle>"
    using ab_type id_left_unit2 by auto
  also have "... = 
add_uncurried \<circ>\<^sub>c \<langle>
add_uncurried \<circ>\<^sub>c \<langle>a,b\<rangle>
,  (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)) 
 \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult_uncurried \<circ>\<^sub>c 
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle> \<langle>a,b\<rangle>,c\<rangle> \<rangle>"
    using ab_type assms(3) cfunc_cross_prod_comp_cfunc_prod id_type long_sharp_type by fastforce
  also have "... = 
add_uncurried \<circ>\<^sub>c \<langle>
add_uncurried \<circ>\<^sub>c \<langle>a,b\<rangle>
,  (add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult_uncurried \<circ>\<^sub>c 
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>) \<circ>\<^sub>c \<langle> \<langle>a,b\<rangle>,c\<rangle> \<rangle>"
    using comp_associative long_type transpose_func_def by presburger
  also have "... = add_uncurried \<circ>\<^sub>c \<langle>
add_uncurried \<circ>\<^sub>c \<langle>a,b\<rangle>
,  add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>

, mult_uncurried \<circ>\<^sub>c
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle> \<circ>\<^sub>c \<langle> \<langle>a,b\<rangle>,c\<rangle> \<rangle>"
    by (simp add: comp_associative)
 also have "... = add_uncurried \<circ>\<^sub>c \<langle>
add_uncurried \<circ>\<^sub>c \<langle>a,b\<rangle>
,  add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c \<langle> \<langle>a,b\<rangle>,c\<rangle>

, mult_uncurried \<circ>\<^sub>c
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>   \<circ>\<^sub>c \<langle> \<langle>a,b\<rangle>,c\<rangle> \<rangle>  \<rangle>"
   using ABC_type cfunc_prod_comp comp_associative multp1p1p2_type right_type by auto
  also have "... =add_uncurried \<circ>\<^sub>c \<langle>
add_uncurried \<circ>\<^sub>c \<langle>a,b\<rangle>
,  add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c \<langle> \<langle>a,b\<rangle>,c\<rangle>

, mult_uncurried \<circ>\<^sub>c
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle> \<langle>a,b\<rangle>,c\<rangle> ,
(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle> \<langle>a,b\<rangle>,c\<rangle>\<rangle>   \<rangle>  \<rangle>"
    by (smt ABC_type cfunc_prod_comp comp_associative p2p1_type right_cart_proj_type)
  also have "... = 
add_uncurried \<circ>\<^sub>c \<langle>
add_uncurried \<circ>\<^sub>c \<langle>a,b\<rangle>
,  add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle> \<langle>a,b\<rangle>,c\<rangle>, 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle> \<langle>a,b\<rangle>,c\<rangle>\<rangle>

, mult_uncurried \<circ>\<^sub>c
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            \<langle>a,b\<rangle>,
c\<rangle>   \<rangle>  \<rangle>"
    by (smt ABC_type ab_type assms(3) cfunc_prod_comp comp_associative left_cart_proj_cfunc_prod p1p1_type right_cart_proj_cfunc_prod right_cart_proj_type)
  also have "... = 
add_uncurried \<circ>\<^sub>c \<langle>
add_uncurried \<circ>\<^sub>c \<langle>a,b\<rangle>
,  add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c 
\<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c   \<langle>a,b\<rangle>, c\<rangle>,
 mult_uncurried \<circ>\<^sub>c\<langle>b,c\<rangle>\<rangle>\<rangle>"
    using ab_type assms(1) assms(2) assms(3) left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod by auto
  also have "... =
add_uncurried \<circ>\<^sub>c \<langle>
add_uncurried \<circ>\<^sub>c \<langle>a,b\<rangle>
,  add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c \<langle>a, c\<rangle>, mult_uncurried \<circ>\<^sub>c\<langle>b,c\<rangle>\<rangle>\<rangle>"
    using assms(1) assms(2) left_cart_proj_cfunc_prod by auto
  also have "... = (a +\<^sub>\<nat> b) +\<^sub>\<nat> (a \<cdot>\<^sub>\<nat> c +\<^sub>\<nat> b \<cdot>\<^sub>\<nat> c)"
    by (simp add: add_def mult_def)
  also have "... = a +\<^sub>\<nat> (b +\<^sub>\<nat> (a \<cdot>\<^sub>\<nat> c +\<^sub>\<nat> b \<cdot>\<^sub>\<nat> c))"
    oops
(*
    also have "... = a +\<^sub>\<nat> ((b +\<^sub>\<nat> a \<cdot>\<^sub>\<nat> c) +\<^sub>\<nat> b \<cdot>\<^sub>\<nat> c)"

 also have "... = a +\<^sub>\<nat> ((a \<cdot>\<^sub>\<nat> c  +\<^sub>\<nat> b) +\<^sub>\<nat> b \<cdot>\<^sub>\<nat> c)"
 also have "... = a +\<^sub>\<nat> (a \<cdot>\<^sub>\<nat> c  +\<^sub>\<nat> (b +\<^sub>\<nat> b \<cdot>\<^sub>\<nat> c))"
   also have "... = (a +\<^sub>\<nat> a \<cdot>\<^sub>\<nat> c)  +\<^sub>\<nat> (b +\<^sub>\<nat> b \<cdot>\<^sub>\<nat> c)"
     also have "... = (a \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c c)) +\<^sub>\<nat> (b \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c c))"
       
*)

lemma mult_commutative:
  assumes "a \<in>\<^sub>c  \<nat>\<^sub>c"  "b\<in>\<^sub>c  \<nat>\<^sub>c" 
  shows "a \<cdot>\<^sub>\<nat> b = b \<cdot>\<^sub>\<nat> a"

proof - 
  have a0_type: "\<langle>a,zero\<rangle>: one \<rightarrow>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)"
    by (simp add: assms(1) cfunc_prod_type zero_type)
  have a1_type: "\<langle>a,id\<^sub>c one\<rangle>: one \<rightarrow>(\<nat>\<^sub>c\<times>\<^sub>c one)"
    by (simp add: assms(1) cfunc_prod_type id_type)
  have ab_typ: "\<langle>a,b\<rangle>: one \<rightarrow>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)"
    by (simp add: assms(1) assms(2) cfunc_prod_type)
  have p1p0_type:  "\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>: (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<rightarrow>  (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)"
    by (simp add: cfunc_prod_type left_cart_proj_type right_cart_proj_type)
  have multp1p0_tye: "mult_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>: (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<rightarrow> \<nat>\<^sub>c"
    using comp_type mult_uncurried_type p1p0_type by blast 
  have multp1p0sharp_type: "(mult_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
    by (simp add: multp1p0_tye transpose_func_def)
  have  multp1p0sharp0_type: "(mult_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>\<circ>\<^sub>c zero: one \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
    using multp1p0sharp_type zero_type by auto
  have  pi0eval_type: "\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>), eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>: \<nat>\<^sub>c\<times>\<^sub>c(\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<rightarrow> (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)"
    by (simp add: cfunc_prod_type eval_func_type left_cart_proj_type)
  have addpi0eval_type: "add_uncurried \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>), eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>: \<nat>\<^sub>c\<times>\<^sub>c(\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<rightarrow> \<nat>\<^sub>c"
    by (simp add: f_mult_flat_type)
  have addpi0evalsharp_type:  "(add_uncurried \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>), eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>: (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<rightarrow> (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)"
    by (simp add: f_mult_type)
  have long_type: "(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>a,b\<rangle>: one \<rightarrow> \<nat>\<^sub>c\<times>\<^sub>c(\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)"
    using ab_typ cfunc_cross_prod_type id_type multp1p0sharp_type by auto


  have f1: "(eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult_uncurried \<circ>\<^sub>c
 \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>\<circ>\<^sub>c zero))\<circ>\<^sub>c \<langle>a,id\<^sub>c one\<rangle> = zero"
  proof - 
    have "(eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult_uncurried \<circ>\<^sub>c
 \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>\<circ>\<^sub>c zero))\<circ>\<^sub>c \<langle>a,id\<^sub>c one\<rangle> = 
eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult_uncurried \<circ>\<^sub>c
 \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>\<circ>\<^sub>c zero)\<circ>\<^sub>c \<langle>a,id\<^sub>c one\<rangle>"
      by (simp add: comp_associative)
    also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult_uncurried \<circ>\<^sub>c
 \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero)\<circ>\<^sub>c \<langle>a,id\<^sub>c one\<rangle>"
      using comp_associative identity_distributes_across_composition multp1p0sharp_type zero_type by auto
    also have "... = (mult_uncurried \<circ>\<^sub>c
 \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero)\<circ>\<^sub>c \<langle>a,id\<^sub>c one\<rangle>"
      using comp_associative flat_cancels_sharp inv_transpose_func_def2 multp1p0_tye multp1p0sharp_type by fastforce
    also have "... = (mult_uncurried \<circ>\<^sub>c
 \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c\<circ>\<^sub>c  a, zero \<circ>\<^sub>c id\<^sub>c one\<rangle>"
      by (smt assms(1) cfunc_cross_prod_comp_cfunc_prod id_type zero_type)
    also have "... =  mult_uncurried \<circ>\<^sub>c
 \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>a, zero\<rangle>"
      using assms(1) comp_associative id_left_unit2 id_right_unit2 zero_type by auto
    also have "... =  mult_uncurried \<circ>\<^sub>c
 \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a, zero\<rangle> ,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a, zero\<rangle> \<rangle>"
      using ETCS_HOL.swap_def assms(1) left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod swap_ap zero_type by auto
    also have "... =  mult_uncurried \<circ>\<^sub>c \<langle>zero , a\<rangle>"
      using assms(1) left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod zero_type by auto
    also have "... = zero"
      using assms(1) mult_def mult_respects_zero_left by auto
then show ?thesis using calculation by auto
qed
(*
  have f2: "(eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ((add_uncurried \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>), eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>\<circ>\<^sub>c
(mult_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>)))\<circ>\<^sub>c \<langle>a,b\<rangle> = (successor \<circ>\<^sub>c a)  \<cdot>\<^sub>\<nat> b"
  proof - 
    have "(eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ((add_uncurried \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>), eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>\<circ>\<^sub>c
(mult_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>)))\<circ>\<^sub>c \<langle>a,b\<rangle> = 
  eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ((add_uncurried \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>), eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>\<circ>\<^sub>c
(mult_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>))\<circ>\<^sub>c \<langle>a,b\<rangle>"
      using comp_associative by auto
    also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ((add_uncurried \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>), eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>))
\<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>a,b\<rangle>"
      using comp_associative f_mult_type identity_distributes_across_composition multp1p0sharp_type by auto
    also have "... = add_uncurried \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>), eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>
\<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>a,b\<rangle>"
      using comp_associative f_mult_flat_type f_mult_type flat_cancels_sharp inv_transpose_func_def2 by fastforce
    also have "... =  add_uncurried \<circ>\<^sub>c
 \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>a,b\<rangle> ,
            eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>a,b\<rangle> \<rangle>"
      using cfunc_prod_comp eval_func_type left_cart_proj_type long_type by fastforce
    also have "... = add_uncurried \<circ>\<^sub>c
 \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>)  ,
            eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<rangle> \<circ>\<^sub>c \<langle>a,b\<rangle>"
      by (smt ab_typ cfunc_prod_comp comp_associative id_left_unit2 id_type left_cart_proj_cfunc_cross_prod left_cart_proj_type multp1p0_tye transpose_func_def)
    also have "... =  add_uncurried \<circ>\<^sub>c
 \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c , 
    eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>)\<rangle>  \<circ>\<^sub>c \<langle>a,b\<rangle> "
    proof -
      have "left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> = id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c"
        by (simp add: id_type left_cart_proj_cfunc_cross_prod multp1p0sharp_type)
      then show ?thesis
        by presburger
    qed
    also have "... = add_uncurried \<circ>\<^sub>c
 \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c , 
    mult_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>  \<circ>\<^sub>c \<langle>a,b\<rangle> "
      using multp1p0_tye transpose_func_def by auto
    also have "... =  add_uncurried \<circ>\<^sub>c
 \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>a,b\<rangle>, 
    mult_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>a,b\<rangle> \<rangle>  "
      by (smt ab_typ cfunc_prod_comp comp_associative id_left_unit2 left_cart_proj_type multp1p0_tye)
    also have "... =  add_uncurried \<circ>\<^sub>c\<langle>a,  mult_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a,b\<rangle>,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a,b\<rangle>\<rangle>  \<rangle>  "
      using ETCS_HOL.swap_def assms(1) assms(2) id_left_unit2 left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod swap_ap by auto
    also have "... =  add_uncurried \<circ>\<^sub>c\<langle>a,  mult_uncurried \<circ>\<^sub>c \<langle>b,a\<rangle>  \<rangle>  "
      using assms(1) assms(2) left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod by auto
    also have "... = a +\<^sub>\<nat> (b \<cdot>\<^sub>\<nat> a)"
      by (simp add: add_def mult_def)
    also have "... = (successor \<circ>\<^sub>c a) \<cdot>\<^sub>\<nat> b"
      oops (*need respects successor to the left, and for that we need "left" distributivity.*)
 
*)   

     
      have f3: "(eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ((mult_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>\<circ>\<^sub>c zero)))
\<circ>\<^sub>c \<langle>a, id\<^sub>c one\<rangle> = zero"
      proof - 
        have "(eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ((mult_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>\<circ>\<^sub>c zero)))
\<circ>\<^sub>c \<langle>a, id\<^sub>c one\<rangle> = 
    eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ((mult_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>\<circ>\<^sub>c zero))
    \<circ>\<^sub>c \<langle>a, id\<^sub>c one\<rangle>"
          by (simp add: comp_associative)
        also have "... =  eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ((mult_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>))
                                          \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  zero) \<circ>\<^sub>c \<langle>a, id\<^sub>c one\<rangle>"
          by (metis comp_associative inv_transpose_func_def2 inv_transpose_of_composition multp1p0sharp0_type multp1p0sharp_type zero_type)
        also have "... = (mult_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  zero) \<circ>\<^sub>c \<langle>a, id\<^sub>c one\<rangle>"
          using comp_associative flat_cancels_sharp inv_transpose_func_def2 multp1p0_tye multp1p0sharp_type by fastforce
        also have "... = mult_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  zero) \<circ>\<^sub>c \<langle>a, id\<^sub>c one\<rangle>"
          by (simp add: comp_associative)
        also have "... = mult_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>  \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c a, zero \<circ>\<^sub>c id\<^sub>c one\<rangle>"
          using ETCS_HOL.swap_def assms(1) calculation f1 id_left_unit2 id_right_unit2 mult_def mult_respects_zero_left swap_ap zero_type by auto
        also have "... =  mult_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a, zero\<rangle> ,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>a, zero\<rangle> \<rangle>  "
          using assms(1) calculation f1 left_cart_proj_cfunc_prod mult_def mult_respects_zero_left right_cart_proj_cfunc_prod zero_type by auto
        also have "... =  mult_uncurried \<circ>\<^sub>c \<langle>zero ,a \<rangle>"
          using assms(1) left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod zero_type by auto
        also have "... = zero"
          using calculation f1 by auto
then show ?thesis using calculation by auto
qed

  oops

         
(*

lemma mult_associative:
  assumes "a \<in>\<^sub>c  \<nat>\<^sub>c"  "b\<in>\<^sub>c  \<nat>\<^sub>c"  "c\<in>\<^sub>c  \<nat>\<^sub>c"
  shows "a \<cdot>\<^sub>\<nat> ( b \<cdot>\<^sub>\<nat> c)   = (a \<cdot>\<^sub>\<nat> b) \<cdot>\<^sub>\<nat> c"
proof -
  have ab_type: "\<langle>a,b\<rangle> : one \<rightarrow>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)"
    by (simp add: assms(1) assms(2) cfunc_prod_type)
  have id_ab_type: "id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<circ>\<^sub>c  \<langle>a,b\<rangle>: one \<rightarrow>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)"
    using ab_type id_left_unit2 by auto
  have b0_type: "\<langle>b,zero\<rangle> : one \<rightarrow>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)"
    using assms(2) cfunc_prod_type zero_type by blast
  have abc_type: "\<langle>\<langle>a,b\<rangle>,c\<rangle>:  one \<rightarrow>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c"
    by (simp add: ab_type assms(3) cfunc_prod_type)
  have sc_type: "successor \<circ>\<^sub>c c : one \<rightarrow> \<nat>\<^sub>c"
    using assms(3) successor_type by auto
  have abz_type: "\<langle>\<langle>a,b\<rangle>,zero\<rangle>:  one \<rightarrow>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c"
    by (simp add: ab_type cfunc_prod_type zero_type)
  have abId_type: "\<langle>\<langle>a,b\<rangle>,id one\<rangle>:  one \<rightarrow>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c one"
    by (simp add: ab_type cfunc_prod_type id_type)
  have abSc_type: "\<langle>\<langle>a,b\<rangle>,successor  \<circ>\<^sub>c c\<rangle>: one \<rightarrow>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c"
    by (simp add: ab_type cfunc_prod_type sc_type)
  have bSc_type: "\<langle>b,successor  \<circ>\<^sub>c c\<rangle>: one \<rightarrow> (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)"
    by (simp add: assms(2) cfunc_prod_type sc_type)
  have multId_type: "mult_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c : (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c\<rightarrow> (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)"
    by (simp add: cfunc_cross_prod_type id_type mult_uncurried_type)
  have multab_type: "mult_uncurried \<circ>\<^sub>c \<langle>a,b\<rangle>: one \<rightarrow> \<nat>\<^sub>c"
    using ab_type comp_type mult_uncurried_type by blast
  have multmultId_type: "mult_uncurried \<circ>\<^sub>c (mult_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) : (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c\<rightarrow> \<nat>\<^sub>c"
    using comp_type multId_type mult_uncurried_type by blast
  have multIdmult_type: "(mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried)): \<nat>\<^sub>c\<times>\<^sub>c( \<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<rightarrow> \<nat>\<^sub>c"
    by (smt comp_type flat_type inv_transpose_func_def2 inv_transpose_of_composition mult_curried_type mult_uncurried_def)
  have multmultIdSharp_type: "(mult_uncurried \<circ>\<^sub>c (mult_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> :  \<nat>\<^sub>c\<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
    by (simp add: multmultId_type transpose_func_def)
  have mmIdSharp0_type: "(mult_uncurried \<circ>\<^sub>c (mult_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>\<circ>\<^sub>c zero : one \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
    using comp_type multmultIdSharp_type zero_type by blast
  have mmIdSharpS_type: "(mult_uncurried \<circ>\<^sub>c (mult_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>\<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
    using multmultIdSharp_type successor_type by auto
  have p0rho0_type: "(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) : (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c\<rightarrow> \<nat>\<^sub>c"
    using comp_type left_cart_proj_type by blast
  have p1rho0_type: "(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) : (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c\<rightarrow> \<nat>\<^sub>c"
    using comp_type left_cart_proj_type right_cart_proj_type by blast
  have p1rho0rho1_type: "\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle> :  (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c \<rightarrow>  (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)"
    by (simp add: cfunc_prod_type p1rho0_type right_cart_proj_type)
  have p0p0p1p0p1_type: "\<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>: (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c \<rightarrow>   \<nat>\<^sub>c \<times>\<^sub>c(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)"
    by (simp add: cfunc_prod_type p0rho0_type p1rho0rho1_type)
  have multIdxMultp0p0p1p0p1_type: "mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle> : (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c \<rightarrow>\<nat>\<^sub>c"
    using comp_associative multIdmult_type p0p0p1p0p1_type by auto
  have multIdxMultp0p0p1p0p1_Sharp_type: "(mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>: \<nat>\<^sub>c\<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>"
    using multIdxMultp0p0p1p0p1_type transpose_func_def by blast
  then have multIdxMultp0p0p1p0p0_Sharp0_type: "(mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero :  one \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>"
    using comp_type zero_type by blast
  have multIdxMultp0p0p1p0p0_SharpSucc_type: "(mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor :  \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>"
    using comp_type multIdxMultp0p0p1p0p1_Sharp_type successor_type by blast
  have zbsharp_type: "(zero \<circ>\<^sub>c \<beta>\<^bsub>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>cone\<^esub>)\<^sup>\<sharp>: one \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>"
    by (simp add: transpose_func_def zero_betaN_type)
  have multsigma0_type: "mult_uncurried \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)):  ((\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>))\<rightarrow> \<nat>\<^sub>c"
    using comp_type left_cart_proj_type mult_uncurried_type by blast
  have multsigma0Eval_type: "\<langle>mult_uncurried \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<rangle> : ((\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>))\<rightarrow> (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)"
    by (simp add: cfunc_prod_type eval_func_type multsigma0_type)
  then have addMultSigma0Eval_type: "add_uncurried \<circ>\<^sub>c \<langle>mult_uncurried \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<rangle> : ((\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>))\<rightarrow> \<nat>\<^sub>c"
    using add_uncurried_type comp_type by blast
  then have addMultSigma0EvalSharp_type: "(add_uncurried \<circ>\<^sub>c \<langle>mult_uncurried \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> : (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)\<rightarrow> (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)"
    by (simp add: transpose_func_def)
  have id_multmultidsharp_type: "(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult_uncurried \<circ>\<^sub>c (mult_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)): (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
    by (meson cfunc_cross_prod_type id_type multmultIdSharp_type)
  have f1: "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult_uncurried \<circ>\<^sub>c (mult_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>\<circ>\<^sub>c zero)))\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle> = zero" 
  proof - 
    have "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult_uncurried \<circ>\<^sub>c (mult_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>\<circ>\<^sub>c zero)))\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle> = 
(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult_uncurried \<circ>\<^sub>c (mult_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>\<circ>\<^sub>c zero))\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>"
      by (simp add: comp_associative)
    also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult_uncurried \<circ>\<^sub>c (mult_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>))\<circ>\<^sub>c ((id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f zero)) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>"
      using comp_associative identity_distributes_across_composition multmultIdSharp_type zero_type by auto
    also have "... = (mult_uncurried \<circ>\<^sub>c (mult_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c   \<langle> id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>a,b\<rangle>, zero \<circ>\<^sub>c id\<^sub>c one\<rangle>"
      by (smt ab_type cfunc_cross_prod_comp_cfunc_prod comp_associative flat_cancels_sharp id_type inv_transpose_func_def2 multmultIdSharp_type multmultId_type zero_type)
    also have "... = mult_uncurried \<circ>\<^sub>c (mult_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)  \<circ>\<^sub>c   \<langle>\<langle>a,b\<rangle>, zero\<rangle>"
      using ab_type comp_associative id_left_unit2 id_right_unit2 zero_type by auto
    also have "... = mult_uncurried \<circ>\<^sub>c \<langle>mult_uncurried \<circ>\<^sub>c \<langle>a,b\<rangle>, zero\<rangle> "
      using ab_type cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_type mult_uncurried_type zero_type by fastforce
    also have "... = zero"
      using mult_def mult_respects_zero_right multab_type by auto
then show ?thesis using calculation by auto
qed


  have f2: "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero))) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle> = zero" 
  proof - 
    have "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero))) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle> = 
   (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero)) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>"
      by (simp add: comp_associative)
    also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> )) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f zero)  \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>"
      using comp_associative identity_distributes_across_composition multIdxMultp0p0p1p0p1_Sharp_type zero_type by auto
    also have "... = (mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f zero)  \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>"
      using comp_associative multIdxMultp0p0p1p0p1_type transpose_func_def by presburger
    also have "... = mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>\<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>a,b\<rangle>,zero \<circ>\<^sub>cid\<^sub>c one\<rangle>"
      by (smt ab_type cfunc_cross_prod_comp_cfunc_prod comp_associative id_type zero_type)
    also have "... = mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,zero\<rangle>"
      using ab_type id_left_unit2 id_right_unit2 zero_type by auto
    also have "... = mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,zero\<rangle>,
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,zero\<rangle>  \<rangle>"
      using abz_type cfunc_prod_comp comp_associative p0rho0_type p1rho0rho1_type by auto
   also have "... = mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,zero\<rangle>,
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,zero\<rangle>  , (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,zero\<rangle>  \<rangle>  \<rangle>"
     using \<open>mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,zero\<rangle> = mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,zero\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,zero\<rangle>\<rangle>\<close> ab_type assms(1) assms(2) associate_right_ap associate_right_def left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod zero_type by auto
   also have "... = mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c  \<langle>a,b\<rangle>,
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c  \<langle>a,b\<rangle>  ,zero  \<rangle>  \<rangle>"
     using ab_type left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod zero_type by auto
   also have "... = mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>a , \<langle>b,zero\<rangle>  \<rangle>"
     using assms(1) assms(2) left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod by auto
   also have "... = mult_uncurried \<circ>\<^sub>c  \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c a ,mult_uncurried \<circ>\<^sub>c \<langle>b,zero\<rangle>  \<rangle>"
     using assms(1) b0_type id_type mult_uncurried_type cfunc_cross_prod_comp_cfunc_prod by fastforce
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
         by (simp add: comp_associative)
       also have "... =  (zero \<circ>\<^sub>c \<beta>\<^bsub>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>cone\<^esub>) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>"
         by (metis calculation transpose_func_def zero_betaN_type)
       also have "... = zero \<circ>\<^sub>c (\<beta>\<^bsub>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>cone\<^esub> \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>)"
         by (simp add: comp_associative)
       also have "... = zero"
         using abId_type beta_N_succ_mEqs_Id1 comp_associative id_right_unit2 successor_type terminal_func_comp zero_type by auto
      then show ?thesis using calculation by auto
qed

(*Equation before "Likewise..." on page 19*)
  have f4: "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f (mult_uncurried \<circ>\<^sub>c (mult_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>\<circ>\<^sub>c successor) )
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle> = (a \<cdot>\<^sub>\<nat> b)  \<cdot>\<^sub>\<nat> (successor  \<circ>\<^sub>c c)"
  proof - 
    have "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f (mult_uncurried \<circ>\<^sub>c (mult_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>\<circ>\<^sub>c successor) )
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle> = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f (mult_uncurried \<circ>\<^sub>c (mult_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>\<circ>\<^sub>c successor) 
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
      by (simp add: comp_associative)
    also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f (mult_uncurried \<circ>\<^sub>c (mult_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f successor) 
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
      using comp_associative identity_distributes_across_composition multmultIdSharp_type successor_type by auto
    also have "... = mult_uncurried \<circ>\<^sub>c (mult_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f successor) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
      using comp_associative flat_cancels_sharp inv_transpose_func_def2 multmultIdSharp_type multmultId_type by fastforce
    also have "... = mult_uncurried \<circ>\<^sub>c (mult_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<circ>\<^sub>c  \<langle>a,b\<rangle>,successor \<circ>\<^sub>c c\<rangle>"
      using ab_type assms(3) cfunc_cross_prod_comp_cfunc_prod id_type successor_type by fastforce
    also have "... = mult_uncurried \<circ>\<^sub>c \<langle>mult_uncurried \<circ>\<^sub>c  (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<circ>\<^sub>c  \<langle>a,b\<rangle>),id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (successor \<circ>\<^sub>c c)\<rangle>"
      using id_ab_type sc_type mult_uncurried_type id_type cfunc_cross_prod_comp_cfunc_prod by fastforce
    also have "... =  mult_uncurried \<circ>\<^sub>c \<langle>mult_uncurried \<circ>\<^sub>c  (\<langle>a,b\<rangle>),(successor \<circ>\<^sub>c c)\<rangle>"
      using ab_type id_left_unit2 sc_type by auto
    also have "... = (a \<cdot>\<^sub>\<nat> b)  \<cdot>\<^sub>\<nat> (successor  \<circ>\<^sub>c c)"
      by (simp add: mult_def)
then show ?thesis using calculation by auto
qed

(*Likewise ...*)

  have f5: "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor)))
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle> = a \<cdot>\<^sub>\<nat> (b  \<cdot>\<^sub>\<nat> (successor  \<circ>\<^sub>c c))"
  proof - 
    have "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor)))
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle> =(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor))
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
      using comp_associative by auto
    also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>))
\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f  successor)
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
      using comp_associative identity_distributes_across_composition multIdxMultp0p0p1p0p1_Sharp_type successor_type by auto
    also have "... = (mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)
\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f  successor)
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
      using comp_associative flat_cancels_sharp inv_transpose_func_def2 multIdxMultp0p0p1p0p1_Sharp_type multIdxMultp0p0p1p0p1_type by fastforce
    also have "... = (mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)
\<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>a,b\<rangle>,successor  \<circ>\<^sub>c c\<rangle>"
      using ab_type assms(3) cfunc_cross_prod_comp_cfunc_prod id_type successor_type by fastforce
    also have "... = (mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,successor  \<circ>\<^sub>c c\<rangle>"
      using ab_type id_left_unit2 by auto
    also have "... = mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,successor  \<circ>\<^sub>c c\<rangle>"
      using comp_associative by force
    also have "... = mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,successor  \<circ>\<^sub>c c\<rangle> ,
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>    \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,successor  \<circ>\<^sub>c c\<rangle>   \<rangle>"
      using abSc_type cfunc_prod_comp comp_associative p0rho0_type p1rho0rho1_type by auto
    also have "... = mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>a,b\<rangle> ,
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,successor  \<circ>\<^sub>c c\<rangle>  , (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,successor  \<circ>\<^sub>c c\<rangle>\<rangle>\<rangle>"
      by (smt abSc_type ab_type cfunc_prod_comp comp_associative left_cart_proj_cfunc_prod p1rho0_type right_cart_proj_type sc_type)
    also have "... = mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>a ,
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>a,b\<rangle>  , successor  \<circ>\<^sub>c c  \<rangle>  \<rangle>"
      using ab_type assms(1) assms(2) left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod sc_type by auto
    also have "... = mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>a,\<langle>b,successor  \<circ>\<^sub>c c\<rangle>\<rangle>"
      using assms(1) assms(2) right_cart_proj_cfunc_prod by auto
    also have "... = mult_uncurried \<circ>\<^sub>c  \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c a, mult_uncurried \<circ>\<^sub>c \<langle>b,successor  \<circ>\<^sub>c c\<rangle>\<rangle>"
      using assms(1) bSc_type id_type mult_uncurried_type cfunc_cross_prod_comp_cfunc_prod by fastforce
    also have "... =   a \<cdot>\<^sub>\<nat> (b  \<cdot>\<^sub>\<nat> (successor  \<circ>\<^sub>c c))"
      using assms(1) id_left_unit2 mult_def by auto
then show ?thesis using calculation by auto
qed

(*Now we compute this pair... *)

  have f6: "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((add_uncurried \<circ>\<^sub>c \<langle>mult_uncurried \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>)
\<circ>\<^sub>c ((mult_uncurried \<circ>\<^sub>c (mult_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)
))  \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle> = (a \<cdot>\<^sub>\<nat> b)  \<cdot>\<^sub>\<nat> (successor  \<circ>\<^sub>c c)"
  proof - 
    have "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((add_uncurried \<circ>\<^sub>c \<langle>mult_uncurried \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>)
\<circ>\<^sub>c ((mult_uncurried \<circ>\<^sub>c (mult_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)
))  \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle> = 
 (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((add_uncurried \<circ>\<^sub>c \<langle>mult_uncurried \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>)
\<circ>\<^sub>c ((mult_uncurried \<circ>\<^sub>c (mult_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)
)  \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
      by (simp add: comp_associative)
    also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((add_uncurried \<circ>\<^sub>c \<langle>mult_uncurried \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>)) \<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult_uncurried \<circ>\<^sub>c (mult_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>))\<circ>\<^sub>c
\<langle>\<langle>a,b\<rangle>,c\<rangle>"
      using addMultSigma0EvalSharp_type comp_associative identity_distributes_across_composition multmultIdSharp_type by auto
    also have "... = (add_uncurried \<circ>\<^sub>c \<langle>mult_uncurried \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<rangle>) \<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult_uncurried \<circ>\<^sub>c (mult_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>))\<circ>\<^sub>c
\<langle>\<langle>a,b\<rangle>,c\<rangle>"
      using addMultSigma0Eval_type comp_associative transpose_func_def by presburger
    also have "... = ((add_uncurried \<circ>\<^sub>c
\<langle>mult_uncurried \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)),
eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<rangle>) 
\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult_uncurried \<circ>\<^sub>c (mult_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)))
\<circ>\<^sub>c\<langle>\<langle>a,b\<rangle>,c\<rangle>"
      by (simp add: comp_associative)
    also have "... = (
add_uncurried \<circ>\<^sub>c
\<langle>mult_uncurried \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>))
\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult_uncurried \<circ>\<^sub>c (mult_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)),
eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)
\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult_uncurried \<circ>\<^sub>c (mult_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>))\<rangle> 
)
\<circ>\<^sub>c\<langle>\<langle>a,b\<rangle>,c\<rangle>"
      by (smt cfunc_prod_comp comp_associative eval_func_type id_multmultidsharp_type multsigma0_type)
    also have "... = (
add_uncurried \<circ>\<^sub>c
\<langle>mult_uncurried \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<nat>\<^sub>c) ,
eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)
\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult_uncurried \<circ>\<^sub>c (mult_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>))\<rangle> 
)
\<circ>\<^sub>c\<langle>\<langle>a,b\<rangle>,c\<rangle>"
      by (smt id_type left_cart_proj_cfunc_cross_prod multmultIdSharp_type)
    also have "... = 
add_uncurried \<circ>\<^sub>c
\<langle>mult_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<nat>\<^sub>c ,
eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)
\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult_uncurried \<circ>\<^sub>c (mult_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>))\<rangle> 
\<circ>\<^sub>c\<langle>\<langle>a,b\<rangle>,c\<rangle>"
      using comp_associative id_right_unit2 mult_uncurried_type by auto
also have "... = add_uncurried \<circ>\<^sub>c
\<langle>mult_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c\<langle>\<langle>a,b\<rangle>,c\<rangle> ,
eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)
\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult_uncurried \<circ>\<^sub>c (mult_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>))\<circ>\<^sub>c\<langle>\<langle>a,b\<rangle>,c\<rangle>   \<rangle>"
         apply(subst cfunc_prod_comp[where X = "one", where Y= "(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c",
                    where A = "\<nat>\<^sub>c", where B= "\<nat>\<^sub>c"])
          using abc_type apply force
          using comp_type left_cart_proj_type mult_uncurried_type apply blast
          using multmultId_type transpose_func_def apply auto[1]
          using comp_associative by presburger
also have "... =  add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c  \<langle>a,b\<rangle> ,(mult_uncurried \<circ>\<^sub>c (mult_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c\<langle>\<langle>a,b\<rangle>,c\<rangle>   \<rangle>"
    using ab_type assms(3) comp_associative left_cart_proj_cfunc_prod multmultId_type transpose_func_def by auto
  also have "... = add_uncurried \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c  \<langle>a,b\<rangle> ,mult_uncurried  \<circ>\<^sub>c\<langle>mult_uncurried \<circ>\<^sub>c\<langle>a,b\<rangle>,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c c\<rangle>   \<rangle>"
    by (smt ab_type assms(3) cfunc_cross_prod_comp_cfunc_prod comp_associative id_type mult_uncurried_type)
  also have "... = (a \<cdot>\<^sub>\<nat> b) +\<^sub>\<nat> ((a \<cdot>\<^sub>\<nat> b)\<cdot>\<^sub>\<nat> c)"
    using add_def assms(3) id_left_unit2 mult_def by auto
  also have "... =  (a \<cdot>\<^sub>\<nat> b)  \<cdot>\<^sub>\<nat> (successor  \<circ>\<^sub>c c)"
    using assms(3) mult_def mult_respects_succ_right multab_type by auto
then show ?thesis using calculation by auto
qed


(*Next to last on page 20*)


(*
  have f7: "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((add_uncurried \<circ>\<^sub>c \<langle>mult_uncurried \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>)
\<circ>\<^sub>c  (mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>
))  \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle> = a \<cdot>\<^sub>\<nat> (b  \<cdot>\<^sub>\<nat> (successor  \<circ>\<^sub>c c))"
  proof - 
    have "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((add_uncurried \<circ>\<^sub>c \<langle>mult_uncurried \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>)
\<circ>\<^sub>c  (mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>
))  \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle> =   
((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c 
(id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((add_uncurried \<circ>\<^sub>c \<langle>mult_uncurried \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>)
))
\<circ>\<^sub>c ( id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f  (mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>)
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
      using addMultSigma0EvalSharp_type comp_associative identity_distributes_across_composition multIdxMultp0p0p1p0p1_Sharp_type by auto
    also have "... = add_uncurried \<circ>\<^sub>c \<langle>mult_uncurried \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>))
, eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)
\<rangle>
\<circ>\<^sub>c ( id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f  (mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>)
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
      using comp_associative addMultSigma0Eval_type transpose_func_def by auto
    also have "...  = (add_uncurried \<circ>\<^sub>c \<langle>mult_uncurried \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>))
, eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)
\<rangle>
\<circ>\<^sub>c ( id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f  (mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>)
)\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
      using comp_associative by auto
    also have "... = (add_uncurried \<circ>\<^sub>c \<langle>mult_uncurried \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>))
\<circ>\<^sub>c ( id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f  (mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>)
, eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)
\<circ>\<^sub>c ( id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f  (mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>)\<rangle>
)\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
      apply (subst cfunc_prod_comp[where X ="(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c",
          where Y = "(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)", where A= "\<nat>\<^sub>c", where B="\<nat>\<^sub>c"])
      apply (simp add: cfunc_cross_prod_type id_type multIdxMultp0p0p1p0p1_Sharp_type)
      using multsigma0_type apply blast
      using eval_func_type apply force
      by (simp add: comp_associative)
    also have "... = (add_uncurried \<circ>\<^sub>c \<langle>mult_uncurried \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>))
\<circ>\<^sub>c ( id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f  (mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>)
, 
  mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>\<rangle>
)\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
      using multIdxMultp0p0p1p0p1_type transpose_func_def by auto
    also have "... = 
(add_uncurried \<circ>\<^sub>c \<langle>mult_uncurried \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<nat>\<^sub>c)  
, 
  mult_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult_uncurried) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>\<rangle>
)\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
      by (smt id_type left_cart_proj_cfunc_cross_prod multIdxMultp0p0p1p0p1_Sharp_type)
    also have "... = 
     (add_uncurried \<circ>\<^sub>c \<langle>mult_uncurried \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<nat>\<^sub>c)  
, 
  mult_uncurried  \<circ>\<^sub>c
 \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>
\<rangle>
\<rangle>
)\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
      using cfunc_cross_prod_comp_cfunc_prod id_type mult_uncurried_type p0rho0_type p1rho0rho1_type by fastforce
    also have "... = add_uncurried \<circ>\<^sub>c 
\<langle>mult_uncurried \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<nat>\<^sub>c)  
, 
  mult_uncurried  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>
\<rangle>
\<rangle>
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
      by (smt comp_associative id_left_unit2 id_right_unit2 mult_uncurried_type p0rho0_type)
    also have "... = add_uncurried \<circ>\<^sub>c 
\<langle>mult_uncurried \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<nat>\<^sub>c)  
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>
,
  mult_uncurried  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>
\<rangle>
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle> \<rangle>"
      apply (subst cfunc_prod_comp[where X = "one", where Y = "(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c",
            where A = "\<nat>\<^sub>c", where B= "\<nat>\<^sub>c"])
      using abc_type apply blast
      using comp_type left_cart_proj_type mult_uncurried_type apply blast
      apply (smt cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_type multIdxMultp0p0p1p0p1_type mult_uncurried_type p0rho0_type p1rho0rho1_type)
      by (simp add: comp_associative)
    also have "... =add_uncurried \<circ>\<^sub>c 
\<langle>mult_uncurried \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<nat>\<^sub>c)  
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>
,
  mult_uncurried  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>
,
mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>
\<rangle>
 \<rangle>"
      apply (subst cfunc_prod_comp [where X = "one", where Y = "(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c",
            where  A = "\<nat>\<^sub>c", where B = "\<nat>\<^sub>c"])
      using abc_type apply blast
      using p0rho0_type apply fastforce
      using comp_type mult_uncurried_type p1rho0rho1_type apply blast
      by (simp add: comp_associative)
    also have "... = add_uncurried \<circ>\<^sub>c 
\<langle>mult_uncurried \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<nat>\<^sub>c)  
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>
,
  mult_uncurried  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>
,
mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>
, (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>  \<rangle>
\<rangle>
 \<rangle>"
      by (smt abc_type cfunc_prod_comp comp_associative p1rho0_type right_cart_proj_type)
    also have "... = add_uncurried \<circ>\<^sub>c 
\<langle>mult_uncurried \<circ>\<^sub>c 
 \<langle>a,b\<rangle>
,
  mult_uncurried  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>a,b\<rangle>
,
mult_uncurried \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c  \<langle>a,b\<rangle>
, (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>  \<rangle>
\<rangle>
 \<rangle>"
      using ab_type assms(3) left_cart_proj_cfunc_prod by auto
    also have "... = add_uncurried \<circ>\<^sub>c 
\<langle>mult_uncurried \<circ>\<^sub>c \<langle>a,b\<rangle> ,mult_uncurried  \<circ>\<^sub>c \<langle>a, mult_uncurried \<circ>\<^sub>c \<langle>b, c \<rangle>\<rangle>\<rangle>"
      using ab_type assms left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod by auto
    also have "... =  (a \<cdot>\<^sub>\<nat> b) +\<^sub>\<nat> a \<cdot>\<^sub>\<nat> (b \<cdot>\<^sub>\<nat> c)"
      by (simp add: add_def mult_def)
    also have "... = a \<cdot>\<^sub>\<nat> b  +\<^sub>\<nat> (b \<cdot>\<^sub>\<nat> c) \<cdot>\<^sub>\<nat> a"
      oops
*)

  oops

*)


(* Don't forget to do Right Distributivity *)


lemma mult_right_distributivity:
  assumes "a \<in>\<^sub>c  \<nat>\<^sub>c"  "b\<in>\<^sub>c  \<nat>\<^sub>c"  "c\<in>\<^sub>c  \<nat>\<^sub>c"
  shows "a \<cdot>\<^sub>\<nat> ( b +\<^sub>\<nat> c)   = (a \<cdot>\<^sub>\<nat> b) +\<^sub>\<nat>  (a \<cdot>\<^sub>\<nat> c)"
  oops

end