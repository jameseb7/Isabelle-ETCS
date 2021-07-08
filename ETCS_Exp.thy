theory ETCS_Exp
  imports ETCS_Mult
begin

(*Defining exponentiation on N*)

definition exp_curried :: "cfunc" where
   "exp_curried = (THE w. w: \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<and>
   triangle_commutes one \<nat>\<^sub>c  (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) zero w ((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>) \<and>
   square_commutes \<nat>\<^sub>c  (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) w ((mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) successor w)"

lemma exp_curried_property: "(exp_curried: \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<and>
   triangle_commutes one \<nat>\<^sub>c  (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) zero exp_curried ((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>) \<and>
   square_commutes \<nat>\<^sub>c  (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) exp_curried ((mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) successor exp_curried)"
  unfolding exp_curried_def
proof (rule theI')
  have q_type: "((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>) :  one \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
    by typecheck_cfuncs
  have f_type: "((mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) : (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<rightarrow> (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)"
    by typecheck_cfuncs
  show "\<exists>!x. x : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<and>
         triangle_commutes one \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) zero x
          ((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>) \<and>
          square_commutes \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) x
          ((mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>)
          successor x"
    by (simp add: f_type natural_number_object_property q_type)
qed

lemma exp_curried_type[type_rule]: "exp_curried:  \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
  by (simp add: exp_curried_property)
 
lemma exp_curried_0_eq: "exp_curried \<circ>\<^sub>c zero = ((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>)"
  using exp_curried_property triangle_commutes_def by blast

lemma exp_curried_comp_succ_eq: "exp_curried \<circ>\<^sub>c successor = ((mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c exp_curried"
  using exp_curried_property square_commutes_def by auto

definition exp_uncurried :: "cfunc"
  where "exp_uncurried = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f exp_curried)"

lemma exp_uncurried_type[type_rule]: "exp_uncurried:  \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c"
  unfolding exp_uncurried_def
proof - 
  have "id \<nat>\<^sub>c \<times>\<^sub>f exp_curried : \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<times>\<^sub>c(\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)"
    by (simp add: exp_curried_property cfunc_cross_prod_type id_type)
  then show "eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f exp_curried : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    using comp_type eval_func_type by blast
qed

definition exp :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" (infixl "^\<^sub>\<nat>" 75)
  where "m ^\<^sub>\<nat> n = exp_uncurried\<circ>\<^sub>c\<langle>m, n\<rangle>"

lemma exp_uncurried_apply:
  assumes "m : X \<rightarrow> \<nat>\<^sub>c" "n : X \<rightarrow> \<nat>\<^sub>c"
  shows "exp_uncurried \<circ>\<^sub>c \<langle>m, n\<rangle> = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, exp_curried \<circ>\<^sub>c n\<rangle>"
 unfolding exp_def  exp_uncurried_def
 using assms by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod comp_associative2 id_left_unit2)


lemma exp_def2:
  assumes "m\<in>\<^sub>c  \<nat>\<^sub>c" "n\<in>\<^sub>c  \<nat>\<^sub>c"
  shows "m ^\<^sub>\<nat> n = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, exp_curried \<circ>\<^sub>c n\<rangle>"
  unfolding exp_def exp_uncurried_def
  using assms apply typecheck_cfuncs
  using exp_uncurried_apply exp_uncurried_def by auto


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
    using assms by (typecheck_cfuncs, simp add: comp_associative2)
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
  using assms by (typecheck_cfuncs, simp add: comp_associative2)
  also have "... = exp_uncurried \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<rangle> \<circ>\<^sub>c m"
    using assms(1) cfunc_prod_comp fact1 id_type by fastforce
  then show ?thesis
    by (simp add: calculation exp_def)
qed

lemma s0proj_type[type_rule]: "successor \<circ>\<^sub>c zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c one): \<nat>\<^sub>c \<times>\<^sub>c one \<rightarrow> \<nat>\<^sub>c"
    using comp_type right_cart_proj_type successor_type zero_type by blast
lemma s0projSharp_type[type_rule]: "(successor \<circ>\<^sub>c zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c one))\<^sup>\<sharp>: one \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
  by (simp add: s0proj_type transpose_func_type)


lemma exp_respects_zero_left_elfree:
  "exp_uncurried  \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> = successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
proof -
  have "exp_uncurried  \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, exp_curried \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
    using exp_uncurried_apply id_type successor_type terminal_func_comp zero_beta_N_succ_type by auto
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, ((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>)  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
    by (typecheck_cfuncs, simp add: comp_associative2 exp_curried_0_eq)
  also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
    by (smt cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_type s0projSharp_type terminal_func_type)
  also have "... = successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one  \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
    by (typecheck_cfuncs, smt comp_associative2 flat_cancels_sharp inv_transpose_func_def2)
  also have "... = successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
    by (metis id_type right_cart_proj_cfunc_prod terminal_func_type)
then show ?thesis
    by (simp add: calculation)
qed

lemma exp_closure[type_rule]:
  assumes "m \<in>\<^sub>c  \<nat>\<^sub>c" "n\<in>\<^sub>c  \<nat>\<^sub>c"
  shows "m ^\<^sub>\<nat> n \<in>\<^sub>c  \<nat>\<^sub>c"
  unfolding exp_def
  using assms by typecheck_cfuncs

lemma exp_respects_Zero_Left:
  assumes "n \<in>\<^sub>c  \<nat>\<^sub>c"
  shows "n ^\<^sub>\<nat> zero = successor \<circ>\<^sub>c zero"
proof - 
  have "n ^\<^sub>\<nat> zero = exp_uncurried  \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c n"
    by (simp add: assms exp_apply1_left zero_type)
  also have "... = successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c n"
    using assms by (typecheck_cfuncs, simp add: comp_associative2 exp_respects_zero_left_elfree)
  also have "... =  successor \<circ>\<^sub>c zero"
    using assms terminal_func_comp zero_beta_succ_mEqs0 by (typecheck_cfuncs, force)
 then show ?thesis
   by (simp add: calculation)
qed
   




(*Notice, in particular that 0^0 = 1*)


(*
lemma exp_respects_one_right_elfree:
  "exp_uncurried  \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> = id\<^sub>c \<nat>\<^sub>c"
proof - 
  have type1: "((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>)\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
    using cfunc_type_def codomain_comp compatible_comp_ETCS_func domain_comp s0b_type s0projSharp_type zero_type by auto
  have type2: "\<langle>id\<^sub>c \<nat>\<^sub>c, ((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>)\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<times>\<^sub>c(\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)"
    by (simp add: cfunc_prod_type id_type type1)
  have "exp_uncurried  \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> =
eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, ((mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>cexp_curried \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<rangle>"
    by (metis comp_associative exp_curried_comp_succ_eq exp_uncurried_apply id_type s0b_type)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, (mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c ((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
    by (simp add: comp_associative exp_curried_0_eq)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c, (mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c ((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
    by (metis id_domain id_right_unit)
  also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>)\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
    using comp_associative comp_type exp_curried_0_eq exp_curried_type zero_betaN_type mult_pie_sharp_type id_type
    apply(subst cfunc_cross_prod_comp_cfunc_prod[where A="\<nat>\<^sub>c", where W = "\<nat>\<^sub>c", where X="\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>",where Y="\<nat>\<^sub>c", where Z= "\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"])
    using id_type apply auto[1]
    apply (metis comp_associative comp_type exp_curried_0_eq exp_curried_type zero_betaN_type)
    using mult_pie_sharp_type apply blast
    by simp
  also have "... =  mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>)\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
    using comp_associative mult_pie_type transpose_func_def by auto
  also have "... =  mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>)\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>)\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle> "
    apply(subst cfunc_prod_comp[where X = "\<nat>\<^sub>c", where Y = "\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>", where A ="\<nat>\<^sub>c", where B = "\<nat>\<^sub>c"])
    apply (metis cfunc_prod_type comp_associative comp_type exp_curried_0_eq exp_curried_type id_type zero_betaN_type)
    apply (simp add: left_cart_proj_type)
    apply (simp add: eval_func_type)
    by simp
  also have "... =  mult2 \<circ>\<^sub>c\<langle>id\<^sub>c \<nat>\<^sub>c,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>)\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle> "
    by (metis id_type left_cart_proj_cfunc_prod type1)
  also have "... =  mult2 \<circ>\<^sub>c\<langle>id\<^sub>c \<nat>\<^sub>c,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle> "
    by (smt cfunc_cross_prod_comp_cfunc_prod id_right_unit2 id_type s0projSharp_type terminal_func_type)
  also have "... =  mult2 \<circ>\<^sub>c\<langle>id\<^sub>c \<nat>\<^sub>c, successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle> "
    using comp_associative s0proj_type transpose_func_def by presburger
  also have "... =  mult2 \<circ>\<^sub>c\<langle>id\<^sub>c \<nat>\<^sub>c, successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> "
    by (metis (no_types) id_type right_cart_proj_cfunc_prod terminal_func_type)
(*At this point we need the result from multiplication*)
*)


lemma exp_respects_one_right:
  assumes "n \<in>\<^sub>c  \<nat>\<^sub>c"
  shows "n ^\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = n" 
proof -
  have "n ^\<^sub>\<nat> (successor \<circ>\<^sub>c zero) =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n, exp_curried \<circ>\<^sub>c(successor \<circ>\<^sub>c zero) \<rangle>"
    using assms comp_type exp_def2 successor_type zero_type by blast
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n, ((mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>cexp_curried \<circ>\<^sub>c zero \<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_type_def comp_associative exp_curried_comp_succ_eq)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n, ((mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c ((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>)\<rangle>"
    by (simp add: exp_curried_0_eq)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c n, ((mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c ((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>)\<rangle>"
    using assms id_left_unit2 by auto
  also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ((mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>n,((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>)\<rangle>"
    by (smt assms cfunc_cross_prod_comp_cfunc_prod exp_curried_property id_type square_commutes_def triangle_commutes_def)
  also have "... = mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>n,((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>)\<rangle>"
    using assms by (typecheck_cfuncs, simp add: comp_associative2 transpose_func_def)
  also have "... = mult2 \<circ>\<^sub>c
\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)
\<circ>\<^sub>c \<langle>n,((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>)\<rangle>,
eval_func \<nat>\<^sub>c \<nat>\<^sub>c 
\<circ>\<^sub>c \<langle>n,((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>)\<rangle> \<rangle> "
    using assms cfunc_prod_type s0projSharp_type left_cart_proj_type eval_func_type
    by (metis cfunc_prod_comp)
  also have "... =  mult2 \<circ>\<^sub>c
\<langle>n ,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>)\<rangle> \<rangle> "
    using assms left_cart_proj_cfunc_prod s0projSharp_type by auto
  also have "... = mult2 \<circ>\<^sub>c
\<langle>n ,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c n,((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>) \<circ>\<^sub>c id\<^sub>c one  \<rangle> \<rangle> "
    using assms id_left_unit2 id_right_unit2 s0projSharp_type by auto
  also have "... = mult2 \<circ>\<^sub>c
\<langle>n ,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>))\<circ>\<^sub>c \<langle>n, id\<^sub>c one  \<rangle> \<rangle> "
    by (smt assms cfunc_cross_prod_comp_cfunc_prod id_type s0projSharp_type)
  also have "... = mult2 \<circ>\<^sub>c \<langle>n ,successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one \<circ>\<^sub>c \<langle>n, id\<^sub>c one  \<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: comp_associative2 transpose_func_def)
  also have "... = mult2 \<circ>\<^sub>c \<langle>n ,successor \<circ>\<^sub>c zero \<circ>\<^sub>c id\<^sub>c one \<rangle>"
    by (metis (no_types) assms id_type right_cart_proj_cfunc_prod)
  also have "... = n"
    using assms id_right_unit2 mult_def s0_is_right_id zero_type by auto
  then show ?thesis
    using calculation by auto
qed

 lemma exp_respects_zero_left:
   assumes "n \<in>\<^sub>c  \<nat>\<^sub>c"
   shows "zero ^\<^sub>\<nat> (successor \<circ>\<^sub>c n) = zero" 
 proof - 
   have zbs_type: "\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
     by (simp add: cfunc_prod_type successor_type zero_betaN_type)

      have main_result: "zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> = exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, successor\<rangle>"
      proof(rule natural_number_object_func_unique[where X = "\<nat>\<^sub>c", where f = "zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"])
        show zb_type: "zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
          by (simp add: zero_betaN_type)
        show type_2: "exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
          using comp_type exp_uncurried_type zbs_type by blast
        show "zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
          by (simp add: zb_type)
        show "(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero =
    (exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>) \<circ>\<^sub>c zero"
        proof - 
          have "(exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>) \<circ>\<^sub>c zero = 
                 exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle> \<circ>\<^sub>c zero"
            by (typecheck_cfuncs, simp add: comp_associative2)
          also have "... = exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<circ>\<^sub>c zero ,successor \<circ>\<^sub>c zero\<rangle>"
            using cfunc_prod_comp comp_associative2 by(typecheck_cfuncs, auto)
          also have "... = exp_uncurried \<circ>\<^sub>c \<langle>zero ,successor \<circ>\<^sub>c zero\<rangle>"
            by (metis cfunc_type_def id_right_unit id_type one_unique_element terminal_func_comp terminal_func_type zero_type)
          also have "... = zero"
            using exp_def exp_respects_one_right zero_type by auto
          also have "... = (zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero"
            by (smt beta_N_succ_mEqs_Id1 comp_associative2 id_right_unit2 successor_type terminal_func_comp terminal_func_type zero_type)
          then show ?thesis using calculation by auto
        qed

        show "(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor =
    (zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
        proof(rule one_separator[where X = "\<nat>\<^sub>c", where Y = "\<nat>\<^sub>c"])
          show "(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
            by (meson comp_type successor_type zb_type)
          show "(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
            using comp_type zb_type by blast
          show "\<And>x. x \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
         ((zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
         ((zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c x"
            by (typecheck_cfuncs , smt comp_associative2 terminal_func_comp)
        qed

        show " (exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>) \<circ>\<^sub>c successor =
    (zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>"
        proof(rule one_separator[where X = "\<nat>\<^sub>c", where Y = "\<nat>\<^sub>c"] )
          show "(exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>) \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
            by (meson comp_type successor_type type_2)
          show "(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
            using comp_type type_2 zb_type by blast
          show "\<And>x. x \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
         ((exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>) \<circ>\<^sub>c
          successor) \<circ>\<^sub>c
         x =
         ((zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c
          exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>) \<circ>\<^sub>c
         x"
          proof - 
            fix x 
            assume x_type: "x \<in>\<^sub>c \<nat>\<^sub>c"
            have "(exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, successor\<rangle> \<circ>\<^sub>c successor)\<circ>\<^sub>c x = 
     eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, exp_curried \<circ>\<^sub>c successor \<rangle> \<circ>\<^sub>c successor \<circ>\<^sub>c x"
        using x_type  by (typecheck_cfuncs, smt comp_associative2 exp_uncurried_apply)
          
            also have "... =  eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c
      \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, ((mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c exp_curried\<rangle> \<circ>\<^sub>c successor \<circ>\<^sub>c x"
             using exp_curried_comp_succ_eq by auto
           also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c 
      \<langle>id\<^sub>c\<nat>\<^sub>c \<circ>\<^sub>c  zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, ((mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c exp_curried\<rangle> \<circ>\<^sub>c successor \<circ>\<^sub>c x"
             using id_left_unit2 successor_type terminal_func_comp zero_beta_N_succ_type by auto
           also have "... =  eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c  (id\<^sub>c\<nat>\<^sub>c \<times>\<^sub>f ((mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>)) 
      \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, exp_curried\<rangle> \<circ>\<^sub>c successor \<circ>\<^sub>c x"
             using x_type by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod comp_associative2)
           also have "... = (mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, exp_curried\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c x"
             using x_type by (typecheck_cfuncs, smt comp_associative2 flat_cancels_sharp inv_transpose_func_def2)
           also have "... =  (mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, exp_curried\<rangle> ,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, exp_curried\<rangle> \<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c x"
             using cfunc_prod_comp by (typecheck_cfuncs, auto)
             
           also have "... = (mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, exp_curried\<rangle> ,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id\<^sub>c\<nat>\<^sub>c \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, exp_curried \<circ>\<^sub>c id\<^sub>c\<nat>\<^sub>c\<rangle> \<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c x"
             using exp_curried_type id_left_unit2 id_right_unit2 successor_type terminal_func_comp zero_beta_N_succ_type by auto
           also have "... = (mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, exp_curried\<rangle> ,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c\<nat>\<^sub>c \<times>\<^sub>f exp_curried) \<circ>\<^sub>c  \<langle> zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,  id\<^sub>c\<nat>\<^sub>c\<rangle> \<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c x"
             by (smt cfunc_cross_prod_comp_cfunc_prod exp_curried_property id_type successor_type terminal_func_comp zero_beta_N_succ_type)
           also have "... = (mult2 \<circ>\<^sub>c\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c\<nat>\<^sub>c \<times>\<^sub>f exp_curried) \<circ>\<^sub>c  \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,  id\<^sub>c\<nat>\<^sub>c\<rangle> \<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c x"
             by (metis (no_types) exp_curried_property left_cart_proj_cfunc_prod zero_betaN_type)
           also have "... = (mult2 \<circ>\<^sub>c\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,  id\<^sub>c\<nat>\<^sub>c\<rangle> \<rangle>)\<circ>\<^sub>c successor \<circ>\<^sub>c x"
             using x_type by (typecheck_cfuncs, simp add: cfunc_type_def comp_associative exp_uncurried_def)
           also have "... =  mult2 \<circ>\<^sub>c\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,  id\<^sub>c\<nat>\<^sub>c\<rangle> \<rangle>\<circ>\<^sub>c successor \<circ>\<^sub>c x"
             using x_type by (typecheck_cfuncs, metis comp_associative2)
           also have "... =  mult2 \<circ>\<^sub>c\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor \<circ>\<^sub>c x, exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,  id\<^sub>c\<nat>\<^sub>c\<rangle>\<circ>\<^sub>c successor \<circ>\<^sub>c x \<rangle>"
             using x_type by (typecheck_cfuncs, smt cfunc_prod_comp cfunc_type_def comp_associative)
           also have "... = zero"
             using mult_def mult_respects_zero_left x_type zero_beta_succ_mEqs0 by (typecheck_cfuncs, presburger)
           also have "... = ((zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c
                exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>) \<circ>\<^sub>c
               x"
             by (typecheck_cfuncs, smt comp_associative2 terminal_func_comp x_type zero_beta_succ_mEqs0)
           then show "((exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>) \<circ>\<^sub>c successor) \<circ>\<^sub>c x = ((zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>) \<circ>\<^sub>c x"
             using calculation comp_associative2 exp_uncurried_type successor_type zbs_type by auto
         qed
       qed
     qed

     have final_eqn: "zero ^\<^sub>\<nat> (successor \<circ>\<^sub>c n) = exp_uncurried \<circ>\<^sub>c \<langle>zero , successor \<circ>\<^sub>c n\<rangle>"
       using exp_def by auto
     also have "... = exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c n , successor \<circ>\<^sub>c n\<rangle>" 
       by (typecheck_cfuncs, metis assms terminal_func_comp zero_beta_succ_mEqs0)
     also have "... = exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>  , successor\<rangle> \<circ>\<^sub>c n "
       by (smt assms cfunc_prod_comp comp_associative2 successor_type terminal_func_type zero_betaN_type zero_type)
     also have "... = zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c n "
       using assms comp_associative2 exp_uncurried_type main_result terminal_func_type zbs_type zero_type by force
     also have "... = zero"
       using assms calculation exp_respects_one_right nonzero_is_succ zero_beta_succ_mEqs0 by fastforce
     then show ?thesis
       by (simp add: calculation)
   qed
   


  
lemma exp_respects_one_left:
   assumes "n \<in>\<^sub>c  \<nat>\<^sub>c"
   shows "(successor \<circ>\<^sub>c zero)^\<^sub>\<nat> n = (successor \<circ>\<^sub>c zero)" 
proof - 
  have s0b0Eqs0: "((successor \<circ>\<^sub>c zero)\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero = (successor \<circ>\<^sub>c zero)"
    using assms by (typecheck_cfuncs, smt beta_N_succ_mEqs_Id1 comp_associative2 id_right_unit2 terminal_func_comp)
   
  have ExpS0b1z: "(exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c zero)\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id\<^sub>c\<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero = (successor \<circ>\<^sub>c zero)"
    using assms by (typecheck_cfuncs, metis cfunc_type_def comp_associative exp_apply1 exp_respects_Zero_Left)
  have szbs_n: "(((successor \<circ>\<^sub>c zero)\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor) \<circ>\<^sub>c  n = ((successor \<circ>\<^sub>c zero)\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c  n"
    using assms by (typecheck_cfuncs, smt comp_associative2 terminal_func_comp)

  have main_result:  "successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> = exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id\<^sub>c\<nat>\<^sub>c\<rangle>"
  proof(rule natural_number_object_func_unique[where X = "\<nat>\<^sub>c", where f = "id\<^sub>c\<nat>\<^sub>c"])
    show "successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
      by (simp add: s0b_type)
    show type1: "exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
      using comp_type exp_uncurried_type s0b_id_type by blast
    show "id\<^sub>c \<nat>\<^sub>c : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
      by (simp add: id_type)
    show "(successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero =
    (exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: ExpS0b1z comp_associative2 s0b0Eqs0)
    show "(successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor =
    id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
      by (typecheck_cfuncs, smt comp_associative2 id_left_unit2 terminal_func_comp)
    show "(exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor =
    id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
    proof(rule one_separator[where X = "\<nat>\<^sub>c", where Y = "\<nat>\<^sub>c"])
      show "(exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
        using comp_type successor_type type1 by auto
      show "id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
        using id_left_unit2 type1 by auto
      show "\<And>x. x \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
         ((exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c
          successor) \<circ>\<^sub>c
         x =
         (id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c x"
      proof - 
        fix x 
        assume x_type: "x \<in>\<^sub>c \<nat>\<^sub>c"
        have sx_type: "successor \<circ>\<^sub>c x  \<in>\<^sub>c \<nat>\<^sub>c"
          by (simp add: succ_n_type x_type)

        have "((exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c
          successor) \<circ>\<^sub>c
         x = exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (successor \<circ>\<^sub>c x)"
          by (typecheck_cfuncs, metis cfunc_type_def comp_associative x_type)
   also have "... = exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c (successor \<circ>\<^sub>c x),  successor \<circ>\<^sub>c x\<rangle>"
     using x_type by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 id_left_unit2)
    also have "... =  exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero, successor \<circ>\<^sub>c x\<rangle>"
      using x_type zero_beta_succ_mEqs0 by auto
    also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id\<^sub>c\<nat>\<^sub>c \<times>\<^sub>f exp_curried) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero, successor \<circ>\<^sub>c x\<rangle>"
      using x_type by (typecheck_cfuncs, simp add: comp_associative2 exp_uncurried_def)
    also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id\<^sub>c\<nat>\<^sub>c \<times>\<^sub>f (id\<^sub>c(\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c exp_curried)) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero, successor \<circ>\<^sub>c x\<rangle>"
      using exp_curried_property id_left_unit2 by auto
    also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id\<^sub>c\<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c(\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero, exp_curried \<circ>\<^sub>c successor \<circ>\<^sub>c x\<rangle>"
      using x_type by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
    also have "... =  eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id\<^sub>c\<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c(\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero, ((mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>)     \<circ>\<^sub>c  exp_curried  \<circ>\<^sub>c x\<rangle>"
      using x_type by (typecheck_cfuncs, simp add: comp_associative2 exp_curried_comp_succ_eq)  
    also have "... =  eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id\<^sub>c\<nat>\<^sub>c \<times>\<^sub>f (id\<^sub>c(\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c ((mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) ) ) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero,    exp_curried  \<circ>\<^sub>c x\<rangle>"
       using x_type by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
     also have "... = (mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero,    exp_curried  \<circ>\<^sub>c x\<rangle>"
       using x_type by (typecheck_cfuncs, simp add: comp_associative2 id_left_unit2 transpose_func_def)
     also have "... = mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero,    exp_curried  \<circ>\<^sub>c x\<rangle>"
       by (typecheck_cfuncs, metis x_type comp_associative2)
     also have "... = mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero,    exp_curried  \<circ>\<^sub>c x\<rangle>,
        eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero,    exp_curried  \<circ>\<^sub>c x\<rangle> \<rangle>"
       by (typecheck_cfuncs, metis x_type cfunc_prod_comp)
     also have "... = mult2 \<circ>\<^sub>c\<langle>successor \<circ>\<^sub>c zero,   eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero,    exp_curried  \<circ>\<^sub>c x\<rangle>\<rangle>"
       using x_type left_cart_proj_cfunc_prod by (typecheck_cfuncs, presburger)
     also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero,    exp_curried  \<circ>\<^sub>c x\<rangle>"
       using mult_def s0_is_left_id x_type by (typecheck_cfuncs, auto)
     also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f exp_curried) \<circ>\<^sub>c \<langle> successor \<circ>\<^sub>c zero, x\<rangle>"
       using cfunc_cross_prod_comp_cfunc_prod id_left_unit2 x_type by (typecheck_cfuncs, auto)
     also have "... = exp_uncurried \<circ>\<^sub>c \<langle> successor \<circ>\<^sub>c zero, x\<rangle>"
       by (typecheck_cfuncs, simp add: \<open>eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero,exp_curried \<circ>\<^sub>c x\<rangle> = eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f exp_curried) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero,x\<rangle>\<close> exp_uncurried_apply x_type)
     also have "... = exp_uncurried \<circ>\<^sub>c \<langle> successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c x , x\<rangle>"
       by (typecheck_cfuncs, metis terminal_func_comp x_type zero_beta_succ_mEqs0)
     also have "... = (id\<^sub>c\<nat>\<^sub>c \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle> successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>  , id\<^sub>c\<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c x"
       by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 id_left_unit2 x_type)
     then show "((exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor) \<circ>\<^sub>c x = (id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c x"
       by (simp add: calculation)
   qed
 qed
qed

  then show ?thesis 
    by (typecheck_cfuncs, smt assms beta_N_succ_mEqs_Id1 cfunc_type_def comp_associative exp_apply1 exp_uncurried_type id_right_unit2 main_result s0b_id_type terminal_func_comp terminal_func_type)
qed



lemma exp_respects_successor:
   assumes "m \<in>\<^sub>c  \<nat>\<^sub>c" "n \<in>\<^sub>c  \<nat>\<^sub>c"
   shows "m^\<^sub>\<nat>(successor \<circ>\<^sub>c n) = m \<cdot>\<^sub>\<nat> (m^\<^sub>\<nat> n) "
proof - 
  have "m^\<^sub>\<nat>(successor \<circ>\<^sub>c n) = exp_uncurried \<circ>\<^sub>c \<langle>m,successor \<circ>\<^sub>c n\<rangle>"
    by (simp add: exp_def)
  also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f exp_curried) \<circ>\<^sub>c  \<langle>m,successor \<circ>\<^sub>c n\<rangle>"
    unfolding exp_uncurried_def
    using assms by (typecheck_cfuncs, simp add: comp_associative2)
  also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f exp_curried) \<circ>\<^sub>c  \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m,successor \<circ>\<^sub>c n\<rangle>"
    using assms(1) id_left_unit2 by auto
  also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f exp_curried) \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c   \<langle>m,  n\<rangle>"
    using assms(1) assms(2) cfunc_cross_prod_comp_cfunc_prod id_type successor_type by fastforce
  also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (exp_curried \<circ>\<^sub>c successor)) \<circ>\<^sub>c  \<langle>m,  n\<rangle>"
    using assms by (typecheck_cfuncs, simp add: comp_associative2 identity_distributes_across_composition)
  also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (((mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>)\<circ>\<^sub>c exp_curried)) \<circ>\<^sub>c  \<langle>m,  n\<rangle>"
    by (simp add: exp_curried_comp_succ_eq)
  also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>)  \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f exp_curried) \<circ>\<^sub>c   \<langle>m,n\<rangle>"
    using assms by (typecheck_cfuncs, simp add: comp_associative2 identity_distributes_across_composition)
  also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>)  \<circ>\<^sub>c   \<langle>m,exp_curried \<circ>\<^sub>c  n\<rangle>"
    using assms(1) assms(2) cfunc_cross_prod_comp_cfunc_prod exp_curried_type id_left_unit2 id_type by fastforce
  also have "... = mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>  \<circ>\<^sub>c   \<langle>m,exp_curried \<circ>\<^sub>c  n\<rangle>"
      using assms by (typecheck_cfuncs, simp add: comp_associative2 transpose_func_def)
  also have "... = mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c   \<langle>m,exp_curried \<circ>\<^sub>c  n\<rangle> ,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c   \<langle>m,exp_curried \<circ>\<^sub>c  n\<rangle>\<rangle>  "
    using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp)
  also have "... = mult2 \<circ>\<^sub>c\<langle>m ,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c   \<langle>m,exp_curried \<circ>\<^sub>c  n\<rangle>\<rangle>  "
    by (metis assms(1) assms(2) comp_type exp_curried_type left_cart_proj_cfunc_prod)
  also have "... = mult2 \<circ>\<^sub>c\<langle>m ,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f exp_curried)\<circ>\<^sub>c \<langle>m,   n\<rangle>\<rangle>  "
    using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
  also have "... = mult2 \<circ>\<^sub>c\<langle>m ,exp_uncurried\<circ>\<^sub>c \<langle>m,   n\<rangle>\<rangle>  "
    using assms by (typecheck_cfuncs, simp add: comp_associative2 exp_uncurried_def)
  also have "... = m \<cdot>\<^sub>\<nat> (m^\<^sub>\<nat> n) "
    by (simp add: exp_def mult_def)
then show ?thesis
    using calculation by auto
qed



lemma exp_left_dist:
   assumes "a \<in>\<^sub>c  \<nat>\<^sub>c" "b \<in>\<^sub>c  \<nat>\<^sub>c" "c \<in>\<^sub>c  \<nat>\<^sub>c"
   shows "(a \<cdot>\<^sub>\<nat> b)^\<^sub>\<nat> c = (a^\<^sub>\<nat> c) \<cdot>\<^sub>\<nat> (b^\<^sub>\<nat> c)"
proof - 
  have type0: "(id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f  zero ): (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one \<rightarrow> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c"
    by (simp add: cfunc_cross_prod_type id_type zero_type)
  have type1: "(mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f  zero ) : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one \<rightarrow>  \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
    using cfunc_cross_prod_type comp_type id_type mult2_type type0 by blast
  have type2: "(exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow>\<nat>\<^sub>c"
    by (meson cfunc_cross_prod_type comp_type exp_uncurried_type id_type mult2_type)

  have type2_sharp:  "(exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> :  \<nat>\<^sub>c  \<rightarrow>\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>"
    by (simp add: transpose_func_type type2)


    have main_result: "(exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> = (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
 (right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
 (right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>"
  proof(rule natural_number_object_func_unique[where X = "\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>", where f ="(mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)), eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>"])
    show "(exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
      by (simp add: type2_sharp)
    show type4: "(mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
      by typecheck_cfuncs
    show " (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> : \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup> \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
      by typecheck_cfuncs
    show "(exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero =
    (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero"
    proof(rule same_evals_equal[where Z = "one", where X = "\<nat>\<^sub>c", where A = "\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"])
      show "(exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero \<in>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
        by typecheck_cfuncs
      show "(mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero \<in>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
        by typecheck_cfuncs
      show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero = eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero"
      proof(rule one_separator[where X = "(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c one", where Y = "\<nat>\<^sub>c"])
        show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one \<rightarrow> \<nat>\<^sub>c"
          by typecheck_cfuncs
        show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one \<rightarrow> \<nat>\<^sub>c"
          by typecheck_cfuncs
        show "\<And>x. x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one \<Longrightarrow>
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x"
        proof - 
          fix x 
          assume x_type: "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one"
          obtain y where x_def: "y \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<and> x = \<langle>y,id one\<rangle>"
            by (typecheck_cfuncs, metis cart_prod_decomp terminal_func_unique x_type)
          obtain p q where y_def: "p \<in>\<^sub>c \<nat>\<^sub>c \<and> q \<in>\<^sub>c \<nat>\<^sub>c \<and> y = \<langle>p,q\<rangle>"
            using cart_prod_decomp x_def by blast
          have x_def2: "x = \<langle>\<langle>p,q\<rangle>,id one\<rangle>"
            by (simp add: x_def y_def)

          have "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>fzero) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, smt comp_associative2 inv_transpose_func_def2 inv_transpose_of_composition x_type)
          also have "... = (exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>fzero) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, simp add: transpose_func_def)
          also have "... = (exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,zero\<rangle>"
            by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2 id_type x_def y_def)
          also have "... = exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,zero\<rangle>"
            using comp_associative2 y_def by (typecheck_cfuncs, fastforce)
          also have "... = exp_uncurried \<circ>\<^sub>c  \<langle>mult2 \<circ>\<^sub>c \<langle>p,q\<rangle>,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero\<rangle>"
            by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod y_def)
          also have "... = exp_uncurried \<circ>\<^sub>c  \<langle>p \<cdot>\<^sub>\<nat> q ,zero\<rangle>"
            using id_left_unit2 mult_def zero_type by auto
          also have "... = (p \<cdot>\<^sub>\<nat> q) ^\<^sub>\<nat> zero"
            by (simp add: exp_def) 
          also have "... = (successor \<circ>\<^sub>c zero)"
            by (simp add: exp_respects_Zero_Left mult_closure y_def)
          also have "... = (successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c zero)"
            by (simp add: s0_is_right_id succ_n_type zero_type)
         also have "... = mult2 \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero, successor \<circ>\<^sub>c zero\<rangle>"
           by (simp add: mult_def)
         also have "... = mult2 \<circ>\<^sub>c  \<langle>p ^\<^sub>\<nat> zero, q ^\<^sub>\<nat> zero\<rangle>"
           by (simp add: exp_respects_Zero_Left y_def)
         also have "... = mult2 \<circ>\<^sub>c  \<langle>exp_uncurried \<circ>\<^sub>c \<langle>p,zero\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>q,zero\<rangle>\<rangle>"
           by (simp add: exp_def)
         also have "... = mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>p,zero\<rangle>,\<langle>q,zero\<rangle>\<rangle>"
           by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod y_def)
         also have "... = mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c
               \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,zero\<rangle>  ,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,zero\<rangle>  \<rangle>   ,
               \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,zero\<rangle>  ,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,zero\<rangle>  \<rangle>    \<rangle>"
           by (typecheck_cfuncs, smt left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod y_def)
         also have "... = mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c
 \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,zero\<rangle>  ,
 \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>   \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,zero\<rangle> \<rangle> "
           using cfunc_prod_comp cfunc_type_def comp_associative y_def by (typecheck_cfuncs, auto)
         also have "... = mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,zero\<rangle>"
           by (typecheck_cfuncs, smt cfunc_prod_comp y_def)
         also have "... = mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero) \<circ>\<^sub>c x"
           by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2 id_type x_def y_def)
         also have "... = (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero)) \<circ>\<^sub>c x"
           using comp_associative2 x_type by (typecheck_cfuncs, auto)
         also have "... = ((mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero)) \<circ>\<^sub>c x"
           by (typecheck_cfuncs, simp add: comp_associative2)
         also have "... = ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero)) \<circ>\<^sub>c x"
           by (typecheck_cfuncs, simp add: transpose_func_def) 
         also  have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x"
           by (typecheck_cfuncs, smt inv_transpose_func_def2 inv_transpose_of_composition)
         then show "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x =
                    (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x"
           by (simp add: calculation)
       qed
     qed
   qed
   show "(exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor =
         (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
   proof(rule same_evals_equal[where Z ="\<nat>\<^sub>c", where X = "\<nat>\<^sub>c", where A = "\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"])
     show "(exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
       by typecheck_cfuncs
     show "(mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
       by typecheck_cfuncs
     show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor =
    eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
     proof(rule one_separator[where X = "(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c", where Y = "\<nat>\<^sub>c"])
       show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
         by typecheck_cfuncs
       show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
         by typecheck_cfuncs
       show "\<And>x. x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c x"
       proof - 
         fix x 
         assume x_type: "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c"
         obtain y r where yr_type: "y \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<and> r \<in>\<^sub>c \<nat>\<^sub>c \<and> x = \<langle>y,r\<rangle>" 
           using cart_prod_decomp x_type by blast
         obtain p q where y_def: "p \<in>\<^sub>c \<nat>\<^sub>c \<and> q \<in>\<^sub>c \<nat>\<^sub>c \<and> y = \<langle>p,q\<rangle>"
           using cart_prod_decomp yr_type by blast
         have x_def: "x = \<langle>\<langle>p,q\<rangle> ,r\<rangle>"
           by (simp add: y_def yr_type)


         have "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
               ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>) \<circ>\<^sub>c(id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor)) \<circ>\<^sub>c x"
           by (typecheck_cfuncs, metis inv_transpose_func_def2 inv_transpose_of_composition)
         also have "... = ((exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c(id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor)) \<circ>\<^sub>c x"
           by (typecheck_cfuncs, simp add: transpose_func_def)
         also have "... = (exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c(id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor)) \<circ>\<^sub>c x"
           by (typecheck_cfuncs, simp add: comp_associative2)
         also have "... = exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c(id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor) \<circ>\<^sub>c x"
           using cfunc_type_def comp_associative x_type by (typecheck_cfuncs, fastforce)
         also have "... = exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle> ,successor \<circ>\<^sub>c r\<rangle>"
           by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod id_left_unit2 y_def yr_type)
         also have "... = exp_uncurried \<circ>\<^sub>c  \<langle>mult2 \<circ>\<^sub>c \<langle>p,q\<rangle> ,successor \<circ>\<^sub>c r\<rangle>"
           by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod id_left_unit2 y_def yr_type)
         also have "... = (p \<cdot>\<^sub>\<nat> q)^\<^sub>\<nat> (successor \<circ>\<^sub>c r)"
           by (simp add: exp_def mult_def)
         also have "... = (p \<cdot>\<^sub>\<nat> q) \<cdot>\<^sub>\<nat> ((p \<cdot>\<^sub>\<nat> q)^\<^sub>\<nat>r)"
           by (simp add: exp_respects_successor mult_closure y_def yr_type)
         also have "... = mult2 \<circ>\<^sub>c \<langle>p \<cdot>\<^sub>\<nat> q, exp_uncurried \<circ>\<^sub>c  \<langle>mult2 \<circ>\<^sub>c\<langle>p,q\<rangle> ,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c r\<rangle>\<rangle>"
           using exp_def id_left_unit2 mult_def yr_type by force
         also have "... = mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c  \<circ>\<^sub>c x, exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c x\<rangle>"
           by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod left_cart_proj_cfunc_prod mult_def y_def yr_type)
         also have "... = mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c, exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c x"
           using cfunc_prod_comp comp_associative2 x_type by (typecheck_cfuncs, auto)
         also have "... = (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c, exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c x"
           using comp_associative2 x_type by (typecheck_cfuncs,blast)
         also have "... = (mult2 \<circ>\<^sub>c \<langle>
            mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>),
            exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) 
               \<circ>\<^sub>c x"
           by (typecheck_cfuncs, simp add: id_left_unit2 left_cart_proj_cfunc_cross_prod)
         also have "... = (mult2 \<circ>\<^sub>c \<langle>
            mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>),
            eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>)\<rangle>) 
               \<circ>\<^sub>c x"
           using transpose_func_def by (typecheck_cfuncs, auto)
         also have "... = (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>) 
              \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c x"
           by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 x_type)
         also have "... = ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)
              \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>)) 
              \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>)) \<circ>\<^sub>c x"
           using comp_associative2 transpose_func_def x_type by (typecheck_cfuncs, auto)
         also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)
              \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>) 
              \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>)) \<circ>\<^sub>c x"
           by (typecheck_cfuncs, simp add: comp_associative2)

         then show " (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c x"
           by (typecheck_cfuncs, smt calculation inv_transpose_func_def2 inv_transpose_of_composition)         
       qed
     qed
   qed

   show "(mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor =
    (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>"

   proof(rule same_evals_equal[where Z ="\<nat>\<^sub>c", where X = "\<nat>\<^sub>c", where A = "\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"])
     show "(mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
       by typecheck_cfuncs
     show "(mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
       by typecheck_cfuncs
     show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor =
    eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>"
     proof(rule one_separator[where X = "(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c", where Y = "\<nat>\<^sub>c"])
       show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
         by typecheck_cfuncs
       show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
         by typecheck_cfuncs
       show "\<And>x. x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
          (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
          (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c x"
       proof - 
         fix x 
         assume x_type: "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c"
         obtain y r where yr_type: "y \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<and> r \<in>\<^sub>c \<nat>\<^sub>c \<and> x = \<langle>y,r\<rangle>" 
           using cart_prod_decomp x_type by blast
         obtain p q where y_def: "p \<in>\<^sub>c \<nat>\<^sub>c \<and> q \<in>\<^sub>c \<nat>\<^sub>c \<and> y = \<langle>p,q\<rangle>"
           using cart_prod_decomp yr_type by blast
         have x_def: "x = \<langle>\<langle>p,q\<rangle> ,r\<rangle>"
           by (simp add: y_def yr_type)
         have ysr_type: "\<langle>y,successor \<circ>\<^sub>c r\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c"
           using yr_type by (typecheck_cfuncs, blast)
         have psr_type: "\<langle>p ,successor \<circ>\<^sub>c r\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
           by (typecheck_cfuncs, simp add: y_def yr_type)
         have qsr_type: "\<langle>q ,successor \<circ>\<^sub>c r\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
           by (typecheck_cfuncs, simp add: y_def yr_type)
         have psrqsr_type: "\<langle>\<langle>p ,successor \<circ>\<^sub>c r\<rangle>,\<langle>q, successor \<circ>\<^sub>c r \<rangle>\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
           by (simp add: cfunc_prod_type psr_type qsr_type) 
         have pr_type: "\<langle>p,r\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
           by (simp add: cfunc_prod_type y_def yr_type)
         have qr_type: "\<langle>q,r\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
           by (simp add: cfunc_prod_type y_def yr_type)


         obtain F where F_def: "F = id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>"
           by simp

         have F_type: "F: (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)"
           by (typecheck_cfuncs, simp add: F_def cfunc_cross_prod_type id_type type4)



         have "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x = 
((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c(id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor)) \<circ>\<^sub>c x"
           by (typecheck_cfuncs, smt inv_transpose_func_def2 inv_transpose_of_composition)
         also have "... = ((mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c(id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor)) \<circ>\<^sub>c x"
           by (typecheck_cfuncs, simp add: transpose_func_def)
         also have "... = (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c(id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor) \<circ>\<^sub>c x"
           using comp_associative2 x_type by (typecheck_cfuncs, auto) 
         also have "... = (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c  \<langle>id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c y,successor \<circ>\<^sub>c r\<rangle>"
           using cfunc_cross_prod_comp_cfunc_prod yr_type by (typecheck_cfuncs, auto)
         also have "... = (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c  \<langle>y,successor \<circ>\<^sub>c r\<rangle>"
           using id_left_unit2 yr_type by (typecheck_cfuncs, auto)
         also have "... = mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c  \<langle>y,successor \<circ>\<^sub>c r\<rangle>"
           using cfunc_type_def comp_associative ysr_type by (typecheck_cfuncs, fastforce)
         also have "... = mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>y,successor \<circ>\<^sub>c r\<rangle> ,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>y,successor \<circ>\<^sub>c r\<rangle>\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>y,successor \<circ>\<^sub>c r\<rangle>,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>y,successor \<circ>\<^sub>c r\<rangle>\<rangle>\<rangle> "
           using cfunc_prod_comp comp_associative2 ysr_type by (typecheck_cfuncs, auto)
         also have "... = mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>p ,successor \<circ>\<^sub>c r\<rangle>,\<langle>q, successor \<circ>\<^sub>c r \<rangle>\<rangle> "
           by (typecheck_cfuncs, smt left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod y_def yr_type)
         also have "... = mult2 \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>p ,successor \<circ>\<^sub>c r\<rangle>, exp_uncurried \<circ>\<^sub>c \<langle>q, successor \<circ>\<^sub>c r \<rangle>\<rangle> "
           using cfunc_cross_prod_comp_cfunc_prod psr_type qsr_type by (typecheck_cfuncs, auto)
         also have "... = (p^\<^sub>\<nat>(successor \<circ>\<^sub>c r)) \<cdot>\<^sub>\<nat>  (q^\<^sub>\<nat>(successor \<circ>\<^sub>c r))"
           by (simp add: exp_def mult_def)
         also have "... = (p \<cdot>\<^sub>\<nat>   (p^\<^sub>\<nat>r)) \<cdot>\<^sub>\<nat> ((q \<cdot>\<^sub>\<nat>  (q^\<^sub>\<nat>r)))"
           by (simp add: exp_respects_successor y_def yr_type)
         also have "... = p \<cdot>\<^sub>\<nat> (  (p^\<^sub>\<nat>r) \<cdot>\<^sub>\<nat> (q \<cdot>\<^sub>\<nat>  (q^\<^sub>\<nat>r)))"
           by (simp add: exp_closure mult_associative mult_closure y_def yr_type)
         also have "... = p \<cdot>\<^sub>\<nat> ((q \<cdot>\<^sub>\<nat>  (q^\<^sub>\<nat>r)) \<cdot>\<^sub>\<nat> (p^\<^sub>\<nat>r))"
           using exp_closure mult_closure mult_commutative y_def yr_type by presburger
         also have "... = p \<cdot>\<^sub>\<nat> (q \<cdot>\<^sub>\<nat>  ((q^\<^sub>\<nat>r) \<cdot>\<^sub>\<nat> (p^\<^sub>\<nat>r)))"
           by (simp add: exp_closure mult_associative y_def yr_type)
         also have "... = p \<cdot>\<^sub>\<nat> (q \<cdot>\<^sub>\<nat>  ((p^\<^sub>\<nat>r) \<cdot>\<^sub>\<nat> (q^\<^sub>\<nat>r)))"
           by (simp add: exp_closure mult_commutative y_def yr_type)
         also have "... = (p \<cdot>\<^sub>\<nat> q)\<cdot>\<^sub>\<nat>  ((p^\<^sub>\<nat>r) \<cdot>\<^sub>\<nat> (q^\<^sub>\<nat>r))"
           by (simp add: exp_closure mult_associative mult_closure y_def yr_type)
         also have "... = mult2 \<circ>\<^sub>c \<langle>mult2  \<circ>\<^sub>c \<langle>p,q\<rangle>  ,mult2 \<circ>\<^sub>c   \<langle>exp_uncurried \<circ>\<^sub>c \<langle>p,r\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>q,r\<rangle>\<rangle>\<rangle>"
           by (simp add: exp_def mult_def)
         also have "... = (mult2 \<circ>\<^sub>c \<langle>mult2  \<circ>\<^sub>c \<langle>p,q\<rangle>  ,mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>p,r\<rangle>,\<langle>q,r\<rangle>\<rangle>\<rangle>) "
           using cfunc_cross_prod_comp_cfunc_prod pr_type qr_type by (typecheck_cfuncs, auto)
         also have "... = (mult2 \<circ>\<^sub>c \<langle>mult2  \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c x  ,mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c x,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c x\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c x,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c x\<rangle>\<rangle>\<rangle>) "
           by (typecheck_cfuncs, smt id_left_unit2 left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod y_def yr_type)
         also have "... = (mult2 \<circ>\<^sub>c \<langle>mult2  \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)   ,mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>) \<circ>\<^sub>c x"
           by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 x_type)
         also have "... = (mult2 \<circ>\<^sub>c \<langle>mult2  \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)   ,eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c F\<rangle>) \<circ>\<^sub>c x"
           by (typecheck_cfuncs, simp add: F_def transpose_func_def)
         also have "... = (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>) \<circ>\<^sub>c F ,eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c F\<rangle>) \<circ>\<^sub>c x"
           using F_def left_cart_proj_cfunc_cross_prod type4 by (typecheck_cfuncs, auto)
         also have "... = (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c F) \<circ>\<^sub>c x" 
           using F_type cfunc_prod_comp comp_associative2 by (typecheck_cfuncs, auto) 
         also have "... = (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle> )\<circ>\<^sub>c F \<circ>\<^sub>c x" 
           using F_type comp_associative2 x_type by (typecheck_cfuncs, auto)
         also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> )\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c x" 
           by (typecheck_cfuncs, simp add: F_def transpose_func_def)
         then show "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
          (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c x"   
           by (typecheck_cfuncs, smt F_def F_type calculation comp_associative2 inv_transpose_func_def2 inv_transpose_of_composition transpose_func_def x_type)
       qed
     qed
   qed
 qed


  have main_result_flat: "exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) = mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
 (right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
 (right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>"
    by (typecheck_cfuncs, metis main_result transpose_func_def)

  have ab_type: "\<langle>a,b\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
    using assms(1) assms(2) cfunc_prod_type by blast
  have abc_type: "\<langle>\<langle>a,b\<rangle>,c\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c"
    by (simp add: ab_type assms(3) cfunc_prod_type)
  have ac_type: "\<langle>a,c\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
    by (simp add: assms(1) assms(3) cfunc_prod_type)
  have bc_type: "\<langle>b,c\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
    by (simp add: assms(2) assms(3) cfunc_prod_type)

  have final_equation: "(a \<cdot>\<^sub>\<nat> b)^\<^sub>\<nat> c = exp_uncurried \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>a,b\<rangle>, c\<rangle>"
    by (simp add: exp_def mult_def)
  also have "... = exp_uncurried \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>a,b\<rangle>, id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c c\<rangle>"
    using assms(3) id_left_unit2 by force
  also have "... = exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
    using ab_type assms(3) cfunc_cross_prod_comp_cfunc_prod by (typecheck_cfuncs, auto)
  also have "... = (exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
    by (typecheck_cfuncs, meson abc_type comp_associative2)
  also have "... = (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
 (right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
 (right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
    by (simp add: main_result_flat)
  also have "... = mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
     (right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
     (right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle> \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
    using abc_type cfunc_type_def comp_associative by (typecheck_cfuncs, fastforce)
  also have "... = mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>,
     (right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>\<rangle>, \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>,
     (right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>\<rangle>\<rangle> "
    using abc_type cfunc_prod_comp comp_associative2 by (typecheck_cfuncs, auto)
  also have "... = mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>a,c\<rangle>, \<langle>b,c\<rangle>\<rangle> "
    by (typecheck_cfuncs, smt assms(1) assms(2) assms(3) left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  also have "... = mult2 \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a,c\<rangle>, exp_uncurried \<circ>\<^sub>c \<langle>b,c\<rangle>\<rangle> "
    using ac_type bc_type cfunc_cross_prod_comp_cfunc_prod by (typecheck_cfuncs, auto)
  also have "... = (a^\<^sub>\<nat> c) \<cdot>\<^sub>\<nat> (b^\<^sub>\<nat> c)"
    by (simp add: exp_def mult_def)
  then show ?thesis
    by (simp add: calculation)
qed







lemma exp_right_dist:
   assumes "a \<in>\<^sub>c  \<nat>\<^sub>c" "b \<in>\<^sub>c  \<nat>\<^sub>c" "c \<in>\<^sub>c  \<nat>\<^sub>c"
   shows "a ^\<^sub>\<nat> (b +\<^sub>\<nat>c) = (a^\<^sub>\<nat> b) \<cdot>\<^sub>\<nat> (a^\<^sub>\<nat> c)"
proof - 
  have bc_type: "\<langle>b,c\<rangle> \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
    by (simp add: assms(2) assms(3) cfunc_prod_type)
  have ab_type: "\<langle>a,b\<rangle> \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
    by (simp add: assms(1) assms(2) cfunc_prod_type)
  have ac_type: "\<langle>a,c\<rangle> \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
    by (simp add: assms(1) assms(3) cfunc_prod_type)
  have abc_type: "\<langle>\<langle>a,b\<rangle>,c\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c"
    by (simp add: ab_type assms(3) cfunc_prod_type)
 have main_result: "(exp_uncurried \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c (associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> = 
    (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c (distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>"
proof(rule natural_number_object_func_unique[where X = "\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>",
       where f = "(mult2 \<circ>\<^sub>c \<langle>(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)), (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c  (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>))\<rangle>)\<^sup>\<sharp>"])
  show type1: "(exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
    by typecheck_cfuncs
  show type2: "(mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
    by typecheck_cfuncs
  show "(mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> : \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup> \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
    by typecheck_cfuncs
  show "(exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero =
    (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero"
  proof(rule same_evals_equal[where Z=one, where X="\<nat>\<^sub>c", where A="\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"])
    show "(exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero \<in>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
      by typecheck_cfuncs
    show "(mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero \<in>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
      by typecheck_cfuncs
    show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero =
    eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero"
    proof(rule one_separator[where X="(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one", where Y="\<nat>\<^sub>c"])
      show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one \<rightarrow> \<nat>\<^sub>c"
        by typecheck_cfuncs
      show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c  distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one \<rightarrow> \<nat>\<^sub>c"
        by typecheck_cfuncs
      show "\<And>x. x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one \<Longrightarrow>
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c  distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x"
      proof - 
        fix x 
        assume x_type: "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one"
        obtain y where x_def: "y \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<and> x = \<langle>y, id one\<rangle>"
          by (typecheck_cfuncs, metis cart_prod_decomp terminal_func_unique x_type)
        obtain p q where y_def: "p \<in>\<^sub>c \<nat>\<^sub>c \<and> q \<in>\<^sub>c \<nat>\<^sub>c \<and> y = \<langle>p,q\<rangle>"
          using cart_prod_decomp x_def by blast
        have x_def2: "x = \<langle>\<langle>p,q\<rangle>, id one\<rangle>"
          by (simp add: x_def y_def)
        have y0_type: "\<langle>y, zero\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c"
          by (simp add: cfunc_prod_type x_def zero_type)

            have  "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x =
                  (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c ((id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f  zero) \<circ>\<^sub>c x)"
              by (typecheck_cfuncs, smt cfunc_type_def comp_associative inv_transpose_func_def2 inv_transpose_of_composition x_type)
            also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>)  \<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c y, zero \<circ>\<^sub>c id one\<rangle>"
              using cfunc_cross_prod_comp_cfunc_prod x_def by (typecheck_cfuncs, auto)
            also have "... = (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)  \<circ>\<^sub>c \<langle>y, zero\<rangle>"
              using id_left_unit2 id_right_unit2 transpose_func_def x_def by (typecheck_cfuncs, auto)
            also have "... = exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>y, zero\<rangle>"
              using cfunc_type_def comp_associative y0_type by (typecheck_cfuncs, fastforce)
            also have "... = exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c  \<langle>p , \<langle>q , zero\<rangle>\<rangle>"
              using associate_right_ap y_def by (typecheck_cfuncs, auto) 
            also have "... = exp_uncurried \<circ>\<^sub>c   \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c p , add2 \<circ>\<^sub>c \<langle>q , zero\<rangle>\<rangle>"
              by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod y_def)
            also have "... = exp_uncurried \<circ>\<^sub>c   \<langle>p , q +\<^sub>\<nat>  zero\<rangle>"
              using add_def id_left_unit2 y_def by (typecheck_cfuncs, auto)
            also have "... =  p ^\<^sub>\<nat> q"
              by (simp add: add_respects_zero_on_right exp_def y_def)
            also have "... = (p ^\<^sub>\<nat> q) \<cdot>\<^sub>\<nat> (p ^\<^sub>\<nat> zero)"
              by (simp add: exp_closure exp_respects_Zero_Left s0_is_right_id y_def)
            also have "... =  mult2 \<circ>\<^sub>c  \<langle>exp_uncurried \<circ>\<^sub>c \<langle>p,q\<rangle>, exp_uncurried \<circ>\<^sub>c \<langle>p,zero\<rangle>\<rangle>"
              using exp_def mult_def by auto
            also have "... =  mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c  \<langle>\<langle>p,q\<rangle>,\<langle>p,zero\<rangle>\<rangle>"
              by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod y_def)
            also have "... =  mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c  distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>p, \<langle>q, zero\<rangle>\<rangle>"
              using distribute_left_ap y_def by (typecheck_cfuncs, auto)
            also have "... =  mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c  distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, zero\<rangle>"
              using associate_right_ap y_def by (typecheck_cfuncs, auto)
            also have "... = (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c  distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)  \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, zero\<rangle>"
              using cfunc_type_def comp_associative y_def by (typecheck_cfuncs, auto)
            also have "... = (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c  distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)  \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero) \<circ>\<^sub>c x"
              by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2 id_type x_def y_def)
            also have "... = ((mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c  distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)  \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero)) \<circ>\<^sub>c x"
              using comp_associative2 x_type by (typecheck_cfuncs, blast)
            also have "... =((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c  distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>)  \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero)) \<circ>\<^sub>c x"
              by (typecheck_cfuncs,simp add: transpose_func_def)
            also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c  distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x"
              by (typecheck_cfuncs, metis inv_transpose_func_def2 inv_transpose_of_composition)  
            then show "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c  distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x"
              by (simp add: calculation)
        qed
      qed
    qed
    show "(exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor =
          (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
    proof(rule same_evals_equal[where Z = "\<nat>\<^sub>c", where X = "\<nat>\<^sub>c", where A = "\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"])
      show "(exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
        by typecheck_cfuncs
      show "(mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
        by typecheck_cfuncs
      show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor =
    eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
      proof(rule one_separator[where X = "(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c", where Y = "\<nat>\<^sub>c"])
        show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
          by typecheck_cfuncs
        show " eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
          by typecheck_cfuncs
        show "\<And>x. x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c x"
        proof - 
          fix x
          assume x_type: "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c"
          obtain y r where x_def: "y \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<and> r \<in>\<^sub>c \<nat>\<^sub>c \<and> x = \<langle>y,r\<rangle>"
            using cart_prod_decomp x_type by blast
          obtain p q where y_def: "p \<in>\<^sub>c \<nat>\<^sub>c  \<and> q \<in>\<^sub>c \<nat>\<^sub>c \<and> y = \<langle>p,q\<rangle>"
            using cart_prod_decomp x_def by blast
          have x_def2: " x = \<langle>\<langle>p,q\<rangle>,r\<rangle>"
            by (simp add: x_def y_def)
          have qr_type: "\<langle>q,r\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
            using cfunc_prod_type x_def y_def by blast  
          have ysr_tye: "\<langle>y, successor\<circ>\<^sub>c r\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c"
            by (simp add: cfunc_prod_type succ_n_type x_def)
          have qsr_type: "\<langle>q, successor\<circ>\<^sub>c r\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
            by (simp add: cfunc_prod_type succ_n_type x_def y_def)
          obtain g where g_def: "g =id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
            by simp

                have "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
                      ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f  successor)) \<circ>\<^sub>c x"
                  by (typecheck_cfuncs, metis inv_transpose_func_def2 inv_transpose_of_composition)
                also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle> id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c y, successor\<circ>\<^sub>c r\<rangle>"
                  by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod cfunc_type_def comp_associative x_def x_type)
                also have "... = (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>y, successor\<circ>\<^sub>c r\<rangle>" 
                  using id_left_unit2 transpose_func_def x_def by (typecheck_cfuncs, auto)
                also have "... = exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>y, successor\<circ>\<^sub>c r\<rangle>" 
                  using cfunc_type_def comp_associative ysr_tye by (typecheck_cfuncs, fastforce)
                also have "... = exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c  \<langle>p,\<langle>q, successor\<circ>\<^sub>c r\<rangle>\<rangle>" 
                  using associate_right_ap x_def y_def by (typecheck_cfuncs, auto)
                also have "... = exp_uncurried \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c p ,add2 \<circ>\<^sub>c \<langle>q, successor\<circ>\<^sub>c r\<rangle>\<rangle>" 
                  using cfunc_cross_prod_comp_cfunc_prod qsr_type y_def by (typecheck_cfuncs,auto)
                also have "... = exp_uncurried \<circ>\<^sub>c \<langle>p ,add2 \<circ>\<^sub>c \<langle>q, successor\<circ>\<^sub>c r\<rangle>\<rangle>" 
                  using id_left_unit2 y_def by (typecheck_cfuncs, auto)
                also have "... = p^\<^sub>\<nat> (q +\<^sub>\<nat> (successor\<circ>\<^sub>c r))"
                  by (simp add: add_def exp_def) 
                also have "... = p^\<^sub>\<nat> (successor\<circ>\<^sub>c (q +\<^sub>\<nat>  r))"
                  by (simp add: add_respects_succ1 x_def y_def)
                also have "... = (p^\<^sub>\<nat>(q +\<^sub>\<nat> r))  \<cdot>\<^sub>\<nat> p"
                  by (simp add: add_type exp_closure exp_respects_successor mult_commutative x_def y_def)
              also have "... = mult2 \<circ>\<^sub>c \<langle>exp_uncurried  \<circ>\<^sub>c \<langle>p, add2 \<circ>\<^sub>c \<langle>q,r\<rangle>\<rangle>, p\<rangle>"
                by (simp add: add_def exp_def mult_def)
              also have "... = mult2 \<circ>\<^sub>c \<langle>exp_uncurried  \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c p, add2 \<circ>\<^sub>c \<langle>q,r\<rangle>\<rangle>, p\<rangle>"
                using id_left_unit2 y_def by (typecheck_cfuncs, auto)
              also have "... = mult2 \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c \<langle>p, \<langle>q,r\<rangle>\<rangle>, p\<rangle>"
                using cfunc_cross_prod_comp_cfunc_prod qr_type y_def by (typecheck_cfuncs, auto)
              also have "... = mult2 \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c x,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c x\<rangle>"
                by (typecheck_cfuncs, smt associate_right_ap id_left_unit2 left_cart_proj_cfunc_prod x_def y_def)
              also have "... = mult2 \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>  \<circ>\<^sub>c x"
                using cfunc_prod_comp comp_associative2 x_type by (typecheck_cfuncs, auto)
              also have "... = (mult2 \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle> ) \<circ>\<^sub>c x"
                using comp_associative2 x_type by (typecheck_cfuncs, blast)
              also have "... = (mult2 \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>) \<circ>\<^sub>c g\<rangle> ) \<circ>\<^sub>c x"
                using type1  g_def left_cart_proj_cfunc_cross_prod by (typecheck_cfuncs, auto)
              also have "... = (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c g,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>) \<circ>\<^sub>c g\<rangle> ) \<circ>\<^sub>c x"
                by (typecheck_cfuncs, simp add: g_def transpose_func_def)
              also have "... = (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle> \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>)) \<circ>\<^sub>c x"
                by (typecheck_cfuncs, smt \<open>(mult2 \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c x = (mult2 \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>) \<circ>\<^sub>c g\<rangle>) \<circ>\<^sub>c x\<close> \<open>(mult2 \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>) \<circ>\<^sub>c g\<rangle>) \<circ>\<^sub>c x = (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c g,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>) \<circ>\<^sub>c g\<rangle>) \<circ>\<^sub>c x\<close> cfunc_prod_comp comp_associative2 left_cart_proj_cfunc_cross_prod transpose_func_def)
              also have "... = ((mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>)) \<circ>\<^sub>c x"
                using comp_associative2 by (typecheck_cfuncs, auto)
              also have "... = ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>)) \<circ>\<^sub>c x"
                by (typecheck_cfuncs, simp add: transpose_func_def)
              also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c x"
                by (typecheck_cfuncs, smt inv_transpose_func_def2 inv_transpose_of_composition)
              then show " (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c x"
                by (simp add: calculation)
            qed
          qed
        qed
      show "(mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor =
    (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
    proof(rule same_evals_equal[where Z = "\<nat>\<^sub>c", where X = "\<nat>\<^sub>c", where A = "\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"])
      show "(mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
        by typecheck_cfuncs
      show "(mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
        by typecheck_cfuncs
      show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor =
    eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
      proof(rule one_separator[where X = "(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c", where Y = "\<nat>\<^sub>c"])
        show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
          by typecheck_cfuncs
        show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
          by typecheck_cfuncs
        show "\<And>x. x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c x"
        proof - 
          fix x
          assume x_type: "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c"
          obtain y r where x_def: "y \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<and> r \<in>\<^sub>c \<nat>\<^sub>c \<and> x = \<langle>y,r\<rangle>"
            using cart_prod_decomp x_type by blast
          obtain p q where y_def: "p \<in>\<^sub>c \<nat>\<^sub>c  \<and> q \<in>\<^sub>c \<nat>\<^sub>c \<and> y = \<langle>p,q\<rangle>"
            using cart_prod_decomp x_def by blast
          have x_def2: " x = \<langle>\<langle>p,q\<rangle>,r\<rangle>"
            by (simp add: x_def y_def)
          have pqr_type: "\<langle>p,\<langle>q,r\<rangle>\<rangle>  \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
            by (simp add: cfunc_prod_type x_def y_def)
          have qr_type: "\<langle>q,r\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
            using cfunc_prod_type x_def y_def by blast  
          have ysr_tye: "\<langle>y, successor\<circ>\<^sub>c r\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c"
            by (simp add: cfunc_prod_type succ_n_type x_def)
          have qsr_type: "\<langle>q, successor\<circ>\<^sub>c r\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
            by (simp add: cfunc_prod_type succ_n_type x_def y_def)
          have pq_type: "\<langle>p,q\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
            by (simp add: cfunc_prod_type x_def y_def)
          have pr_type: "\<langle>p,r\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
            by (simp add: cfunc_prod_type x_def y_def)
          have psr_type: "\<langle>p, successor\<circ>\<^sub>c r\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
            by (simp add: cfunc_prod_type succ_n_type x_def y_def)
          obtain g where g_def: "g = id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
            by simp

          have "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x = 
         ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor)) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, metis inv_transpose_func_def2 inv_transpose_of_composition)
          also have "... =  ((mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor)) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, simp add: transpose_func_def)
          also have "... =  (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor) \<circ>\<^sub>c x"
            using comp_associative2 x_type by (typecheck_cfuncs, auto)
          also have "... =  (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c y ,successor \<circ>\<^sub>c r\<rangle>"
            using cfunc_cross_prod_comp_cfunc_prod x_def by (typecheck_cfuncs, auto)
          also have "... =  (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>y ,successor \<circ>\<^sub>c r\<rangle>"
            using id_left_unit2 x_def by (typecheck_cfuncs, auto)
          also have "... =   mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>y ,successor \<circ>\<^sub>c r\<rangle>"
            using comp_associative2 ysr_tye by (typecheck_cfuncs, auto)
          also have "... =   mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>p,\<langle>q ,successor \<circ>\<^sub>c r\<rangle>\<rangle>"
            using associate_right_ap x_def y_def by (typecheck_cfuncs, auto)
          also have "... =   mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c  \<langle>\<langle>p ,q\<rangle>,\<langle>p ,successor \<circ>\<^sub>c r\<rangle>\<rangle>"
            using distribute_left_ap x_def y_def by (typecheck_cfuncs, auto)
          also have "... =   mult2 \<circ>\<^sub>c   \<langle>exp_uncurried \<circ>\<^sub>c  \<langle>p ,q\<rangle>,exp_uncurried \<circ>\<^sub>c  \<langle>p ,successor \<circ>\<^sub>c r\<rangle>\<rangle>"
            by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod psr_type y_def)
          also have "... =    (p^\<^sub>\<nat>q) \<cdot>\<^sub>\<nat> (p^\<^sub>\<nat> (successor \<circ>\<^sub>c r))"
            by (simp add: exp_def mult_def)
          also have "... = (p ^\<^sub>\<nat> q) \<cdot>\<^sub>\<nat> ((p ^\<^sub>\<nat> r) \<cdot>\<^sub>\<nat> p )"
            by (simp add: exp_closure exp_respects_successor mult_commutative x_def y_def)
          also have "... = ((p ^\<^sub>\<nat> q) \<cdot>\<^sub>\<nat> (p ^\<^sub>\<nat> r)) \<cdot>\<^sub>\<nat> p "
            by (simp add: exp_closure mult_associative x_def y_def)
          also have "... = mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c  \<langle>exp_uncurried \<circ>\<^sub>c \<langle>p,q\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>p,r\<rangle>\<rangle> ,p\<rangle>"
            by (simp add: exp_def mult_def)
          also have "... = mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c  \<langle>\<langle>p,q\<rangle>,\<langle>p,r\<rangle>\<rangle> ,p\<rangle>"
            using cfunc_cross_prod_comp_cfunc_prod pq_type pr_type by (typecheck_cfuncs, auto)
          also have "... = mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>p,\<langle>q,r\<rangle>\<rangle> ,p\<rangle>"
            using distribute_left_ap x_def y_def by (typecheck_cfuncs, auto)
          also have "... = mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c x ,p\<rangle>"
            using associate_right_ap x_def y_def by (typecheck_cfuncs, auto)
          also have "... = mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c x ,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c  \<circ>\<^sub>c x\<rangle>"
            by (typecheck_cfuncs, metis id_left_unit2 left_cart_proj_cfunc_prod x_def y_def)
          also have "... = mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c ,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>   \<circ>\<^sub>c x"
            using cfunc_prod_comp comp_associative2 x_type by (typecheck_cfuncs, auto)
          also have "... = (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c ,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>  ) \<circ>\<^sub>c x"
            using comp_associative2 x_type by (typecheck_cfuncs, blast)
          also have "... = (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c g ,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<circ>\<^sub>c g \<rangle>  ) \<circ>\<^sub>c x"
            using g_def left_cart_proj_cfunc_cross_prod transpose_func_def type2 by (typecheck_cfuncs, auto)
          also have "... = ((mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>)) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, smt cfunc_prod_comp cfunc_type_def comp_associative g_def)
          also have "... = ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>)) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, simp add: transpose_func_def)
          also have "... =  (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, smt inv_transpose_func_def2 inv_transpose_of_composition)
          then show "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c x"
            by (simp add: calculation)
        qed
      qed
    qed
  qed

  have main_result_flat: "exp_uncurried \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c (associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) = 
    mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c (distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)"
  by (typecheck_cfuncs, metis flat_cancels_sharp main_result)

  have final_eqn: "a ^\<^sub>\<nat> (b +\<^sub>\<nat>c) = exp_uncurried \<circ>\<^sub>c \<langle>a, add2 \<circ>\<^sub>c \<langle>b,c\<rangle>\<rangle>"
    by (simp add: add_def exp_def)
  also have "... = exp_uncurried \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c \<langle>a,\<langle>b,c\<rangle>\<rangle>"
    using assms(1) bc_type cfunc_cross_prod_comp_cfunc_prod id_left_unit2 by (typecheck_cfuncs, auto)
  also have "... = exp_uncurried \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c  (associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
    using assms associate_right_ap by auto
  also have "... = (exp_uncurried \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c  (associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
    using abc_type cfunc_type_def comp_associative by (typecheck_cfuncs, auto)
  also have "... = (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c (distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
    by (simp add: main_result_flat)
  also have "... = mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c (distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
    using abc_type comp_associative2 by (typecheck_cfuncs, auto)
  also have "... = mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c (distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c  \<langle>a, \<langle>b,c\<rangle>\<rangle>"
    using assms associate_right_ap by auto
  also have "... = mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried)  \<circ>\<^sub>c  \<langle>\<langle>a,b\<rangle>, \<langle>a,c\<rangle>\<rangle>"
    using assms distribute_left_ap by auto
  also have "... = mult2 \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a,b\<rangle>, exp_uncurried \<circ>\<^sub>c \<langle>a,c\<rangle>\<rangle>"
    using ab_type ac_type cfunc_cross_prod_comp_cfunc_prod by (typecheck_cfuncs, auto)
  also have "... = (a^\<^sub>\<nat> b) \<cdot>\<^sub>\<nat> (a^\<^sub>\<nat> c)"
    by (simp add: exp_def mult_def)
  then show ?thesis using calculation by auto
qed

lemma power_rule:
   assumes "a \<in>\<^sub>c  \<nat>\<^sub>c" "b \<in>\<^sub>c  \<nat>\<^sub>c" "c \<in>\<^sub>c  \<nat>\<^sub>c"
   shows "(a ^\<^sub>\<nat> b)^\<^sub>\<nat> c = (a^\<^sub>\<nat> (b \<cdot>\<^sub>\<nat> c))"
proof- 
  have main_result: "(exp_uncurried \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f id(\<nat>\<^sub>c)))\<^sup>\<sharp>  =  
                     ((exp_uncurried \<circ>\<^sub>c (id(\<nat>\<^sub>c) \<times>\<^sub>f mult2)) \<circ>\<^sub>c (associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>"
  proof(rule natural_number_object_func_unique[where X = "\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>",
 where f = "(mult2 \<circ>\<^sub>c \<langle>(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)), exp_uncurried \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>))\<rangle>)\<^sup>\<sharp>"])
    show "(exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
      by typecheck_cfuncs
    show "((exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
      by typecheck_cfuncs
    show "(mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),exp_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> : \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup> \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
      by typecheck_cfuncs
    show "(exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero =
    ((exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero"
    proof(rule same_evals_equal[where Z = one, where X = "\<nat>\<^sub>c", where A = "\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"])
      show "(exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero \<in>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
        by typecheck_cfuncs
      show "((exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero \<in>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
        by typecheck_cfuncs
      show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero =
    eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f ((exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero"
      proof(rule one_separator[where X = "(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one", where Y = "\<nat>\<^sub>c"])
        show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one \<rightarrow> \<nat>\<^sub>c"
          by typecheck_cfuncs
        show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f ((exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one \<rightarrow> \<nat>\<^sub>c"
          by typecheck_cfuncs
        show "\<And>x. x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one \<Longrightarrow>
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f ((exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x"
        proof - 
          fix x 
          assume x_type: "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one"
          then have "\<exists>mn. mn \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<and> x = \<langle>mn, id one\<rangle>"
            by (typecheck_cfuncs, metis cart_prod_decomp terminal_func_unique)
          then obtain mn where x_def: "mn \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<and> x = \<langle>mn, id one\<rangle>"
            by blast
          then obtain m n where mn_def: "m \<in>\<^sub>c \<nat>\<^sub>c \<and> n \<in>\<^sub>c \<nat>\<^sub>c \<and> mn = \<langle>m,n\<rangle>"
            using cart_prod_decomp x_def by (typecheck_cfuncs, blast)
          then have x_def2: "x = \<langle>\<langle>m,n\<rangle>, id one\<rangle>"
            by (simp add: x_def)
          have mn0_type: "\<langle>\<langle>m,n\<rangle>, zero\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c"
            by (simp add: cfunc_prod_type mn_def zero_type)
          have mn0_type2: "\<langle>m, \<langle>n, zero\<rangle>\<rangle> \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)" 
            by (simp add: cfunc_prod_type mn_def zero_type)
          have "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x = 
                ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, metis inv_transpose_func_def2 inv_transpose_of_composition)
          also have "... = ((exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, simp add: transpose_func_def)
          also have "... = (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero) \<circ>\<^sub>c \<langle>mn, id one\<rangle>"
            by (typecheck_cfuncs, metis comp_associative2 x_def)
          also have "... = (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c    \<langle>id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c mn,zero \<circ>\<^sub>c id one\<rangle>"
            using cfunc_cross_prod_comp_cfunc_prod x_def by (typecheck_cfuncs, auto)
          also have "... = (exp_uncurried \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c    \<langle> \<langle>m,n\<rangle> ,zero\<rangle>"
            by (typecheck_cfuncs, metis id_left_unit2 id_right_unit2 mn_def)
          also have "... = exp_uncurried \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c   \<langle> \<langle>m,n\<rangle> ,zero\<rangle>"
            using comp_associative2 mn0_type by (typecheck_cfuncs, auto)
          also have "... = exp_uncurried \<circ>\<^sub>c  \<langle>exp_uncurried \<circ>\<^sub>c \<langle>m,n\<rangle> ,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  zero\<rangle>" 
            by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod mn_def)
          also have "... = exp_uncurried \<circ>\<^sub>c  \<langle>exp_uncurried \<circ>\<^sub>c \<langle>m,n\<rangle> ,zero\<rangle>"
            using id_left_unit2 zero_type by auto
          also have "... = (m ^\<^sub>\<nat> n) ^\<^sub>\<nat> zero"
            by (simp add: exp_def)
          also have "... =  m ^\<^sub>\<nat> zero"
            by (simp add: exp_closure exp_respects_Zero_Left mn_def)
          also have "... = m ^\<^sub>\<nat> (n \<cdot>\<^sub>\<nat> zero)"
            by (simp add: mn_def mult_respects_zero_right)
          also have "... = exp_uncurried \<circ>\<^sub>c \<langle>m, mult2 \<circ>\<^sub>c\<langle>n, zero\<rangle>\<rangle>"
            by (simp add: exp_def mult_def)
          also have "... = exp_uncurried \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m, mult2 \<circ>\<^sub>c\<langle>n, zero\<rangle>\<rangle>"
            using id_left_unit2 mn_def by auto
          also have "... = exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c  \<langle>m,\<langle>n, zero\<rangle>\<rangle>"
            by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod mn_def)
          also have "... = (exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c  \<langle>m,\<langle>n, zero\<rangle>\<rangle>"
            using comp_associative2 mn0_type2 by (typecheck_cfuncs, blast)
          also have "... = (exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  \<langle> \<langle>m,n\<rangle>, zero\<rangle>"
           using associate_right_ap mn_def by (typecheck_cfuncs, auto)
          also have "... = (exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c  \<langle>m,n\<rangle>, zero \<circ>\<^sub>c id one\<rangle>"
            by (typecheck_cfuncs, metis id_left_unit2 id_right_unit2 mn_def)
          also have "... = (exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod mn_def x_def)
          also have "... = ((exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero) \<circ>\<^sub>c x"
            using comp_associative2 x_type by (typecheck_cfuncs, blast)
          also have "... =  ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f ((exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero)) \<circ>\<^sub>c x"
            using comp_associative2 transpose_func_def x_type by (typecheck_cfuncs, auto)
          also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f ((exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x" 
            by (typecheck_cfuncs, metis inv_transpose_func_def2 inv_transpose_of_composition)
          then show "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x =
                     (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f ((exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x"
            by (simp add: calculation)
        qed
      qed
    qed
    show "(exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor =
    (mult2 \<circ>\<^sub>c
     \<langle>eval_func \<nat>\<^sub>c
       (\<nat>\<^sub>c \<times>\<^sub>c
        \<nat>\<^sub>c),exp_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
    (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
    proof(rule same_evals_equal[where Z = "\<nat>\<^sub>c", where X = "\<nat>\<^sub>c", where A = "\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"])
      show "(exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
        by typecheck_cfuncs
      show "(mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),exp_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
        by typecheck_cfuncs
      show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor =
            eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),exp_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
      proof(rule one_separator[where X = "(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c", where Y = "\<nat>\<^sub>c"])
        show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
          by typecheck_cfuncs
        show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),exp_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c(exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
          by typecheck_cfuncs
        show "\<And>x. x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),exp_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c x"
        proof -
          fix x 
          assume x_type: "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c"
          then have x_def: "\<exists>y t . y \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<and> t \<in>\<^sub>c \<nat>\<^sub>c \<and> x = \<langle>y,t\<rangle>"
            using cart_prod_decomp by blast
          then obtain y t where x_def: "y \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<and> t \<in>\<^sub>c \<nat>\<^sub>c \<and> x = \<langle>y,t\<rangle>"
            by blast
          then have y_exists: "\<exists>m n. m \<in>\<^sub>c \<nat>\<^sub>c \<and> n \<in>\<^sub>c \<nat>\<^sub>c \<and> y = \<langle>m,n\<rangle>"
            using cart_prod_decomp by blast
          then obtain m n where y_def: "m \<in>\<^sub>c \<nat>\<^sub>c \<and> n \<in>\<^sub>c \<nat>\<^sub>c \<and> y = \<langle>m,n\<rangle>"
            by blast
          then have x_def2: "x = \<langle>\<langle>m,n\<rangle>,t\<rangle>"
            by (simp add: x_def)
          have yst_type: "\<langle>y,successor \<circ>\<^sub>c t\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c"
            by (simp add: cfunc_prod_type succ_n_type x_def)


          have "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),exp_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c x =  
               ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),exp_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f  (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>)) \<circ>\<^sub>c x"
            apply typecheck_cfuncs
            by (metis inv_transpose_func_def2 inv_transpose_of_composition)
          also have "... = ((mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),exp_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f  (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>)) \<circ>\<^sub>c x"
            apply typecheck_cfuncs
            by (simp add: transpose_func_def)
          also have "... = (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),exp_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>) \<circ>\<^sub>c ((id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f  (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c x)"
            apply typecheck_cfuncs
            using comp_associative2 x_type by auto
          also have "... = mult2 \<circ>\<^sub>c (\<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),exp_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle> \<circ>\<^sub>c ((id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f  (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>)) \<circ>\<^sub>c x)"
            apply typecheck_cfuncs
            by (metis cfunc_type_def comp_associative x_type)
          also have "... = mult2 \<circ>\<^sub>c (\<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),exp_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle> \<circ>\<^sub>c ((id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f  (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>)) \<circ>\<^sub>c x)"
            oops


(*
          have "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
                ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor)) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, metis inv_transpose_func_def2 inv_transpose_of_composition)
          also have "... = ((exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor)) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, simp add: transpose_func_def)
          also have "... = (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor) \<circ>\<^sub>c \<langle>y,t\<rangle>"
            by (typecheck_cfuncs, metis comp_associative2 x_def)
          also have "... =  (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c y,successor \<circ>\<^sub>c t\<rangle>"
            using cfunc_cross_prod_comp_cfunc_prod x_def by (typecheck_cfuncs, auto)
          also have "... =  (exp_uncurried \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>y,successor \<circ>\<^sub>c t\<rangle>"
            using id_left_unit2 x_def by (typecheck_cfuncs, auto)
          also have "... =  exp_uncurried \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)  \<circ>\<^sub>c \<langle>y,successor \<circ>\<^sub>c t\<rangle>"
            using comp_associative2 yst_type by (typecheck_cfuncs, auto)
          also have "... =  exp_uncurried \<circ>\<^sub>c   \<langle>exp_uncurried \<circ>\<^sub>c  y,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (successor \<circ>\<^sub>c t)\<rangle>"
            by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod x_def)
          also have "... =  exp_uncurried \<circ>\<^sub>c   \<langle>exp_uncurried \<circ>\<^sub>c  y, (successor \<circ>\<^sub>c t)\<rangle>"
            using id_left_unit2 x_def by (typecheck_cfuncs, fastforce)
          also have "... = (m ^\<^sub>\<nat> n) ^\<^sub>\<nat> (successor \<circ>\<^sub>c t)"
            by (simp add: exp_def y_def)
          *)


end