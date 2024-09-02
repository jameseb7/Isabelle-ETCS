theory Exp
  imports Mult
begin

(*Defining exponentiation on N*)

definition exp_curried :: "cfunc" where
   "exp_curried = (THE w. w: \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<and>
    w \<circ>\<^sub>c zero =  ((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp>) \<and>
    w \<circ>\<^sub>c successor = ((mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c w)"

lemma exp_curried_property: "(exp_curried: \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<and>
    exp_curried \<circ>\<^sub>c zero =  ((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp>) \<and>
    exp_curried \<circ>\<^sub>c successor = ((mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c exp_curried)"
  unfolding exp_curried_def
  by (rule theI', typecheck_cfuncs, smt (verit, best) natural_number_object_property2)


lemma exp_curried_type[type_rule]: "exp_curried: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
  by (simp add: exp_curried_property)
 
lemma exp_curried_0_eq: "exp_curried \<circ>\<^sub>c zero = ((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp>)"
  using exp_curried_property by blast


lemma exp_curried_comp_succ_eq: "exp_curried \<circ>\<^sub>c successor = ((mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c exp_curried"
  by (simp add: exp_curried_property)


definition exp_uncurried :: "cfunc"
  where "exp_uncurried = eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f exp_curried)"

lemma exp_uncurried_type[type_rule]: "exp_uncurried: \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
  unfolding exp_uncurried_def by typecheck_cfuncs

definition exp :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" (infixl "^\<^sub>\<nat>" 75)
  where "m ^\<^sub>\<nat> n = exp_uncurried \<circ>\<^sub>c \<langle>m, n\<rangle>"

lemma exp_uncurried_apply:
  assumes "m : X \<rightarrow> \<nat>\<^sub>c" "n : X \<rightarrow> \<nat>\<^sub>c"
  shows "exp_uncurried \<circ>\<^sub>c \<langle>m, n\<rangle> = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, exp_curried \<circ>\<^sub>c n\<rangle>"
  unfolding exp_def  exp_uncurried_def
  using assms by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod comp_associative2 id_left_unit2)

lemma exp_def2:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "m ^\<^sub>\<nat> n = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, exp_curried \<circ>\<^sub>c n\<rangle>"
  unfolding exp_def exp_uncurried_def
  using assms exp_uncurried_apply exp_uncurried_def by auto

lemma exp_apply1:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "m ^\<^sub>\<nat> n = exp_uncurried \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<circ>\<^sub>c n"
  unfolding add_def 
proof - 
  have "exp_uncurried \<circ>\<^sub>c \<langle>m,n\<rangle> = exp_uncurried \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c id \<one>, id \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>"
    by (metis assms cfunc_type_def id_left_unit id_right_unit)
  also have "... = exp_uncurried \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c n), id \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>"
    by (metis assms(2) comp_type id_type one_unique_element terminal_func_type)
  also have "... = exp_uncurried \<circ>\<^sub>c \<langle>(m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c n, id \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>"
    using assms by (typecheck_cfuncs, simp add: comp_associative2)
  also have "... = exp_uncurried \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<circ>\<^sub>c n"
    using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp)
  then show ?thesis
    by (simp add: calculation exp_def)
qed

lemma exp_apply1_left:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "m ^\<^sub>\<nat> n = exp_uncurried \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c m"
  unfolding add_def 
proof - 
  have "exp_uncurried \<circ>\<^sub>c \<langle>m,n\<rangle> = exp_uncurried \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c \<circ>\<^sub>c m, n \<circ>\<^sub>c id \<one>\<rangle>"
    by (metis assms cfunc_type_def id_left_unit id_right_unit)
  also have "... = exp_uncurried \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c \<circ>\<^sub>c m, n \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m)\<rangle>"
    by (metis assms(1) comp_type id_type one_unique_element terminal_func_type)
  also have "... = exp_uncurried \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c \<circ>\<^sub>c m, (n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c m\<rangle>"
    using assms by (typecheck_cfuncs, simp add: comp_associative2)
  also have "... = exp_uncurried \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<rangle> \<circ>\<^sub>c m"
    using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp) 
  then show ?thesis
    by (simp add: calculation exp_def)
qed

lemma exp_respects_zero_left_elfree:
  "exp_uncurried  \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> = successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
proof -
  have "exp_uncurried  \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, exp_curried \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
    using exp_uncurried_apply   terminal_func_comp  by (typecheck_cfuncs, auto)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, ((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp>)  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
    by (typecheck_cfuncs, simp add: comp_associative2 exp_curried_0_eq)
  also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
    by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
  also have "... = successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<one>  \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
    by (typecheck_cfuncs, smt comp_associative2 flat_cancels_sharp inv_transpose_func_def3)
  also have "... = successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
    by (metis id_type right_cart_proj_cfunc_prod terminal_func_type)
then show ?thesis
    by (simp add: calculation)
qed

lemma exp_closure[type_rule]:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "m ^\<^sub>\<nat> n \<in>\<^sub>c \<nat>\<^sub>c"
  unfolding exp_def
  using assms by typecheck_cfuncs

lemma exp_respects_Zero_Left:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "n ^\<^sub>\<nat> zero = successor \<circ>\<^sub>c zero"
proof - 
  have "n ^\<^sub>\<nat> zero = exp_uncurried  \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c n"
    by (simp add: assms exp_apply1_left zero_type)
  also have "... = successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c n"
    using assms by (typecheck_cfuncs, simp add: comp_associative2 exp_respects_zero_left_elfree)
  also have "... =  successor \<circ>\<^sub>c zero"
    using assms by (typecheck_cfuncs, simp add: id_right_unit2 terminal_func_comp_elem)
 then show ?thesis
   by (simp add: calculation)
qed

(*Notice, in particular that 0^0 = 1*)


(*
lemma exp_respects_one_right_elfree:
  "exp_uncurried  \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> = id\<^sub>c \<nat>\<^sub>c"
proof - 
  have type1: "((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp>)\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
    using cfunc_type_def codomain_comp compatible_comp_ETCS_func domain_comp s0b_type s0projSharp_type zero_type by auto
  have type2: "\<langle>id\<^sub>c \<nat>\<^sub>c, ((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp>)\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<times>\<^sub>c(\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)"
    by (simp add: cfunc_prod_type id_type type1)
  have "exp_uncurried  \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> =
eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, ((mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>cexp_curried \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<rangle>"
    by (metis comp_associative exp_curried_comp_succ_eq exp_uncurried_apply id_type s0b_type)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, (mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c ((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp>) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
    by (simp add: comp_associative exp_curried_0_eq)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c, (mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c ((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp>) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
    by (metis id_domain id_right_unit)
  also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp>)\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
    using comp_associative comp_type exp_curried_0_eq exp_curried_type zero_betaN_type mult_pie_sharp_type id_type
    apply(subst cfunc_cross_prod_comp_cfunc_prod[where A="\<nat>\<^sub>c", where W = "\<nat>\<^sub>c", where X="\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>",where Y="\<nat>\<^sub>c", where Z= "\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"])
    using id_type apply auto[1]
    apply (metis comp_associative comp_type exp_curried_0_eq exp_curried_type zero_betaN_type)
    using mult_pie_sharp_type apply blast
    by simp
  also have "... =  mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp>)\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
    using comp_associative mult_pie_type transpose_func_def by auto
  also have "... =  mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp>)\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp>)\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle> "
    apply(subst cfunc_prod_comp[where X = "\<nat>\<^sub>c", where Y = "\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>", where A ="\<nat>\<^sub>c", where B = "\<nat>\<^sub>c"])
    apply (metis cfunc_prod_type comp_associative comp_type exp_curried_0_eq exp_curried_type id_type zero_betaN_type)
    apply (simp add: left_cart_proj_type)
    apply (simp add: eval_func_type)
    by simp
  also have "... =  mult2 \<circ>\<^sub>c\<langle>id\<^sub>c \<nat>\<^sub>c,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp>)\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle> "
    by (metis id_type left_cart_proj_cfunc_prod type1)
  also have "... =  mult2 \<circ>\<^sub>c\<langle>id\<^sub>c \<nat>\<^sub>c,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle> "
    by (smt cfunc_cross_prod_comp_cfunc_prod id_right_unit2 id_type s0projSharp_type terminal_func_type)
  also have "... =  mult2 \<circ>\<^sub>c\<langle>id\<^sub>c \<nat>\<^sub>c, successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<one> \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle> "
    using comp_associative s0proj_type transpose_func_def by presburger
  also have "... =  mult2 \<circ>\<^sub>c\<langle>id\<^sub>c \<nat>\<^sub>c, successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> "
    by (metis (no_types) id_type right_cart_proj_cfunc_prod terminal_func_type)
(*At this point we need the result from multiplication*)
*)

lemma exp_respects_one_right:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "n ^\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = n" 
proof -
  have "n ^\<^sub>\<nat> (successor \<circ>\<^sub>c zero) =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n, exp_curried \<circ>\<^sub>c(successor \<circ>\<^sub>c zero) \<rangle>"
    using assms comp_type exp_def2 successor_type zero_type by blast
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n, ((mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>cexp_curried \<circ>\<^sub>c zero \<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_type_def comp_associative exp_curried_comp_succ_eq)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n, ((mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c ((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp>)\<rangle>"
    by (simp add: exp_curried_0_eq)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c n, ((mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c ((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp>)\<rangle>"
    using assms id_left_unit2 by auto
  also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ((mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>n,((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp>)\<rangle>"
    using assms cfunc_cross_prod_comp_cfunc_prod by (typecheck_cfuncs, auto)
  also have "... = mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>n,((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp>)\<rangle>"
    using assms by (typecheck_cfuncs, simp add: comp_associative2 transpose_func_def)
  also have "... = mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c \<langle>n,((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp>)\<rangle>,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp>)\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp)
  also have "... =  mult2 \<circ>\<^sub>c \<langle>n ,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp>)\<rangle>\<rangle>"
    using assms left_cart_proj_cfunc_prod by (typecheck_cfuncs, presburger)
  also have "... = mult2 \<circ>\<^sub>c\<langle>n ,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c n,((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp>) \<circ>\<^sub>c id\<^sub>c \<one>  \<rangle>\<rangle>"
    using assms id_left_unit2 id_right_unit2  by (typecheck_cfuncs, auto)
  also have "... = mult2 \<circ>\<^sub>c \<langle>n ,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ((successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<one>)\<^sup>\<sharp>))\<circ>\<^sub>c \<langle>n, id\<^sub>c \<one> \<rangle>\<rangle>"
    by (typecheck_cfuncs, smt assms cfunc_cross_prod_comp_cfunc_prod)
  also have "... = mult2 \<circ>\<^sub>c \<langle>n ,successor \<circ>\<^sub>c zero \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<one> \<circ>\<^sub>c \<langle>n, id\<^sub>c \<one>  \<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: comp_associative2 transpose_func_def)
  also have "... = mult2 \<circ>\<^sub>c \<langle>n ,successor \<circ>\<^sub>c zero \<circ>\<^sub>c id\<^sub>c \<one> \<rangle>"
    by (metis (no_types) assms id_type right_cart_proj_cfunc_prod)
  also have "... = n"
    using assms id_right_unit2 mult_def s0_is_right_id zero_type by auto
  then show ?thesis
    using calculation by auto
qed

lemma exp_respects_zero_left:
  assumes n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "zero ^\<^sub>\<nat> (successor \<circ>\<^sub>c n) = zero" 
proof - 
  have main_result: "zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> = exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, successor\<rangle>"
  proof(etcs_rule natural_number_object_func_unique[where X = "\<nat>\<^sub>c", where f = "zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"])
    show "(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero = (exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>) \<circ>\<^sub>c zero"
    proof - 
      have "(exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>) \<circ>\<^sub>c zero =  exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle> \<circ>\<^sub>c zero"
        by (typecheck_cfuncs, simp add: comp_associative2)
      also have "... = exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<circ>\<^sub>c zero ,successor \<circ>\<^sub>c zero\<rangle>"
        using cfunc_prod_comp comp_associative2 by(typecheck_cfuncs, auto)
      also have "... = exp_uncurried \<circ>\<^sub>c \<langle>zero ,successor \<circ>\<^sub>c zero\<rangle>"
        by (metis cfunc_type_def id_right_unit id_type one_unique_element terminal_func_comp terminal_func_type zero_type)
      also have "... = zero"
        using exp_def exp_respects_one_right zero_type by auto
      also have "... = (zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero"
        by (typecheck_cfuncs, metis comp_associative2 id_right_unit2 terminal_func_comp_elem)
      then show ?thesis using calculation by auto
    qed
    show "(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor = (zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
      by(etcs_rule one_separator[where X = "\<nat>\<^sub>c", where Y = "\<nat>\<^sub>c"], typecheck_cfuncs, smt comp_associative2 terminal_func_comp)

    show "(exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>) \<circ>\<^sub>c successor = (zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>"
    proof(etcs_rule one_separator[where X = "\<nat>\<^sub>c", where Y = "\<nat>\<^sub>c"])
      show "\<And>x. x \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>((exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>) \<circ>\<^sub>c  successor) \<circ>\<^sub>c x = ((zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>) \<circ>\<^sub>c x"
      proof - 
        fix x 
        assume x_type[type_rule]: "x \<in>\<^sub>c \<nat>\<^sub>c"
        have "(exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, successor\<rangle> \<circ>\<^sub>c successor)\<circ>\<^sub>c x =  eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, exp_curried \<circ>\<^sub>c successor \<rangle> \<circ>\<^sub>c successor \<circ>\<^sub>c x"
          by (typecheck_cfuncs, smt comp_associative2 exp_uncurried_apply)
        also have "... =  eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, ((mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c exp_curried\<rangle> \<circ>\<^sub>c successor \<circ>\<^sub>c x"
          by (simp add: exp_curried_comp_succ_eq)
        also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c  \<langle>id\<^sub>c\<nat>\<^sub>c \<circ>\<^sub>c  zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, ((mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c exp_curried\<rangle> \<circ>\<^sub>c successor \<circ>\<^sub>c x"
          using id_left_unit2 by (typecheck_cfuncs, presburger)
        also have "... =  eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c  (id\<^sub>c\<nat>\<^sub>c \<times>\<^sub>f ((mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>))  \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, exp_curried\<rangle> \<circ>\<^sub>c successor \<circ>\<^sub>c x"
          by (typecheck_cfuncs, smt (z3) cfunc_cross_prod_comp_cfunc_prod comp_associative2)
        also have "... = (mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, exp_curried\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c x"
          by (typecheck_cfuncs, metis cfunc_type_def comp_associative transpose_func_def)
        also have "... =  (mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, exp_curried\<rangle> ,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, exp_curried\<rangle> \<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c x"
          by (typecheck_cfuncs, simp add: cfunc_prod_comp)
        also have "... = (mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, exp_curried\<rangle> ,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id\<^sub>c\<nat>\<^sub>c \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, exp_curried \<circ>\<^sub>c id\<^sub>c\<nat>\<^sub>c\<rangle> \<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c x"
          by (typecheck_cfuncs, metis id_left_unit2 id_right_unit2)
        also have "... = (mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, exp_curried\<rangle> ,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c\<nat>\<^sub>c \<times>\<^sub>f exp_curried) \<circ>\<^sub>c  \<langle> zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,  id\<^sub>c\<nat>\<^sub>c\<rangle> \<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c x"
          by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
        also have "... = (mult2 \<circ>\<^sub>c\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c\<nat>\<^sub>c \<times>\<^sub>f exp_curried) \<circ>\<^sub>c  \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,  id\<^sub>c\<nat>\<^sub>c\<rangle> \<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c x"
          by (metis (no_types) exp_curried_property left_cart_proj_cfunc_prod zero_betaN_type)
        also have "... = (mult2 \<circ>\<^sub>c\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,  id\<^sub>c\<nat>\<^sub>c\<rangle> \<rangle>)\<circ>\<^sub>c successor \<circ>\<^sub>c x"
          by (typecheck_cfuncs, simp add: cfunc_type_def comp_associative exp_uncurried_def)
        also have "... =  mult2 \<circ>\<^sub>c\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,  id\<^sub>c\<nat>\<^sub>c\<rangle> \<rangle>\<circ>\<^sub>c successor \<circ>\<^sub>c x"
          by (typecheck_cfuncs, metis comp_associative2)
        also have "... =  mult2 \<circ>\<^sub>c\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor \<circ>\<^sub>c x, exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,  id\<^sub>c\<nat>\<^sub>c\<rangle>\<circ>\<^sub>c successor \<circ>\<^sub>c x \<rangle>"
          by (typecheck_cfuncs, smt cfunc_prod_comp cfunc_type_def comp_associative)
        also have "... = zero"
          by (typecheck_cfuncs, metis id_right_unit2 id_type mult_def mult_respects_zero_left one_unique_element)
        also have "... = ((zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c  exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>) \<circ>\<^sub>c x"
          by (typecheck_cfuncs, smt (z3) comp_associative2 id_right_unit2 terminal_func_comp_elem)
        then show "((exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>) \<circ>\<^sub>c successor) \<circ>\<^sub>c x = ((zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>) \<circ>\<^sub>c x"
          using \<open>zero = ((zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>) \<circ>\<^sub>c x\<close> calculation comp_associative2 by (typecheck_cfuncs, force)
      qed
    qed
  qed

  have final_eqn: "zero ^\<^sub>\<nat> (successor \<circ>\<^sub>c n) = exp_uncurried \<circ>\<^sub>c \<langle>zero , successor \<circ>\<^sub>c n\<rangle>"
    using exp_def by auto
  also have "... = exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c n , successor \<circ>\<^sub>c n\<rangle>" 
    using assms by (typecheck_cfuncs, simp add: id_right_unit2 terminal_func_comp_elem)
  also have "... = exp_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>  , successor\<rangle> \<circ>\<^sub>c n "
    using assms cfunc_prod_comp comp_associative2 by (typecheck_cfuncs, force)
  also have "... = zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c n "
    using assms comp_associative2 main_result by (typecheck_cfuncs, force)
  also have "... = zero"
    using assms by (typecheck_cfuncs, simp add: id_right_unit2 terminal_func_comp_elem)
  then show ?thesis
    by (simp add: calculation)
qed
   
lemma exp_respects_one_left:
   assumes n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
   shows "(successor \<circ>\<^sub>c zero) ^\<^sub>\<nat> n = successor \<circ>\<^sub>c zero" 
proof - 
  have "successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> = exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id\<^sub>c\<nat>\<^sub>c\<rangle>"
  proof(etcs_rule natural_number_object_func_unique[where X = "\<nat>\<^sub>c", where f = "id\<^sub>c\<nat>\<^sub>c"])
    show "(successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero = (exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, metis cfunc_type_def comp_associative exp_apply1 exp_respects_Zero_Left id_right_unit2 terminal_func_comp_elem)
    show "(successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor =    id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
      by (typecheck_cfuncs, smt comp_associative2 id_left_unit2 terminal_func_comp)
    show "(exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor =  id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
    proof(etcs_rule one_separator[where X = "\<nat>\<^sub>c", where Y = "\<nat>\<^sub>c"])
      show "\<And>x. x \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>((exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c  successor) \<circ>\<^sub>c x =(id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c x"
      proof - 
        fix x 
        assume x_type[type_rule]: "x \<in>\<^sub>c \<nat>\<^sub>c"
        have "((exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c  successor) \<circ>\<^sub>c x = exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (successor \<circ>\<^sub>c x)"
          by (typecheck_cfuncs, metis cfunc_type_def comp_associative x_type)
        also have "... = exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c (successor \<circ>\<^sub>c x),  successor \<circ>\<^sub>c x\<rangle>"
          by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 id_left_unit2)
        also have "... =  exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero, successor \<circ>\<^sub>c x\<rangle>"
          by (typecheck_cfuncs, simp add: id_right_unit2 terminal_func_comp_elem)
        also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id\<^sub>c\<nat>\<^sub>c \<times>\<^sub>f exp_curried) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero, successor \<circ>\<^sub>c x\<rangle>"
          by (typecheck_cfuncs, simp add: comp_associative2 exp_uncurried_def)
        also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id\<^sub>c\<nat>\<^sub>c \<times>\<^sub>f (id\<^sub>c(\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c exp_curried)) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero, successor \<circ>\<^sub>c x\<rangle>"
          using exp_curried_property id_left_unit2 by auto
        also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id\<^sub>c\<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c(\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero, exp_curried \<circ>\<^sub>c successor \<circ>\<^sub>c x\<rangle>"
          by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
        also have "... =  eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id\<^sub>c\<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c(\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero, ((mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>)  \<circ>\<^sub>c  exp_curried  \<circ>\<^sub>c x\<rangle>"
          by (typecheck_cfuncs, simp add: comp_associative2 exp_curried_comp_succ_eq)  
        also have "... =  eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id\<^sub>c\<nat>\<^sub>c \<times>\<^sub>f (id\<^sub>c(\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c ((mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>))) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero,  exp_curried  \<circ>\<^sub>c x\<rangle>"
          by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
        also have "... = (mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero, exp_curried  \<circ>\<^sub>c x\<rangle>"
          by (typecheck_cfuncs, simp add: comp_associative2 id_left_unit2 transpose_func_def)
        also have "... = mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero,   exp_curried  \<circ>\<^sub>c x\<rangle>"
          by (typecheck_cfuncs, metis comp_associative2)
        also have "... = mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero,    exp_curried  \<circ>\<^sub>c x\<rangle>, eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero,    exp_curried  \<circ>\<^sub>c x\<rangle> \<rangle>"
          by (typecheck_cfuncs, metis cfunc_prod_comp)
        also have "... = mult2 \<circ>\<^sub>c\<langle>successor \<circ>\<^sub>c zero,   eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero,    exp_curried  \<circ>\<^sub>c x\<rangle>\<rangle>"
          using left_cart_proj_cfunc_prod by (typecheck_cfuncs, presburger)
        also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero,    exp_curried  \<circ>\<^sub>c x\<rangle>"
          using mult_def s0_is_left_id by (typecheck_cfuncs, auto)
        also have "... = exp_uncurried \<circ>\<^sub>c \<langle> successor \<circ>\<^sub>c zero, x\<rangle>"
          using exp_uncurried_apply by (typecheck_cfuncs, presburger)
        also have "... = exp_uncurried \<circ>\<^sub>c \<langle> successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c x , x\<rangle>"
          by (typecheck_cfuncs, simp add: id_right_unit2 terminal_func_comp_elem)
        also have "... = (id\<^sub>c\<nat>\<^sub>c \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle> successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>  , id\<^sub>c\<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c x"
          by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 id_left_unit2)
        then show "((exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor) \<circ>\<^sub>c x = (id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c x"
          by (simp add: calculation)
      qed
    qed
  qed
  then have "successor \<circ>\<^sub>c zero = exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c n, id\<^sub>c\<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>" 
    by (typecheck_cfuncs, smt (verit, best)  cart_prod_extract_right cfunc_prod_type comp_associative2 comp_type id_right_unit2 terminal_func_comp_elem)
  then show ?thesis
    by (typecheck_cfuncs, metis exp_def id_left_unit2 id_right_unit2 terminal_func_comp_elem)
qed



lemma exp_respects_successor:
   assumes "m \<in>\<^sub>c  \<nat>\<^sub>c" "n \<in>\<^sub>c  \<nat>\<^sub>c"
   shows "m^\<^sub>\<nat>(successor \<circ>\<^sub>c n) = m \<cdot>\<^sub>\<nat> (m^\<^sub>\<nat> n)"
proof - 
  have "m^\<^sub>\<nat>(successor \<circ>\<^sub>c n) = exp_uncurried \<circ>\<^sub>c \<langle>m,successor \<circ>\<^sub>c n\<rangle>"
    by (simp add: exp_def)
  also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f exp_curried) \<circ>\<^sub>c  \<langle>m,successor \<circ>\<^sub>c n\<rangle>"
    unfolding exp_uncurried_def
    using assms by (typecheck_cfuncs, simp add: comp_associative2)
  also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f exp_curried) \<circ>\<^sub>c  \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m,successor \<circ>\<^sub>c n\<rangle>"
    using assms(1) id_left_unit2 by auto
  also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f exp_curried) \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c   \<langle>m,  n\<rangle>"
    using assms cfunc_cross_prod_comp_cfunc_prod id_type successor_type by fastforce
  also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (exp_curried \<circ>\<^sub>c successor)) \<circ>\<^sub>c  \<langle>m,  n\<rangle>"
    using assms by (typecheck_cfuncs, simp add: comp_associative2 identity_distributes_across_composition)
  also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (((mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>)\<circ>\<^sub>c exp_curried)) \<circ>\<^sub>c  \<langle>m,  n\<rangle>"
    by (simp add: exp_curried_comp_succ_eq)
  also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>)  \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f exp_curried) \<circ>\<^sub>c \<langle>m,n\<rangle>"
    using assms by (typecheck_cfuncs, simp add: comp_associative2 identity_distributes_across_composition)
  also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>)  \<circ>\<^sub>c \<langle>m,exp_curried \<circ>\<^sub>c  n\<rangle>"
    using assms cfunc_cross_prod_comp_cfunc_prod exp_curried_type id_left_unit2 id_type by fastforce
  also have "... = mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>  \<circ>\<^sub>c   \<langle>m,exp_curried \<circ>\<^sub>c  n\<rangle>"
      using assms by (typecheck_cfuncs, simp add: comp_associative2 transpose_func_def)
  also have "... = mult2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c   \<langle>m,exp_curried \<circ>\<^sub>c  n\<rangle> ,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c   \<langle>m,exp_curried \<circ>\<^sub>c  n\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp)
  also have "... = mult2 \<circ>\<^sub>c\<langle>m ,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c   \<langle>m,exp_curried \<circ>\<^sub>c  n\<rangle>\<rangle>"
    by (metis assms comp_type exp_curried_type left_cart_proj_cfunc_prod)
  also have "... = mult2 \<circ>\<^sub>c\<langle>m ,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f exp_curried)\<circ>\<^sub>c \<langle>m, n\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
  also have "... = mult2 \<circ>\<^sub>c\<langle>m ,exp_uncurried\<circ>\<^sub>c \<langle>m, n\<rangle>\<rangle>  "
    using assms by (typecheck_cfuncs, simp add: comp_associative2 exp_uncurried_def)
  also have "... = m \<cdot>\<^sub>\<nat> (m^\<^sub>\<nat> n) "
    by (simp add: exp_def mult_def)
  then show ?thesis
    using calculation by auto
qed

lemma exp_left_dist:
   assumes a_type[type_rule]: "a \<in>\<^sub>c \<nat>\<^sub>c" and b_type[type_rule]: "b \<in>\<^sub>c \<nat>\<^sub>c" and c_type[type_rule]: "c \<in>\<^sub>c \<nat>\<^sub>c"
   shows "(a \<cdot>\<^sub>\<nat> b) ^\<^sub>\<nat> c = (a ^\<^sub>\<nat>c) \<cdot>\<^sub>\<nat> (b ^\<^sub>\<nat> c)"
proof - 
  have main_result: "(exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> = (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
   (right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
   (right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>"
  proof(etcs_rule natural_number_object_func_unique[where X = "\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>", where f ="(mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)), eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>"])
    show "(exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero =
          (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero"
    proof(etcs_rule same_evals_equal[where Z = "\<one>", where X = "\<nat>\<^sub>c", where A = "\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"])
      show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero = eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero"
      proof(etcs_rule one_separator[where X = "(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<one>", where Y = "\<nat>\<^sub>c"])
        show "\<And>x. x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<one> \<Longrightarrow>
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x"
        proof - 
          fix x 
          assume x_type[type_rule]: "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<one>"
          obtain y where y_type[type_rule]:  "y \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c" and x_def: "x = \<langle>y,id \<one>\<rangle>"
            by (typecheck_cfuncs, metis cart_prod_decomp terminal_func_unique x_type)
          obtain p q where p_type[type_rule]: "p \<in>\<^sub>c \<nat>\<^sub>c" and q_type[type_rule]: "q \<in>\<^sub>c \<nat>\<^sub>c" and y_def: "y = \<langle>p,q\<rangle>"
            by (typecheck_cfuncs, meson cart_prod_decomp)

          have "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>fzero) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, smt comp_associative2 inv_transpose_func_def3 inv_transpose_of_composition x_type)
          also have "... = (exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>fzero) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, simp add: transpose_func_def)
          also have "... = (exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,zero\<rangle>"
            by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2 id_type x_def y_def)
          also have "... = exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,zero\<rangle>"
            using comp_associative2  by (typecheck_cfuncs, fastforce)
          also have "... = exp_uncurried \<circ>\<^sub>c  \<langle>mult2 \<circ>\<^sub>c \<langle>p,q\<rangle>,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero\<rangle>"
            by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod)
          also have "... = exp_uncurried \<circ>\<^sub>c  \<langle>p \<cdot>\<^sub>\<nat> q ,zero\<rangle>"
            using id_left_unit2 mult_def zero_type by auto
          also have "... = (p \<cdot>\<^sub>\<nat> q) ^\<^sub>\<nat> zero"
            by (simp add: exp_def) 
          also have "... = (successor \<circ>\<^sub>c zero)"
            by (typecheck_cfuncs, simp add: exp_respects_Zero_Left mult_closure)
          also have "... = (successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c zero)"
            by (simp add: s0_is_right_id succ_n_type zero_type)
         also have "... = mult2 \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero, successor \<circ>\<^sub>c zero\<rangle>"
           by (simp add: mult_def)
         also have "... = mult2 \<circ>\<^sub>c  \<langle>p ^\<^sub>\<nat> zero, q ^\<^sub>\<nat> zero\<rangle>"
           by (typecheck_cfuncs, simp add: exp_respects_Zero_Left)
         also have "... = mult2 \<circ>\<^sub>c  \<langle>exp_uncurried \<circ>\<^sub>c \<langle>p,zero\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>q,zero\<rangle>\<rangle>"
           by (simp add: exp_def)
         also have "... = mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>p,zero\<rangle>,\<langle>q,zero\<rangle>\<rangle>"
           by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod)
         also have "... = mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c
               \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,zero\<rangle>  ,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,zero\<rangle>  \<rangle>   ,
               \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,zero\<rangle>  ,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,zero\<rangle>  \<rangle>    \<rangle>"
           by (typecheck_cfuncs, smt left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
         also have "... = mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c
 \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,zero\<rangle>  ,
 \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>   \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,zero\<rangle> \<rangle> "
           by (typecheck_cfuncs, simp add: cfunc_prod_comp cfunc_type_def comp_associative)
         also have "... = mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c \<langle>y,zero\<rangle>"
           by (typecheck_cfuncs, simp add: cfunc_prod_comp y_def)
         also have "... = (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero)) \<circ>\<^sub>c x"
           by (typecheck_cfuncs, smt (z3) cfunc_cross_prod_comp_cfunc_prod comp_associative2 id_left_unit2 id_right_unit2 one_unique_element terminal_func_comp terminal_func_comp_elem x_def)
         also have "... = ((mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero)) \<circ>\<^sub>c x"
           by (typecheck_cfuncs, simp add: comp_associative2)
         also have "... = ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero)) \<circ>\<^sub>c x"
           by (typecheck_cfuncs, simp add: transpose_func_def) 
         also  have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x"
           by (typecheck_cfuncs, smt inv_transpose_func_def3 inv_transpose_of_composition)
         then show "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x =
                    (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x"
           by (simp add: calculation)
       qed
     qed
    qed
    show "(exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor =
         (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
    proof(etcs_rule same_evals_equal[where Z ="\<nat>\<^sub>c", where X = "\<nat>\<^sub>c", where A = "\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"])
      show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor =
            eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
      proof(etcs_rule one_separator[where X = "(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c", where Y = "\<nat>\<^sub>c"])
        show "\<And>x. x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c x"
        proof - 
          fix x 
          assume x_type[type_rule]: "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c"
          obtain y r where y_type[type_rule]: "y \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c" and  r_type[type_rule]: "r \<in>\<^sub>c \<nat>\<^sub>c" and x_def: "x = \<langle>y, r\<rangle>" 
            using cart_prod_decomp x_type by blast
          obtain p q where p_type[type_rule]: "p \<in>\<^sub>c \<nat>\<^sub>c" and q_type[type_rule]: "q \<in>\<^sub>c \<nat>\<^sub>c" and y_def: "y = \<langle>p, q\<rangle>"
            using cart_prod_decomp  by (typecheck_cfuncs, blast)

          have "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
                ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>) \<circ>\<^sub>c(id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor)) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, metis inv_transpose_func_def3 inv_transpose_of_composition)
          also have "... = ((exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c(id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor)) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, simp add: transpose_func_def)
          also have "... = (exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c(id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor)) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, simp add: comp_associative2)
          also have "... = exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c(id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, simp add: cfunc_type_def comp_associative)
          also have "... = exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, successor \<circ>\<^sub>c r\<rangle>"
            by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 x_def y_def)
          also have "... = exp_uncurried \<circ>\<^sub>c  \<langle>mult2 \<circ>\<^sub>c \<langle>p,q\<rangle>, successor \<circ>\<^sub>c r\<rangle>"
            by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
          also have "... = (p \<cdot>\<^sub>\<nat> q)^\<^sub>\<nat> (successor \<circ>\<^sub>c r)"
            by (simp add: exp_def mult_def)
          also have "... = (p \<cdot>\<^sub>\<nat> q) \<cdot>\<^sub>\<nat> ((p \<cdot>\<^sub>\<nat> q)^\<^sub>\<nat>r)"
            by (typecheck_cfuncs, simp add: exp_respects_successor mult_closure)
          also have "... = mult2 \<circ>\<^sub>c \<langle>p \<cdot>\<^sub>\<nat> q, exp_uncurried \<circ>\<^sub>c  \<langle>mult2 \<circ>\<^sub>c\<langle>p,q\<rangle> ,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c r\<rangle>\<rangle>"
            by (typecheck_cfuncs, simp add: exp_def id_left_unit2 mult_def)
          also have "... = mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c  \<circ>\<^sub>c x, exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c x\<rangle>"
            by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod left_cart_proj_cfunc_prod mult_def x_def y_def)
          also have "... = mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c, exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c x"
            by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
          also have "... = (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c, exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, simp add: comp_associative2)
          also have "... = (mult2 \<circ>\<^sub>c \<langle>
             mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>),
             exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, simp add: id_left_unit2 left_cart_proj_cfunc_cross_prod)
          also have "... = (mult2 \<circ>\<^sub>c \<langle>
             mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>),
             eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>)\<rangle>) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, simp add: transpose_func_def)
          also have "... = (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),
             eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)  \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 x_type)
          also have "... = ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)
               \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>)) 
               \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>)) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, simp add:  comp_associative2 transpose_func_def)
          also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)
               \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>) 
               \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>)) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, simp add: comp_associative2)
          then show " (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
                      (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, smt calculation inv_transpose_func_def3 inv_transpose_of_composition)         
        qed
      qed
    qed

    show "(mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor =
          (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>"    
    proof(etcs_rule same_evals_equal[where Z ="\<nat>\<^sub>c", where X = "\<nat>\<^sub>c", where A = "\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"])
      show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor =
            eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>"
      proof(etcs_rule one_separator[where X = "(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c", where Y = "\<nat>\<^sub>c"])
        show "\<And>x. x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
              (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
              (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c x"
        proof - 
          fix x 
          assume x_type[type_rule]: "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c"
          obtain y r where y_type[type_rule]: "y \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c" and r_type[type_rule]: "r \<in>\<^sub>c \<nat>\<^sub>c" and x_def: "x = \<langle>y,r\<rangle>" 
            using cart_prod_decomp x_type by blast
          obtain p q where p_type[type_rule]: "p \<in>\<^sub>c \<nat>\<^sub>c" and q_type[type_rule]: "q \<in>\<^sub>c \<nat>\<^sub>c" and y_def: "y = \<langle>p,q\<rangle>"
            using cart_prod_decomp by (typecheck_cfuncs, blast)
    
          obtain F where F_def: "F = id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>"
            and          F_type[type_rule]: "F: (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)"
            by (typecheck_cfuncs, blast)
    
          have "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x = 
               ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c(id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor)) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, smt inv_transpose_func_def3 inv_transpose_of_composition)
          also have "... = ((mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c(id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor)) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, simp add: transpose_func_def)
          also have "... = (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c(id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, simp add: comp_associative2) 
          also have "... = (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c  \<langle>id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c y,successor \<circ>\<^sub>c r\<rangle>"
            by (typecheck_cfuncs, simp add:  cfunc_cross_prod_comp_cfunc_prod x_def)
          also have "... = (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c  \<langle>y,successor \<circ>\<^sub>c r\<rangle>"
            by (typecheck_cfuncs, simp add: id_left_unit2)
          also have "... = mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c  \<langle>y,successor \<circ>\<^sub>c r\<rangle>"
            by (typecheck_cfuncs, simp add: cfunc_type_def comp_associative)
          also have "... = mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>y,successor \<circ>\<^sub>c r\<rangle> ,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>y,successor \<circ>\<^sub>c r\<rangle>\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>y,successor \<circ>\<^sub>c r\<rangle>,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>y,successor \<circ>\<^sub>c r\<rangle>\<rangle>\<rangle>"
            by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
          also have "... = mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>p ,successor \<circ>\<^sub>c r\<rangle>,\<langle>q, successor \<circ>\<^sub>c r\<rangle>\<rangle>"
            by (typecheck_cfuncs, smt left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod y_def )
          also have "... = mult2 \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>p ,successor \<circ>\<^sub>c r\<rangle>, exp_uncurried \<circ>\<^sub>c \<langle>q, successor \<circ>\<^sub>c r\<rangle>\<rangle>"
            by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
          also have "... = (p^\<^sub>\<nat>(successor \<circ>\<^sub>c r)) \<cdot>\<^sub>\<nat>  (q^\<^sub>\<nat>(successor \<circ>\<^sub>c r))"
            by (simp add: exp_def mult_def)
          also have "... = (p \<cdot>\<^sub>\<nat>   (p^\<^sub>\<nat>r)) \<cdot>\<^sub>\<nat> ((q \<cdot>\<^sub>\<nat>  (q^\<^sub>\<nat>r)))"
            by (typecheck_cfuncs, simp add: exp_respects_successor)
          also have "... = p \<cdot>\<^sub>\<nat> (  (p^\<^sub>\<nat>r) \<cdot>\<^sub>\<nat> (q \<cdot>\<^sub>\<nat>  (q^\<^sub>\<nat>r)))"
            by (typecheck_cfuncs, simp add: exp_closure mult_associative mult_closure)
          also have "... = p \<cdot>\<^sub>\<nat> ((q \<cdot>\<^sub>\<nat>  (q^\<^sub>\<nat>r)) \<cdot>\<^sub>\<nat> (p^\<^sub>\<nat>r))"
            using exp_closure mult_closure mult_commutative  by (typecheck_cfuncs, presburger)
          also have "... = p \<cdot>\<^sub>\<nat> (q \<cdot>\<^sub>\<nat>  ((q^\<^sub>\<nat>r) \<cdot>\<^sub>\<nat> (p^\<^sub>\<nat>r)))"
            by (typecheck_cfuncs, simp add: exp_closure mult_associative)
          also have "... = p \<cdot>\<^sub>\<nat> (q \<cdot>\<^sub>\<nat>  ((p^\<^sub>\<nat>r) \<cdot>\<^sub>\<nat> (q^\<^sub>\<nat>r)))"
            by (typecheck_cfuncs, simp add: exp_closure mult_commutative)
          also have "... = (p \<cdot>\<^sub>\<nat> q)\<cdot>\<^sub>\<nat>  ((p^\<^sub>\<nat>r) \<cdot>\<^sub>\<nat> (q^\<^sub>\<nat>r))"
            by (typecheck_cfuncs, simp add: exp_closure mult_associative mult_closure)
          also have "... = mult2 \<circ>\<^sub>c \<langle>mult2  \<circ>\<^sub>c \<langle>p,q\<rangle>  ,mult2 \<circ>\<^sub>c   \<langle>exp_uncurried \<circ>\<^sub>c \<langle>p,r\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>q,r\<rangle>\<rangle>\<rangle>"
            by (simp add: exp_def mult_def)
          also have "... = (mult2 \<circ>\<^sub>c \<langle>mult2  \<circ>\<^sub>c \<langle>p,q\<rangle>  ,mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>p,r\<rangle>,\<langle>q,r\<rangle>\<rangle>\<rangle>) "
            by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
          also have "... = (mult2 \<circ>\<^sub>c \<langle>mult2  \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c x  ,mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c x,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c x\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c x,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c x\<rangle>\<rangle>\<rangle>) "
            by (typecheck_cfuncs, simp add: id_left_unit2 left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod x_def y_def)
          also have "... = (mult2 \<circ>\<^sub>c \<langle>mult2  \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)   ,mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2)
          also have "... = (mult2 \<circ>\<^sub>c \<langle>mult2  \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)   ,eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c F\<rangle>) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, simp add: F_def transpose_func_def)
          also have "... = (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>) \<circ>\<^sub>c F ,eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c F\<rangle>) \<circ>\<^sub>c x"
            sorry
          also have "... = (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c F) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2) 
          also have "... = (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle> )\<circ>\<^sub>c F \<circ>\<^sub>c x" 
            by (typecheck_cfuncs, simp add: comp_associative2)
          also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> )\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c x" 
            by (typecheck_cfuncs, simp add: F_def transpose_func_def)
          then show "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
                     (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c x"   
            by (typecheck_cfuncs, smt F_def F_type calculation comp_associative2 inv_transpose_func_def3 inv_transpose_of_composition transpose_func_def x_type)
        qed
      qed
    qed
  qed
  have main_result_flat: "exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) = mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
 (right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
 (right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>"
    by (typecheck_cfuncs, metis main_result transpose_func_def)
  have final_equation: "(a \<cdot>\<^sub>\<nat> b)^\<^sub>\<nat> c = exp_uncurried \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>a,b\<rangle>, c\<rangle>"
    by (simp add: exp_def mult_def)
  also have "... = exp_uncurried \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>a,b\<rangle>, id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c c\<rangle>"
    using assms(3) id_left_unit2 by force
  also have "... = exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
    by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod assms)
  also have "... = (exp_uncurried \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
    by (typecheck_cfuncs, meson  comp_associative2 assms)
  also have "... = (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
                                   (right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
                                   (right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
    by (simp add: main_result_flat)
  also have "... = mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
     (right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
     (right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle> \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
    by (typecheck_cfuncs, smt assms cfunc_type_def comp_associative)
  also have "... = mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>,
     (right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>\<rangle>, \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>,
     (right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>\<rangle>\<rangle> "
    using assms cfunc_prod_comp comp_associative2 by (typecheck_cfuncs, auto)
  also have "... = mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>a,c\<rangle>, \<langle>b,c\<rangle>\<rangle> "
    by (typecheck_cfuncs, smt assms left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  also have "... = mult2 \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a,c\<rangle>, exp_uncurried \<circ>\<^sub>c \<langle>b,c\<rangle>\<rangle> "
    by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod assms)
  also have "... = (a^\<^sub>\<nat> c) \<cdot>\<^sub>\<nat> (b^\<^sub>\<nat> c)"
    by (simp add: exp_def mult_def)
  then show ?thesis
    by (simp add: calculation)
qed

lemma exp_right_dist:
   assumes "a \<in>\<^sub>c \<nat>\<^sub>c" "b \<in>\<^sub>c \<nat>\<^sub>c" "c \<in>\<^sub>c \<nat>\<^sub>c"
   shows "a ^\<^sub>\<nat> (b +\<^sub>\<nat> c) = (a^\<^sub>\<nat> b) \<cdot>\<^sub>\<nat> (a^\<^sub>\<nat> c)"
proof - 
 have main_result: "(exp_uncurried \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c (associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> = 
    (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c (distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>"
 proof(etcs_rule natural_number_object_func_unique[where X = "\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>",
       where f = "(mult2 \<circ>\<^sub>c \<langle>(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)), (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c  (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>))\<rangle>)\<^sup>\<sharp>"])
  show "(exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero =
    (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero"
  proof(etcs_rule same_evals_equal[where Z=\<one>, where X="\<nat>\<^sub>c", where A="\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"])
    show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero =
    eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero"
    proof(etcs_rule one_separator[where X="(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<one>", where Y="\<nat>\<^sub>c"])
      show "\<And>x. x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<one> \<Longrightarrow>
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c  distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x"
      proof - 
        fix x 
        assume x_type[type_rule]: "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<one>"
        obtain y where y_type[type_rule]: "y \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c" and x_def: "x = \<langle>y, id \<one>\<rangle>"
          by (typecheck_cfuncs, metis cart_prod_decomp terminal_func_unique x_type)
        obtain p q where p_type[type_rule]: "p \<in>\<^sub>c \<nat>\<^sub>c" and q_type[type_rule]: "q \<in>\<^sub>c \<nat>\<^sub>c" and y_def: "y = \<langle>p,q\<rangle>"
          using cart_prod_decomp  by (typecheck_cfuncs, blast)
        have  "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x =
              (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c ((id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f  zero) \<circ>\<^sub>c x)"
          by (typecheck_cfuncs, smt cfunc_type_def comp_associative inv_transpose_func_def3 inv_transpose_of_composition x_type)
        also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c y, zero \<circ>\<^sub>c id \<one>\<rangle>"
          using cfunc_cross_prod_comp_cfunc_prod x_def by (typecheck_cfuncs, auto)
        also have "... = (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>y, zero\<rangle>"
          using id_left_unit2 id_right_unit2 transpose_func_def x_def by (typecheck_cfuncs, auto)
        also have "... = exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>y, zero\<rangle>"
          using cfunc_type_def comp_associative  by (typecheck_cfuncs, fastforce)
        also have "... = exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c \<langle>p, \<langle>q, zero\<rangle>\<rangle>"
          using associate_right_ap y_def by (typecheck_cfuncs, auto) 
        also have "... = exp_uncurried \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c p, add2 \<circ>\<^sub>c \<langle>q, zero\<rangle>\<rangle>"
          by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod y_def)
        also have "... = exp_uncurried \<circ>\<^sub>c \<langle>p, q +\<^sub>\<nat> zero\<rangle>"
          using add_def id_left_unit2 y_def by (typecheck_cfuncs, auto)
        also have "... =  p ^\<^sub>\<nat> q"
          by (typecheck_cfuncs, simp add: add_respects_zero_on_right exp_def)
        also have "... = (p ^\<^sub>\<nat> q) \<cdot>\<^sub>\<nat> (p ^\<^sub>\<nat> zero)"
          by (typecheck_cfuncs, simp add: exp_closure exp_respects_Zero_Left s0_is_right_id)
        also have "... =  mult2 \<circ>\<^sub>c  \<langle>exp_uncurried \<circ>\<^sub>c \<langle>p,q\<rangle>, exp_uncurried \<circ>\<^sub>c \<langle>p,zero\<rangle>\<rangle>"
          using exp_def mult_def by auto
        also have "... =  mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,\<langle>p,zero\<rangle>\<rangle>"
          by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod)
        also have "... =  mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>p, \<langle>q, zero\<rangle>\<rangle>"
          using distribute_left_ap by (typecheck_cfuncs, auto)
        also have "... =  mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, zero\<rangle>"
          using associate_right_ap  by (typecheck_cfuncs, auto)
        also have "... = (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, zero\<rangle>"
          using cfunc_type_def comp_associative  by (typecheck_cfuncs, auto)
        also have "... = (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero) \<circ>\<^sub>c x"
          by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2 id_type x_def y_def)
        also have "... = ((mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero)) \<circ>\<^sub>c x"
          using comp_associative2  by (typecheck_cfuncs, blast)
        also have "... =((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero)) \<circ>\<^sub>c x"
          by (typecheck_cfuncs,simp add: transpose_func_def)
        also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x"
          by (typecheck_cfuncs, metis inv_transpose_func_def3 inv_transpose_of_composition)  
        then show "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x =
     (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c  distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x"
          by (simp add: calculation)
      qed
    qed
  qed
  show "(exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor =
      (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
  proof(etcs_rule same_evals_equal[where Z = "\<nat>\<^sub>c", where X = "\<nat>\<^sub>c", where A = "\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"])
    show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor =
          eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
    proof(etcs_rule one_separator[where X = "(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c", where Y = "\<nat>\<^sub>c"])
      show "\<And>x. x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
       (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
       (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c), left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c x"
      proof - 
        fix x
        assume x_type[type_rule]: "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c"
        obtain y r where y_type[type_rule]: "y \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c" and r_type[type_rule]: "r \<in>\<^sub>c \<nat>\<^sub>c" and x_def:  "x = \<langle>y,r\<rangle>"
          using cart_prod_decomp x_type by blast
        obtain p q where p_type[type_rule]: "p \<in>\<^sub>c \<nat>\<^sub>c" and q_type[type_rule]: "q \<in>\<^sub>c \<nat>\<^sub>c" and y_def: "y = \<langle>p,q\<rangle>"
          using cart_prod_decomp x_def by (typecheck_cfuncs, blast)
        obtain g where g_def: "g =id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
          by simp  
        have "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
              ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f  successor)) \<circ>\<^sub>c x"
          by (typecheck_cfuncs, metis inv_transpose_func_def3 inv_transpose_of_composition)
        also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle> id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c y, successor\<circ>\<^sub>c r\<rangle>"
          by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod cfunc_type_def comp_associative x_def x_type)
        also have "... = (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>y, successor\<circ>\<^sub>c r\<rangle>" 
          using id_left_unit2 transpose_func_def x_def by (typecheck_cfuncs, auto)
        also have "... = exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>y, successor\<circ>\<^sub>c r\<rangle>" 
          using cfunc_type_def comp_associative  by (typecheck_cfuncs, fastforce)
        also have "... = exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c  \<langle>p,\<langle>q, successor\<circ>\<^sub>c r\<rangle>\<rangle>" 
          using associate_right_ap x_def y_def by (typecheck_cfuncs, auto)
        also have "... = exp_uncurried \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c p ,add2 \<circ>\<^sub>c \<langle>q, successor\<circ>\<^sub>c r\<rangle>\<rangle>" 
          using cfunc_cross_prod_comp_cfunc_prod  y_def by (typecheck_cfuncs, auto)
        also have "... = exp_uncurried \<circ>\<^sub>c \<langle>p ,add2 \<circ>\<^sub>c \<langle>q, successor\<circ>\<^sub>c r\<rangle>\<rangle>" 
          using id_left_unit2 y_def by (typecheck_cfuncs, auto)
        also have "... = p^\<^sub>\<nat> (q +\<^sub>\<nat> (successor \<circ>\<^sub>c r))"
          by (simp add: add_def exp_def) 
        also have "... = p^\<^sub>\<nat> (successor\<circ>\<^sub>c (q +\<^sub>\<nat>  r))"
          by (typecheck_cfuncs, simp add: add_respects_succ1)
        also have "... = (p^\<^sub>\<nat>(q +\<^sub>\<nat> r)) \<cdot>\<^sub>\<nat> p"
          by (typecheck_cfuncs, simp add: add_type exp_closure exp_respects_successor mult_commutative)
        also have "... = mult2 \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>p, add2 \<circ>\<^sub>c \<langle>q,r\<rangle>\<rangle>, p\<rangle>"
          by (simp add: add_def exp_def mult_def)
        also have "... = mult2 \<circ>\<^sub>c \<langle>exp_uncurried  \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c p, add2 \<circ>\<^sub>c \<langle>q,r\<rangle>\<rangle>, p\<rangle>"
          using id_left_unit2 y_def by (typecheck_cfuncs, auto)
        also have "... = mult2 \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c \<langle>p, \<langle>q,r\<rangle>\<rangle>, p\<rangle>"
          using cfunc_cross_prod_comp_cfunc_prod  by (typecheck_cfuncs, auto)
        also have "... = mult2 \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c x,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c x\<rangle>"
          by (typecheck_cfuncs, metis associate_right_ap id_left_unit2 left_cart_proj_cfunc_prod x_def y_def y_type)
        also have "... = mult2 \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>  \<circ>\<^sub>c x"
          using cfunc_prod_comp comp_associative2 x_type by (typecheck_cfuncs, auto)
        also have "... = (mult2 \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle> ) \<circ>\<^sub>c x"
          using comp_associative2 x_type by (typecheck_cfuncs, blast)
        also have "... = (mult2 \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>) \<circ>\<^sub>c g\<rangle> ) \<circ>\<^sub>c x"
          by (typecheck_cfuncs, smt (verit, best) g_def left_cart_proj_cfunc_cross_prod transpose_func_type)
        also have "... = (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c g,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>) \<circ>\<^sub>c g\<rangle> ) \<circ>\<^sub>c x"
          by (typecheck_cfuncs, simp add: g_def transpose_func_def)
        also have "... = (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle> \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>)) \<circ>\<^sub>c x"
          using cfunc_prod_comp comp_associative2 g_def by (typecheck_cfuncs, auto)
        also have "... = ((mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>)) \<circ>\<^sub>c x"
          using comp_associative2 by (typecheck_cfuncs, auto)
        also have "... = ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>)) \<circ>\<^sub>c x"
          by (typecheck_cfuncs, simp add: transpose_func_def)
        also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c x"
          by (typecheck_cfuncs, smt inv_transpose_func_def3 inv_transpose_of_composition)
        then show " (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
   (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c x"
          by (simp add: calculation)
      qed
    qed
  qed
  show "(mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor =
        (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
  proof(etcs_rule same_evals_equal[where Z = "\<nat>\<^sub>c", where X = "\<nat>\<^sub>c", where A = "\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"])
    show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor =
    eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
    proof(etcs_rule one_separator[where X = "(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c\<nat>\<^sub>c", where Y = "\<nat>\<^sub>c"])
      show "\<And>x. x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c x"
      proof - 
        fix x
        assume x_type[type_rule]: "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c"
        obtain y r where y_type[type_rule]: "y \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c" and r_type[type_rule]: "r \<in>\<^sub>c \<nat>\<^sub>c" and x_def: "x = \<langle>y,r\<rangle>"
          using cart_prod_decomp x_type by blast
        obtain p q where p_type[type_rule]: "p \<in>\<^sub>c \<nat>\<^sub>c" and q_type[type_rule]: "q \<in>\<^sub>c \<nat>\<^sub>c" and y_def: "y = \<langle>p,q\<rangle>"
          using cart_prod_decomp  by (typecheck_cfuncs, blast)   
        obtain g where g_def: "g = id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
          by simp
    
        have "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x = 
         ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor)) \<circ>\<^sub>c x"
          by (typecheck_cfuncs, metis inv_transpose_func_def3 inv_transpose_of_composition)
        also have "... = ((mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor)) \<circ>\<^sub>c x"
          by (typecheck_cfuncs, simp add: transpose_func_def)
        also have "... = (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor) \<circ>\<^sub>c x"
          using comp_associative2  by (typecheck_cfuncs, auto)
        also have "... = (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c y ,successor \<circ>\<^sub>c r\<rangle>"
          using cfunc_cross_prod_comp_cfunc_prod x_def by (typecheck_cfuncs, auto)
        also have "... = (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>y ,successor \<circ>\<^sub>c r\<rangle>"
          using id_left_unit2  by (typecheck_cfuncs, auto)
        also have "... = mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>y ,successor \<circ>\<^sub>c r\<rangle>"
          using comp_associative2  by (typecheck_cfuncs, auto)
        also have "... = mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>p,\<langle>q ,successor \<circ>\<^sub>c r\<rangle>\<rangle>"
          using associate_right_ap  y_def by (typecheck_cfuncs, auto)
        also have "... = mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c  \<langle>\<langle>p ,q\<rangle>,\<langle>p ,successor \<circ>\<^sub>c r\<rangle>\<rangle>"
          using distribute_left_ap by (typecheck_cfuncs, auto)
        also have "... = mult2 \<circ>\<^sub>c   \<langle>exp_uncurried \<circ>\<^sub>c  \<langle>p ,q\<rangle>,exp_uncurried \<circ>\<^sub>c  \<langle>p ,successor \<circ>\<^sub>c r\<rangle>\<rangle>"
          by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod)
        also have "... = (p^\<^sub>\<nat>q) \<cdot>\<^sub>\<nat> (p^\<^sub>\<nat> (successor \<circ>\<^sub>c r))"
          by (simp add: exp_def mult_def)
        also have "... = (p ^\<^sub>\<nat> q) \<cdot>\<^sub>\<nat> ((p ^\<^sub>\<nat> r) \<cdot>\<^sub>\<nat> p )"
          using exp_respects_successor mult_commutative by (typecheck_cfuncs, presburger)
        also have "... = ((p ^\<^sub>\<nat> q) \<cdot>\<^sub>\<nat> (p ^\<^sub>\<nat> r)) \<cdot>\<^sub>\<nat> p "
          by (typecheck_cfuncs, meson mult_associative)
        also have "... = mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c  \<langle>exp_uncurried \<circ>\<^sub>c \<langle>p,q\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>p,r\<rangle>\<rangle> ,p\<rangle>"
          by (simp add: exp_def mult_def)
        also have "... = mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c  \<langle>\<langle>p,q\<rangle>,\<langle>p,r\<rangle>\<rangle> ,p\<rangle>"
          using cfunc_cross_prod_comp_cfunc_prod   by (typecheck_cfuncs, auto)
        also have "... = mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>p,\<langle>q,r\<rangle>\<rangle> ,p\<rangle>"
          using distribute_left_ap x_def y_def by (typecheck_cfuncs, auto)
        also have "... = mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c x ,p\<rangle>"
          using associate_right_ap x_def y_def by (typecheck_cfuncs, auto)
        also have "... = mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c x ,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c  \<circ>\<^sub>c x\<rangle>"
          by (typecheck_cfuncs, metis id_left_unit2 left_cart_proj_cfunc_prod q_type r_type x_def y_def y_type)
        also have "... = mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c ,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>   \<circ>\<^sub>c x"
          using cfunc_prod_comp comp_associative2 by (typecheck_cfuncs, auto)
        also have "... = (mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c ,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>  ) \<circ>\<^sub>c x"
          using comp_associative2  by (typecheck_cfuncs, blast)
        also have "... = (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c g ,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<circ>\<^sub>c g \<rangle>  ) \<circ>\<^sub>c x"
          by (typecheck_cfuncs, smt (verit, best) g_def left_cart_proj_cfunc_cross_prod transpose_func_def transpose_func_type)
        also have "... = ((mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>)) \<circ>\<^sub>c x"
          by (typecheck_cfuncs, smt cfunc_prod_comp cfunc_type_def comp_associative g_def)
        also have "... = ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>)) \<circ>\<^sub>c x"
          by (typecheck_cfuncs, simp add: transpose_func_def)
        also have "... =  (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c x"
          by (typecheck_cfuncs, smt inv_transpose_func_def3 inv_transpose_of_composition)
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
    using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
  also have "... = exp_uncurried \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c  (associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
    using assms associate_right_ap by auto
  also have "... = (exp_uncurried \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c  (associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
    by (typecheck_cfuncs, metis cfunc_type_def comp_associative assms)
  also have "... = (mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c (distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
    by (simp add: main_result_flat)
  also have "... = mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c (distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
    using  assms comp_associative2 by (typecheck_cfuncs, auto)
  also have "... = mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried) \<circ>\<^sub>c (distribute_left \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c  \<langle>a, \<langle>b,c\<rangle>\<rangle>"
    using assms associate_right_ap by auto
  also have "... = mult2 \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f exp_uncurried)  \<circ>\<^sub>c  \<langle>\<langle>a,b\<rangle>, \<langle>a,c\<rangle>\<rangle>"
    using assms distribute_left_ap by auto
  also have "... = mult2 \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a,b\<rangle>, exp_uncurried \<circ>\<^sub>c \<langle>a,c\<rangle>\<rangle>"
    using  assms cfunc_cross_prod_comp_cfunc_prod by (typecheck_cfuncs, auto)
  also have "... = (a^\<^sub>\<nat> b) \<cdot>\<^sub>\<nat> (a^\<^sub>\<nat> c)"
    by (simp add: exp_def mult_def)
  then show ?thesis using calculation by auto
qed

lemma power_tower_rule:
   assumes "a \<in>\<^sub>c \<nat>\<^sub>c" "b \<in>\<^sub>c \<nat>\<^sub>c" "c \<in>\<^sub>c \<nat>\<^sub>c"
   shows "(a ^\<^sub>\<nat> b)^\<^sub>\<nat> c = (a^\<^sub>\<nat> (b \<cdot>\<^sub>\<nat> c))"
proof- 
  have main_result: "(exp_uncurried \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f id(\<nat>\<^sub>c)))\<^sup>\<sharp>  =  
                     ((exp_uncurried \<circ>\<^sub>c (id(\<nat>\<^sub>c) \<times>\<^sub>f mult2)) \<circ>\<^sub>c (associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>"
  proof(etcs_rule natural_number_object_func_unique[where X = "\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>",
        where f = "(mult2 \<circ>\<^sub>c \<langle>(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)), exp_uncurried \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>))\<rangle>)\<^sup>\<sharp>"])
    show "(exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero =
    ((exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero"
    proof(etcs_rule same_evals_equal[where Z = \<one>, where X = "\<nat>\<^sub>c", where A = "\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"])
      show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero =
    eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f ((exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero"
      proof(etcs_rule one_separator[where X = "(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<one>", where Y = "\<nat>\<^sub>c"])
        show "\<And>x. x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<one> \<Longrightarrow>
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f ((exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x"
        proof - 
          fix x 
          assume x_type[type_rule]: "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<one>"
          then obtain m n  where m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c" and n_type[type_rule]:  "n \<in>\<^sub>c \<nat>\<^sub>c" and x_def: "x =  \<langle>\<langle>m, n\<rangle>, id \<one>\<rangle>"
            by (typecheck_cfuncs, metis cart_prod_decomp terminal_func_unique)      
          have "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x = 
                ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, metis inv_transpose_func_def3 inv_transpose_of_composition)
          also have "... = ((exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, simp add: transpose_func_def)
          also have "... = (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero) \<circ>\<^sub>c \<langle>\<langle>m, n\<rangle>, id \<one>\<rangle>"
            by (typecheck_cfuncs, metis comp_associative2 x_def)
          also have "... = (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>m, n\<rangle>, zero \<circ>\<^sub>c id \<one>\<rangle>"
            using cfunc_cross_prod_comp_cfunc_prod  by (typecheck_cfuncs, auto)
          also have "... = (exp_uncurried \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>\<langle>m,n\<rangle>, zero\<rangle>"
            by (typecheck_cfuncs, metis id_left_unit2 id_right_unit2)
          also have "... = exp_uncurried \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>m,n\<rangle>, zero\<rangle>"
            using comp_associative2  by (typecheck_cfuncs, auto)
          also have "... = exp_uncurried \<circ>\<^sub>c  \<langle>exp_uncurried \<circ>\<^sub>c \<langle>m,n\<rangle> ,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero\<rangle>" 
            by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod)
          also have "... = exp_uncurried \<circ>\<^sub>c  \<langle>exp_uncurried \<circ>\<^sub>c \<langle>m,n\<rangle> ,zero\<rangle>"
            using id_left_unit2 zero_type by auto
          also have "... = (m ^\<^sub>\<nat> n) ^\<^sub>\<nat> zero"
            by (simp add: exp_def)
          also have "... =  m ^\<^sub>\<nat> zero"
            using exp_respects_Zero_Left by (typecheck_cfuncs, presburger)
          also have "... = m ^\<^sub>\<nat> (n \<cdot>\<^sub>\<nat> zero)"
            by (typecheck_cfuncs, simp add:  mult_respects_zero_right)
          also have "... = exp_uncurried \<circ>\<^sub>c \<langle>m, mult2 \<circ>\<^sub>c\<langle>n, zero\<rangle>\<rangle>"
            by (simp add: exp_def mult_def)
          also have "... = exp_uncurried \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m, mult2 \<circ>\<^sub>c\<langle>n, zero\<rangle>\<rangle>"
            using id_left_unit2  by (typecheck_cfuncs, auto)
          also have "... = exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c  \<langle>m,\<langle>n, zero\<rangle>\<rangle>"
            by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod)
          also have "... = (exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c  \<langle>m,\<langle>n, zero\<rangle>\<rangle>"
            using comp_associative2  by (typecheck_cfuncs, blast)
          also have "... = (exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  \<langle> \<langle>m,n\<rangle>, zero\<rangle>"
           using associate_right_ap  by (typecheck_cfuncs, auto)
          also have "... = (exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c  \<langle>m,n\<rangle>, zero \<circ>\<^sub>c id \<one>\<rangle>"
            by (typecheck_cfuncs, metis id_left_unit2 id_right_unit2)
          also have "... = (exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod x_def)
          also have "... = ((exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero) \<circ>\<^sub>c x"
            using comp_associative2  by (typecheck_cfuncs, blast)
          also have "... =  ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f ((exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero)) \<circ>\<^sub>c x"
            using comp_associative2 transpose_func_def  by (typecheck_cfuncs, auto)
          also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f ((exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x" 
            by (typecheck_cfuncs, metis inv_transpose_func_def3 inv_transpose_of_composition)
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
    proof(etcs_rule same_evals_equal[where Z = "\<nat>\<^sub>c", where X = "\<nat>\<^sub>c", where A = "\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"])
      show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor =
            eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),exp_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
      proof(etcs_rule one_separator[where X = "(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c", where Y = "\<nat>\<^sub>c"])
        show "\<And>x. x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),exp_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c x"
        proof -
          fix x 
          assume x_type[type_rule]: "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c"         
          then obtain y t where y_type[type_rule]: "y \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c" and t_type[type_rule]: "t \<in>\<^sub>c \<nat>\<^sub>c" and x_def: "x = \<langle>y,t\<rangle>"
            using cart_prod_decomp by blast
          then obtain m n where m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c" and n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c" and y_def: "y = \<langle>m,n\<rangle>"
            using cart_prod_decomp by blast
          obtain F where F_def: "F = (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f  (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>)"
              and  F_type[type_rule]: "F: (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)"
            by (typecheck_cfuncs, blast)
          have "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
                ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor)) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, metis inv_transpose_func_def3 inv_transpose_of_composition)
          also have "... = ((exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor)) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, simp add: transpose_func_def)
          also have "... = (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor) \<circ>\<^sub>c \<langle>y,t\<rangle>"
            by (typecheck_cfuncs, metis comp_associative2 x_def)
          also have "... =  (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c y,successor \<circ>\<^sub>c t\<rangle>"
            using cfunc_cross_prod_comp_cfunc_prod  by (typecheck_cfuncs, auto)
          also have "... =  (exp_uncurried \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>y,successor \<circ>\<^sub>c t\<rangle>"
            using id_left_unit2  by (typecheck_cfuncs, auto)
          also have "... =  exp_uncurried \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)  \<circ>\<^sub>c \<langle>y,successor \<circ>\<^sub>c t\<rangle>"
            using comp_associative2 by (typecheck_cfuncs, auto)
          also have "... =  exp_uncurried \<circ>\<^sub>c   \<langle>exp_uncurried \<circ>\<^sub>c  y,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (successor \<circ>\<^sub>c t)\<rangle>"
            by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod)
          also have "... =  exp_uncurried \<circ>\<^sub>c   \<langle>exp_uncurried \<circ>\<^sub>c  y, (successor \<circ>\<^sub>c t)\<rangle>"
            using id_left_unit2 x_def by (typecheck_cfuncs, fastforce)
          also have "... = (m ^\<^sub>\<nat> n) ^\<^sub>\<nat> (successor \<circ>\<^sub>c t)"
            using y_def by (typecheck_cfuncs, simp add: exp_def)
          also have "... =((m ^\<^sub>\<nat> n)^\<^sub>\<nat> t) \<cdot>\<^sub>\<nat> (m ^\<^sub>\<nat> n)"
            by (typecheck_cfuncs, simp add: exp_closure exp_respects_successor mult_commutative)
          also have "... = mult2 \<circ>\<^sub>c (\<langle>exp_uncurried \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c y,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c t\<rangle>, exp_uncurried \<circ>\<^sub>c y\<rangle>)"
            using exp_def id_left_unit2 mult_def y_def by (typecheck_cfuncs, presburger)
          also have "... = mult2 \<circ>\<^sub>c (\<langle>exp_uncurried \<circ>\<^sub>c ((exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c x), exp_uncurried \<circ>\<^sub>c y\<rangle>)"
            using cfunc_cross_prod_comp_cfunc_prod x_def by (typecheck_cfuncs, auto)
          also have "... = mult2 \<circ>\<^sub>c (\<langle>(exp_uncurried \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c x, exp_uncurried \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c x \<rangle>)"
            by (typecheck_cfuncs, metis cfunc_type_def comp_associative left_cart_proj_cfunc_prod t_type x_def)
          also have "... = mult2 \<circ>\<^sub>c (\<langle>(exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c), exp_uncurried \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c x)"
            using cfunc_prod_comp comp_associative2 x_type by (typecheck_cfuncs, auto)
          also have "... = (mult2 \<circ>\<^sub>c \<langle>(exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c), exp_uncurried \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>) \<circ>\<^sub>c x"
            using comp_associative2 id_left_unit2 x_type by (typecheck_cfuncs, auto)
          also have "... = (mult2 \<circ>\<^sub>c \<langle>(exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c), exp_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>) \<circ>\<^sub>c F\<rangle>) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, smt (verit, ccfv_threshold) F_def left_cart_proj_cfunc_cross_prod transpose_func_type)
          also have "... = (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c F, (exp_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)) \<circ>\<^sub>c F\<rangle>) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, metis F_def F_type comp_associative2 transpose_func_def)
          also have "... = (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),exp_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle> \<circ>\<^sub>c F) \<circ>\<^sub>c x"
            using F_type cfunc_prod_comp by (typecheck_cfuncs, auto)
          also have "... = ((mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),exp_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)
                                    \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f  (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>)) \<circ>\<^sub>c x"
            using F_def comp_associative2 by (typecheck_cfuncs, auto)
          also have "... = ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),exp_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f  (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>)) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, simp add: transpose_func_def)
          also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),exp_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, metis inv_transpose_func_def3 inv_transpose_of_composition)
          then show " (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),exp_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c exp_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c x"
            by (simp add: calculation)
        qed
      qed
    qed
    show "((exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c
    successor =
    (mult2 \<circ>\<^sub>c
     \<langle>eval_func \<nat>\<^sub>c
       (\<nat>\<^sub>c \<times>\<^sub>c
        \<nat>\<^sub>c),exp_uncurried \<circ>\<^sub>c
              left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
    ((exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
    proof(etcs_rule same_evals_equal[where Z = "\<nat>\<^sub>c", where X = "\<nat>\<^sub>c", where A = "\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"])
      show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f ((exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor =
  eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),exp_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c ((exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
      proof(etcs_rule one_separator[where X = "(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c", where Y = "\<nat>\<^sub>c"])
        show "\<And>x. x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f ((exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),exp_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c ((exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c x"
        proof - 
          fix x 
          assume x_type[type_rule]: "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c"
          then obtain y t where y_type[type_rule]: "y \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c" and t_type[type_rule]: "t \<in>\<^sub>c \<nat>\<^sub>c" and x_def: "x = \<langle>y,t\<rangle>"
            using cart_prod_decomp by blast
          then obtain m n where m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c" and n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c" and y_def: "y = \<langle>m,n\<rangle>"
            using cart_prod_decomp by blast          
          obtain F where F_def: "F = ((exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2)) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)"
              and  F_type[type_rule]: "F: (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
            by (typecheck_cfuncs, blast)
          obtain G where G_def: "G = (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f F\<^sup>\<sharp>)"
              and G_type[type_rule]: "G : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
            by (typecheck_cfuncs, blast)
          
          have "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f ((exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
                ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f ((exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c(id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor)) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, metis inv_transpose_func_def3 inv_transpose_of_composition)
          also have "... = ((exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c(id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor) \<circ>\<^sub>c x"
            using comp_associative2 transpose_func_def x_type by (typecheck_cfuncs, auto)
          also have "... = ((exp_uncurried \<circ>\<^sub>c ((id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c))) \<circ>\<^sub>c(id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor) \<circ>\<^sub>c x"
            using comp_associative2 by (typecheck_cfuncs, auto)
          also have "... = ((exp_uncurried \<circ>\<^sub>c ((id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c))) \<circ>\<^sub>c   \<langle>id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c  y,successor \<circ>\<^sub>c t\<rangle>"
            using cfunc_cross_prod_comp_cfunc_prod x_def by (typecheck_cfuncs, auto)
          also have "... = ((exp_uncurried \<circ>\<^sub>c ((id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c))) \<circ>\<^sub>c   \<langle>\<langle>m,n\<rangle>,successor \<circ>\<^sub>c t\<rangle>"
            by (typecheck_cfuncs, metis id_left_unit2 y_def)
          also have "... = exp_uncurried \<circ>\<^sub>c ((id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c   \<langle>\<langle>m,n\<rangle>,successor \<circ>\<^sub>c t\<rangle>)"
            by (typecheck_cfuncs, metis cfunc_type_def comp_associative y_def)
          also have "... = exp_uncurried \<circ>\<^sub>c ((id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c  \<langle>m,\<langle>n,successor \<circ>\<^sub>c t\<rangle>\<rangle>)"
            using associate_right_ap x_def y_def by (typecheck_cfuncs, auto)
          also have "... = exp_uncurried \<circ>\<^sub>c  \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m,mult2 \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c t\<rangle>\<rangle>"
            by (typecheck_cfuncs, smt (z3) cfunc_cross_prod_comp_cfunc_prod y_def)
          also have "... = exp_uncurried \<circ>\<^sub>c  \<langle>m,mult2 \<circ>\<^sub>c \<langle>n,successor \<circ>\<^sub>c t\<rangle>\<rangle>"
            using id_left_unit2  by (typecheck_cfuncs, auto)
          also have "... = m ^\<^sub>\<nat>(n \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c t))"
            by (simp add: exp_def mult_def)
          also have "... = m ^\<^sub>\<nat> ( (n \<cdot>\<^sub>\<nat> t) +\<^sub>\<nat> n)"
            by (typecheck_cfuncs, simp add: exp_closure exp_right_dist mult_closure mult_commutative mult_respects_succ_right y_def)
          also have "... =  (m ^\<^sub>\<nat> (n \<cdot>\<^sub>\<nat> t) )  \<cdot>\<^sub>\<nat> (m ^\<^sub>\<nat> n)"
            by (typecheck_cfuncs, simp add: exp_right_dist mult_closure)
          also have "... = mult2 \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>id\<^sub>c(\<nat>\<^sub>c) \<circ>\<^sub>c m,mult2 \<circ>\<^sub>c \<langle>n,t\<rangle>\<rangle> ,exp_uncurried \<circ>\<^sub>c  y \<rangle>"
            using exp_def id_left_unit2 mult_def y_def by (typecheck_cfuncs, presburger)
          also have "... = mult2 \<circ>\<^sub>c \<langle>(exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2)) \<circ>\<^sub>c \<langle>m,\<langle>n,t\<rangle>\<rangle> ,exp_uncurried \<circ>\<^sub>c  y \<rangle>"
            by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod comp_associative2 )
          also have "... = mult2 \<circ>\<^sub>c \<langle>(exp_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2)) \<circ>\<^sub>c( associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c x) ,exp_uncurried \<circ>\<^sub>c  y \<rangle>"
            using associate_right_ap x_def y_def by (typecheck_cfuncs, presburger)
          also have "... = mult2 \<circ>\<^sub>c \<langle>F \<circ>\<^sub>c x ,exp_uncurried \<circ>\<^sub>c   (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c x \<rangle>"
            by (typecheck_cfuncs, simp add: F_def comp_associative2 left_cart_proj_cfunc_prod t_type x_def)
          also have "... = mult2 \<circ>\<^sub>c \<langle>F ,exp_uncurried \<circ>\<^sub>c   (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)  \<rangle> \<circ>\<^sub>c x"
            using F_type cfunc_prod_comp comp_associative2 x_type by (typecheck_cfuncs, auto)
          also have "... = (mult2 \<circ>\<^sub>c \<langle>F ,exp_uncurried \<circ>\<^sub>c   id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)  \<rangle>) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, metis  comp_associative2 id_left_unit2)
          also have "... = (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c G ,exp_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>) \<circ>\<^sub>c G \<rangle>) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, metis (full_types) G_def left_cart_proj_cfunc_cross_prod transpose_func_def transpose_func_type)
          also have "... = (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),exp_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle> \<circ>\<^sub>c G) \<circ>\<^sub>c x"
            using G_type cfunc_prod_comp comp_associative2 by (typecheck_cfuncs, auto)
          also have "... = ((mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),exp_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>) \<circ>\<^sub>c G) \<circ>\<^sub>c x"
            using G_type comp_associative2 by (typecheck_cfuncs, auto)
          also have "... = ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),exp_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c(id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f F\<^sup>\<sharp>)) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, simp add: G_def transpose_func_def)
          also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),exp_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c F\<^sup>\<sharp>) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, metis inv_transpose_func_def3 inv_transpose_of_composition)
          then show " (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f ((exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c),exp_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c ((exp_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c x"
            by (simp add: F_def calculation)
        qed
      qed
    qed
  qed
  then have main_result_flat: "(exp_uncurried \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f id(\<nat>\<^sub>c)))  =  
                     ((exp_uncurried \<circ>\<^sub>c (id(\<nat>\<^sub>c) \<times>\<^sub>f mult2)) \<circ>\<^sub>c (associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c))"
    by (typecheck_cfuncs, metis flat_cancels_sharp main_result)
  have "(a ^\<^sub>\<nat> b)^\<^sub>\<nat> c = exp_uncurried \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a,b\<rangle>, id(\<nat>\<^sub>c) \<circ>\<^sub>c c\<rangle>"
    using assms(3) exp_def id_left_unit2 by auto
  also have "... =  exp_uncurried \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f id(\<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, c\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
  also have "... =  (exp_uncurried \<circ>\<^sub>c (exp_uncurried \<times>\<^sub>f id(\<nat>\<^sub>c))) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, c\<rangle>"
    using assms by (typecheck_cfuncs, meson comp_associative2)
  also have "... = ((exp_uncurried \<circ>\<^sub>c (id(\<nat>\<^sub>c) \<times>\<^sub>f mult2)) \<circ>\<^sub>c (associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, c\<rangle>"
    using main_result_flat by auto
  also have "... = exp_uncurried \<circ>\<^sub>c ((id(\<nat>\<^sub>c) \<times>\<^sub>f mult2) \<circ>\<^sub>c (associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, c\<rangle>"
    using assms by (typecheck_cfuncs, smt comp_associative2)
  also have "... = exp_uncurried \<circ>\<^sub>c ((id(\<nat>\<^sub>c) \<times>\<^sub>f mult2) \<circ>\<^sub>c (associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, c\<rangle>)"
    using assms comp_associative2 by (typecheck_cfuncs, auto)
  also have "... = exp_uncurried \<circ>\<^sub>c ((id(\<nat>\<^sub>c) \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>a,\<langle>b, c\<rangle>\<rangle>)"
    using assms associate_right_ap by auto
  also have "... = exp_uncurried \<circ>\<^sub>c   \<langle>id(\<nat>\<^sub>c) \<circ>\<^sub>c a,mult2 \<circ>\<^sub>c \<langle>b, c\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
  also have "... = (a^\<^sub>\<nat> (b \<cdot>\<^sub>\<nat> c))"
    using assms(1) exp_def id_left_unit2 mult_def by auto
  then show ?thesis
    by (simp add: calculation)
qed



(*Powers of two and three*)

lemma powers_of_two_are_even:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c" 
  assumes "n \<noteq> zero"
  shows "is_even \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c   \<langle>successor \<circ>\<^sub>csuccessor  \<circ>\<^sub>c zero,n\<rangle>) = \<t>"
proof - 
  obtain j where j_type[type_rule]: "j \<in>\<^sub>c \<nat>\<^sub>c" and j_def: "n = successor \<circ>\<^sub>c j"
    using assms nonzero_is_succ by blast
  have "exp_uncurried \<circ>\<^sub>c   \<langle>successor \<circ>\<^sub>csuccessor  \<circ>\<^sub>c zero,n\<rangle> = exp_uncurried \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>csuccessor  \<circ>\<^sub>c zero, (successor  \<circ>\<^sub>c zero) +\<^sub>\<nat> j\<rangle>"
    by (typecheck_cfuncs, metis add_commutes add_respects_succ3 add_respects_zero_on_right j_def)
  also have "... = ((successor \<circ>\<^sub>csuccessor  \<circ>\<^sub>c zero) ^\<^sub>\<nat> (successor  \<circ>\<^sub>c zero)) \<cdot>\<^sub>\<nat> ((successor \<circ>\<^sub>csuccessor  \<circ>\<^sub>c zero) ^\<^sub>\<nat> j)"
    using exp_def exp_right_dist by (typecheck_cfuncs, force)
  also have "... = (successor \<circ>\<^sub>csuccessor  \<circ>\<^sub>c zero)  \<cdot>\<^sub>\<nat> ((successor \<circ>\<^sub>csuccessor  \<circ>\<^sub>c zero) ^\<^sub>\<nat> j)"
    by (typecheck_cfuncs, simp add: exp_respects_one_right)
  then show ?thesis
    by (metis calculation exp_closure j_type mult_evens_is_even2 prod_of_consecutive_nats_is_even s0_is_left_id succ_n_type zero_type)
qed


lemma three_is_odd:
  "is_odd \<circ>\<^sub>c (successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor  \<circ>\<^sub>c zero) = \<t>"
  by (typecheck_cfuncs, metis (full_types) comp_associative2 is_even_not_is_odd is_odd_def2 prod_of_consecutive_nats_is_even s0_is_left_id)





lemma powers_of_three_are_odd:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c" 
  shows "is_odd \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c   \<langle>successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor  \<circ>\<^sub>c zero,n\<rangle>) = \<t>"
proof - 
  have main_result: "is_odd \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c   \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor  \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id \<nat>\<^sub>c\<rangle>) = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
  proof(etcs_rule natural_number_object_func_unique[where X = "\<Omega>", where f = "id \<Omega>" ]) 
    show "(is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero"
    proof - 
      have "(is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero = 
             is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c zero"
        using comp_associative2 by (typecheck_cfuncs, force)
      also have "... = is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c zero ,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero\<rangle> "
        using cfunc_prod_comp comp_associative2 by (typecheck_cfuncs, force)
      also have "... = is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero, zero\<rangle>"
        by (typecheck_cfuncs, metis beta_N_succ_nEqs_Id1 id_left_unit2 id_right_unit2 terminal_func_comp)
      also have "... = is_odd \<circ>\<^sub>c (successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)"
        by (typecheck_cfuncs, metis even_or_odd exp_def exp_respects_Zero_Left mult_evens_is_even2 not_even_and_odd s0_is_left_id three_is_odd)
      also have "... = \<t>"
        by (simp add: three_is_odd)
      then show ?thesis
        by (metis calculation cfunc_type_def comp_associative is_even_def2 is_even_nth_even_true nth_even_def2 zero_type)
    qed
    show "(is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor =  id\<^sub>c \<Omega> \<circ>\<^sub>c is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
    proof(etcs_rule one_separator[where X = "\<nat>\<^sub>c", where Y = "\<Omega>"])
      show "\<And>x. x \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
         ((is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
         (id\<^sub>c \<Omega> \<circ>\<^sub>c is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c x"
      proof - 
        fix m
        assume m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c"
        have " (id\<^sub>c \<Omega> \<circ>\<^sub>c is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c m = 
                (is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>)  \<circ>\<^sub>c m"  
          using id_left_unit2 by (typecheck_cfuncs, presburger)
        also have "... = is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>  \<circ>\<^sub>c m"
          by (typecheck_cfuncs, metis cfunc_type_def comp_associative)
        also have "... = is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m ,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m\<rangle>"
          using cfunc_prod_comp comp_associative2 by (typecheck_cfuncs, auto)
        also have "... = is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) ,m\<rangle>"
          by (typecheck_cfuncs, metis id_left_unit2 id_right_unit2 id_type one_unique_element)
        also have "... = ((is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor) \<circ>\<^sub>c m"
        proof(cases "is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) ,m\<rangle> = \<t>")
          assume real_case: "is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) ,m\<rangle> = \<t>"  (*The only real case*)
          have "((is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor) \<circ>\<^sub>c m = 
                 (is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c (successor \<circ>\<^sub>c m)"
            by (typecheck_cfuncs, simp add: comp_associative2)
          also have "...  =  (is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c (m +\<^sub>\<nat> (successor \<circ>\<^sub>c zero))"
            by (typecheck_cfuncs, metis add_commutes add_respects_succ3 add_respects_zero_on_left)
          also have "... =  is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (m +\<^sub>\<nat> (successor \<circ>\<^sub>c zero))"
            by (typecheck_cfuncs, metis cfunc_type_def comp_associative)
          also have "... =  is_odd \<circ>\<^sub>c ((exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c m) \<cdot>\<^sub>\<nat> 
                                       (exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (successor \<circ>\<^sub>c zero)))"
            by (typecheck_cfuncs, metis exp_apply1 exp_right_dist)
          also have "... = \<t>"
            by (typecheck_cfuncs, metis real_case exp_apply1 exp_def exp_respects_one_right mult_odds_is_odd2 three_is_odd)
          then show ?thesis
            using calculation real_case by presburger
        next
          assume "is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero,m\<rangle> \<noteq> \<t>"
          then have fake_case: "is_even \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero,m\<rangle> = \<t>"   (*The fake case... only difference is final line!*)
            by (metis even_or_odd exp_closure exp_def m_type succ_n_type zero_type)
          have "((is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor) \<circ>\<^sub>c m = 
                 (is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c (successor \<circ>\<^sub>c m)"
            by (typecheck_cfuncs, simp add: comp_associative2)
          also have "...  =  (is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c (m +\<^sub>\<nat> (successor \<circ>\<^sub>c zero))"
            by (typecheck_cfuncs, metis add_commutes add_respects_succ3 add_respects_zero_on_left)
          also have "... =  is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (m +\<^sub>\<nat> (successor \<circ>\<^sub>c zero))"
            by (typecheck_cfuncs, metis cfunc_type_def comp_associative)
          also have "... =  is_odd \<circ>\<^sub>c ((exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c m) \<cdot>\<^sub>\<nat> 
                                       (exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (successor \<circ>\<^sub>c zero)))"
            by (typecheck_cfuncs, metis exp_apply1 exp_right_dist)
          also have "... = \<f>"
            by (typecheck_cfuncs, metis cart_prod_extract_right fake_case mult_evens_is_even2 not_even_and_odd true_false_only_truth_values)
          then show ?thesis
            by (metis NOT_true_is_false NOT_type calculation cfunc_type_def comp_associative exp_closure exp_def fake_case is_even_type is_odd_not_is_even m_type succ_n_type zero_type)
        qed
        then show "((is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor) \<circ>\<^sub>c m =
         (id\<^sub>c \<Omega> \<circ>\<^sub>c is_odd \<circ>\<^sub>c exp_uncurried \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c m"
          by (simp add: calculation)
      qed
    qed
    show "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor = id\<^sub>c \<Omega> \<circ>\<^sub>c \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
      by (typecheck_cfuncs, smt (z3) comp_associative2 id_left_unit2 terminal_func_comp)
  qed
  have "is_odd \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c   \<langle>successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor  \<circ>\<^sub>c zero,n\<rangle>) = 
        (is_odd \<circ>\<^sub>c (exp_uncurried \<circ>\<^sub>c   \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor  \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id \<nat>\<^sub>c\<rangle>)) \<circ>\<^sub>c n"
    using assms cfunc_type_def comp_associative exp_apply1 exp_def by (typecheck_cfuncs, fastforce)
  then show ?thesis
    by (typecheck_cfuncs, smt (z3) main_result assms beta_N_succ_nEqs_Id1 comp_associative2 id_right_unit2 terminal_func_comp terminal_func_type)
qed


(*From "Ordinal_Inequalities" *)

lemma exp_leq_preserving: 
  assumes a_type[type_rule]: "a \<in>\<^sub>c \<nat>\<^sub>c" and b_type[type_rule]: "b \<in>\<^sub>c \<nat>\<^sub>c" and c_type[type_rule]: "c \<in>\<^sub>c \<nat>\<^sub>c"
  assumes a_leq_b: "leq \<circ>\<^sub>c \<langle>a, b\<rangle> = \<t>"
  shows "(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>, exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c c  = \<t>"
proof(etcs_rule nat_induction)
  show "(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id\<^sub>c \<nat>\<^sub>c\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c zero = \<t>"
    by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 exp_apply1 exp_respects_Zero_Left lqe_connexity succ_n_type)
  show "\<And>n. n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
         (leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c n = \<t> \<Longrightarrow>
         (leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c n = \<t>"
  proof - 
    fix n 
    assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
    assume ind_hyp: "(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c n = \<t>"
    have "a ^\<^sub>\<nat> n \<le>\<^sub>\<nat> b ^\<^sub>\<nat> n"
    proof - 
      have "(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c n = 
             leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c n,exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c n\<rangle> "
        by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2)
      also have "... = leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a, n\<rangle> ,exp_uncurried \<circ>\<^sub>c \<langle>b, n\<rangle>\<rangle>"
        by (typecheck_cfuncs, metis cart_prod_extract_right)
      then show ?thesis
        using calculation exp_def ind_hyp leq_infix_def by presburger
    qed
    then have "a ^\<^sub>\<nat> (successor \<circ>\<^sub>c n) \<le>\<^sub>\<nat> b ^\<^sub>\<nat> (successor \<circ>\<^sub>c n)"
      using  a_leq_b exp_closure exp_respects_successor leq_infix_def mult_monotonic by (typecheck_cfuncs, force)
    then show "(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>, exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c n = \<t>"
      by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 exp_apply1 leq_infix_def)
  qed
qed

lemma exp_leq_preserving': 
  assumes a_type[type_rule]: "a \<in>\<^sub>c \<nat>\<^sub>c" and b_type[type_rule]: "b \<in>\<^sub>c \<nat>\<^sub>c" and c_type[type_rule]: "c \<in>\<^sub>c \<nat>\<^sub>c"
  shows "a \<le>\<^sub>\<nat> b \<Longrightarrow> a ^\<^sub>\<nat> c \<le>\<^sub>\<nat> b ^\<^sub>\<nat> c"
proof(unfold leq_infix_def exp_def)
  have "(leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>, exp_uncurried \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c c = 
         leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a,c\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b,c\<rangle>\<rangle>"
    by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2 id_left_unit2 id_right_unit2 terminal_func_comp_elem)
  then show "leq \<circ>\<^sub>c \<langle>a,b\<rangle> = \<t> \<Longrightarrow> leq \<circ>\<^sub>c \<langle>exp_uncurried \<circ>\<^sub>c \<langle>a,c\<rangle>,exp_uncurried \<circ>\<^sub>c \<langle>b,c\<rangle>\<rangle> = \<t>"
    by (typecheck_cfuncs, metis exp_leq_preserving)
qed

lemma nonzero_to_k_nonzero:
  assumes "a \<in>\<^sub>c \<nat>\<^sub>c" "k \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "a \<noteq> zero"
  shows "a ^\<^sub>\<nat> k \<noteq> zero"
proof - 
  have "leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero, a\<rangle> = \<t>"
    by (metis add_respects_succ2 add_respects_zero_on_right assms(1,3) exists_implies_leq_true nonzero_is_succ succ_n_type zero_type)
  then have "leq \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c zero) ^\<^sub>\<nat> k, a ^\<^sub>\<nat> k\<rangle> = \<t>"
    by (typecheck_cfuncs, meson assms exp_leq_preserving' leq_infix_def)
  then show "a ^\<^sub>\<nat> k \<noteq> zero"
    using  assms(2) exp_respects_one_left lqe_antisymmetry succ_n_type zero_is_not_successor zero_is_smallest by(typecheck_cfuncs, force)
qed

lemma exp_order_preserving:
  assumes a_type[type_rule]: "a \<in>\<^sub>c \<nat>\<^sub>c" and b_type[type_rule]: "b \<in>\<^sub>c \<nat>\<^sub>c" and c_type[type_rule]: "c \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "a ^\<^sub>\<nat> (successor \<circ>\<^sub>c c) = b ^\<^sub>\<nat> (successor \<circ>\<^sub>c c)"
  shows "a = b"
proof(rule ccontr)
  assume "a \<noteq> b"
  show False
  proof(cases "a \<le>\<^sub>\<nat> b")
    case True
    then have "leq \<circ>\<^sub>c \<langle>a ^\<^sub>\<nat> (successor \<circ>\<^sub>c c),b ^\<^sub>\<nat> (successor \<circ>\<^sub>c c)\<rangle> = \<t>"
      by (typecheck_cfuncs, meson exp_leq_preserving' leq_infix_def)
    then have f1: "leq \<circ>\<^sub>c \<langle>a ^\<^sub>\<nat> (successor \<circ>\<^sub>c c),a \<cdot>\<^sub>\<nat> (b ^\<^sub>\<nat> c)\<rangle> = \<t>"
      by (typecheck_cfuncs, metis True exp_closure exp_leq_preserving' exp_respects_successor leq_infix_def lqe_connexity mult_monotonic)
    have f2: "leq \<circ>\<^sub>c \<langle>a \<cdot>\<^sub>\<nat> (b ^\<^sub>\<nat> c), b ^\<^sub>\<nat> (successor \<circ>\<^sub>c c)\<rangle> = \<t>"
      by (typecheck_cfuncs, metis True exp_respects_successor leq_infix_def lqe_connexity mult_monotonic) 
    have f3: "a \<cdot>\<^sub>\<nat> (b ^\<^sub>\<nat> c) \<noteq> b ^\<^sub>\<nat> (successor \<circ>\<^sub>c c)"
      by (typecheck_cfuncs, metis \<open>a \<noteq> b\<close> assms(4) exp_respects_successor exp_respects_zero_left mult_cancellative nonzero_to_k_nonzero)
    have "a \<cdot>\<^sub>\<nat> (b ^\<^sub>\<nat> c) = b ^\<^sub>\<nat> (successor \<circ>\<^sub>c c)"
      using a_type assms(4) b_type c_type exp_closure f1 f2 lqe_antisymmetry mult_type succ_n_type by presburger
    then show ?thesis
      using f3 by blast
  next
    case False 
    then have "b \<le>\<^sub>\<nat> a"
      using a_type b_type leq_infix_def lqe_connexity by auto
    then have f0: "leq \<circ>\<^sub>c \<langle>b ^\<^sub>\<nat> (successor \<circ>\<^sub>c c),a ^\<^sub>\<nat> (successor \<circ>\<^sub>c c)\<rangle> = \<t>"
      by (typecheck_cfuncs, meson exp_leq_preserving' leq_infix_def)
    then have f1: "leq \<circ>\<^sub>c \<langle>b ^\<^sub>\<nat> (successor \<circ>\<^sub>c c),b \<cdot>\<^sub>\<nat> (a ^\<^sub>\<nat> c)\<rangle> = \<t>"
      by (typecheck_cfuncs, metis False exp_closure exp_leq_preserving' exp_respects_successor leq_infix_def lqe_connexity mult_monotonic)
    have f2: "leq \<circ>\<^sub>c \<langle>b \<cdot>\<^sub>\<nat> (a ^\<^sub>\<nat> c), a ^\<^sub>\<nat> (successor \<circ>\<^sub>c c)\<rangle> = \<t>"
      by (typecheck_cfuncs, metis False exp_respects_successor leq_infix_def lqe_connexity mult_monotonic) 
    have f3: "b \<cdot>\<^sub>\<nat> (a ^\<^sub>\<nat> c) \<noteq> a ^\<^sub>\<nat> (successor \<circ>\<^sub>c c)"
      by (typecheck_cfuncs, metis \<open>a \<noteq> b\<close> assms(4) exp_respects_successor exp_respects_zero_left mult_cancellative nonzero_to_k_nonzero)
    have f4: "b \<cdot>\<^sub>\<nat> (a ^\<^sub>\<nat> c) = a ^\<^sub>\<nat> (successor \<circ>\<^sub>c c)"
      using a_type assms(4) b_type c_type exp_closure f1 f2 lqe_antisymmetry mult_type succ_n_type by presburger
    then show ?thesis
      using f3 by blast  
  qed
qed

lemma exp_order_preserving':
  assumes a_type[type_rule]: "a \<in>\<^sub>c \<nat>\<^sub>c" and b_type[type_rule]: "b \<in>\<^sub>c \<nat>\<^sub>c" and c_type[type_rule]: "c \<in>\<^sub>c \<nat>\<^sub>c"
  assumes nonzero_exp: "c \<noteq> zero"
  shows "(a = b) \<longleftrightarrow> (a ^\<^sub>\<nat> c = b ^\<^sub>\<nat> c)"
  by (typecheck_cfuncs, metis exp_order_preserving nonzero_exp nonzero_is_succ)



end