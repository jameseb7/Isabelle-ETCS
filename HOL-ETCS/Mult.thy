theory Mult
  imports Inequality
begin

(*Defining multiplication on N*)
  



definition mult1 :: "cfunc" where
  "mult1 = (THE v. v: \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<and>
    v \<circ>\<^sub>c zero = ((zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c \<one>))\<^sup>\<sharp>) \<and>
    v \<circ>\<^sub>c successor = ((add2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c v)"

lemma mult1_property: "mult1: \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<and>
    mult1 \<circ>\<^sub>c zero = ((zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c \<one>))\<^sup>\<sharp>) \<and>
    mult1 \<circ>\<^sub>c successor = ((add2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c mult1"
  unfolding mult1_def
  by (rule theI', typecheck_cfuncs, smt (verit, best) natural_number_object_property2)

lemma mult1_type[type_rule]: "mult1:  \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
  by (simp add: mult1_property)


lemma mult1_0_eq: "mult1 \<circ>\<^sub>c zero = ((zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c \<one>))\<^sup>\<sharp>)"
  by (simp add: mult1_property)




lemma mult1_comp_succ_eq: "mult1 \<circ>\<^sub>c successor =
  ((add2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c mult1"
  by (simp add: mult1_property)


definition mult2 :: "cfunc"
  where "mult2 = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f mult1)"

lemma mult2_type[type_rule]: "mult2:  \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c"
  unfolding mult2_def
  by typecheck_cfuncs



definition mult :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" (infixl "\<cdot>\<^sub>\<nat>" 70)
  where "m \<cdot>\<^sub>\<nat> n = mult2\<circ>\<^sub>c\<langle>m, n\<rangle>"

lemma mult_type[type_rule]:
  assumes "m : X \<rightarrow> \<nat>\<^sub>c" "n : X \<rightarrow> \<nat>\<^sub>c"
  shows "m \<cdot>\<^sub>\<nat> n : X \<rightarrow> \<nat>\<^sub>c"
  unfolding mult_def using assms by typecheck_cfuncs

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
  have "mult2 \<circ>\<^sub>c \<langle>m,n\<rangle> = mult2 \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c id \<one>  ,id \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>"
    by (metis assms cfunc_type_def id_left_unit id_right_unit)
  also have "... = mult2 \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c n)  ,id \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>"
    by (metis assms(2) comp_type id_type one_unique_element terminal_func_type)
  also have "... = mult2 \<circ>\<^sub>c \<langle>(m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c n  ,id \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>"
    using assms by (typecheck_cfuncs, simp add: comp_associative2)
  also have "... = mult2 \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<circ>\<^sub>c n"
    using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp)
  then show "mult2 \<circ>\<^sub>c \<langle>m,n\<rangle> = mult2 \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c n"
    using calculation by auto
qed

lemma mult_apply1_left:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n\<in>\<^sub>c \<nat>\<^sub>c"
  shows "m  \<cdot>\<^sub>\<nat>  n = mult2 \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<circ>\<^sub>c m"
  unfolding mult_def 
proof - 
  have "mult2 \<circ>\<^sub>c \<langle>m,n\<rangle> = mult2 \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c \<circ>\<^sub>c m, n \<circ>\<^sub>c id \<one>\<rangle>"
    by (metis assms cfunc_type_def id_left_unit id_right_unit)
  also have "... = mult2 \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c \<circ>\<^sub>c m, n \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m)\<rangle>"
    by (metis assms(1) comp_type id_type one_unique_element terminal_func_type)
  also have "... = mult2 \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c \<circ>\<^sub>c m, (n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c m\<rangle>"
    using assms by (typecheck_cfuncs, simp add: comp_associative2)
  also have "... = mult2 \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<rangle> \<circ>\<^sub>c m"
    using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp)
  then show "mult2 \<circ>\<^sub>c \<langle>m,n\<rangle> = mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c m"
    using calculation by auto
qed

lemma mult_closure[type_rule]:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n\<in>\<^sub>c \<nat>\<^sub>c"
  shows "m \<cdot>\<^sub>\<nat> n \<in>\<^sub>c \<nat>\<^sub>c"
  unfolding mult_def
  using assms by typecheck_cfuncs

lemma mult_respects_zero_right:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c"
  shows "m \<cdot>\<^sub>\<nat> zero = zero"
proof - 
  have "m \<cdot>\<^sub>\<nat> zero =  mult2\<circ>\<^sub>c\<langle>m, zero\<rangle>"
    by (simp add: mult_def)
  also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, mult1 \<circ>\<^sub>c zero\<rangle>"
    using assms calculation mult_def2 zero_type by auto
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, ((zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c \<one>))\<^sup>\<sharp>) \<rangle>"
    by (simp add: mult1_0_eq)
  also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f((zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c \<one>))\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>m, id\<^sub>c \<one>\<rangle>"
    using assms cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2 by (typecheck_cfuncs, force)
  also have "... = zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c \<one>) \<circ>\<^sub>c \<langle>m, id\<^sub>c \<one>\<rangle>"
    using assms by (typecheck_cfuncs , simp add: cfunc_type_def comp_associative transpose_func_def)
  also have "... = zero"
    by (metis assms cfunc_type_def id_right_unit id_type right_cart_proj_cfunc_prod zero_type)
then show ?thesis using calculation by auto
qed


lemma mult_respects_succ_right:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "m \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c n) = m +\<^sub>\<nat> (m \<cdot>\<^sub>\<nat> n)"
proof - 
  have "m \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c n) = mult2\<circ>\<^sub>c\<langle>m, (successor \<circ>\<^sub>c n)\<rangle>"
    by (simp add: mult_def)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult1)\<circ>\<^sub>c \<langle>m, (successor \<circ>\<^sub>c n)\<rangle>"
    using assms by (typecheck_cfuncs, simp add: comp_associative2 mult2_def)
  also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, mult1 \<circ>\<^sub>c (successor \<circ>\<^sub>c n)\<rangle>"
    using assms calculation mult_def2 by (typecheck_cfuncs, auto)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m,((add2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>)\<circ>\<^sub>c mult1 \<circ>\<^sub>c n\<rangle>"
    using assms comp_associative2 mult1_property by (typecheck_cfuncs, force)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m,((add2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>)\<circ>\<^sub>c mult1 \<circ>\<^sub>c n\<rangle>"
    using assms by (typecheck_cfuncs, simp add: id_left_unit2)
 also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>m,mult1 \<circ>\<^sub>c n\<rangle>"
   using assms cfunc_cross_prod_comp_cfunc_prod by (typecheck_cfuncs, auto)
  also have "... =(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>) )\<circ>\<^sub>c \<langle>m,mult1 \<circ>\<^sub>c n\<rangle>"
    using assms by (typecheck_cfuncs, simp add: comp_associative2)
  also have "... = (add2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m, mult1\<circ>\<^sub>c n\<rangle>"
    using assms by (typecheck_cfuncs, simp add: id_left_unit2 transpose_func_def)
  also have "... = add2  \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>))\<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m, mult1\<circ>\<^sub>c n\<rangle>,(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m, mult1\<circ>\<^sub>c n\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2)
  also have "...  = add2  \<circ>\<^sub>c \<langle>m,(eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m, mult1\<circ>\<^sub>c n\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: id_left_unit2 left_cart_proj_cfunc_prod)
  also have "... = add2  \<circ>\<^sub>c \<langle>m, (eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  mult1)\<circ>\<^sub>c \<langle>m,n\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
  also have "... = add2  \<circ>\<^sub>c \<langle>m, mult2 \<circ>\<^sub>c \<langle>m,n\<rangle>\<rangle>"
    using assms comp_associative2 mult2_def by (typecheck_cfuncs, force)
  also have "... =  m +\<^sub>\<nat> (m \<cdot>\<^sub>\<nat> n)"
    by (simp add: add_def mult_def)
  then show ?thesis using calculation by auto
qed

lemma mult2_respects_succ_right:
  assumes n_type[type_rule]: "n \<in>\<^sub>c  \<nat>\<^sub>c"
  shows "mult2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, successor\<rangle> = add2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, mult2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<rangle>"
proof (etcs_rule one_separator[where X="\<nat>\<^sub>c", where Y="\<nat>\<^sub>c"])
  fix x
  assume x_type: "x \<in>\<^sub>c \<nat>\<^sub>c"
  have "mult2 \<circ>\<^sub>c \<langle>n, successor \<circ>\<^sub>c x\<rangle> = add2 \<circ>\<^sub>c \<langle>n, mult2 \<circ>\<^sub>c \<langle>n, x\<rangle>\<rangle>"
    using add_def assms mult_def mult_respects_succ_right x_type by auto
  then have "mult2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c x,successor \<circ>\<^sub>c x\<rangle>
      = add2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c x,mult2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c x,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c x\<rangle>\<rangle>"
    using assms x_type by (typecheck_cfuncs, metis id_left_unit2 id_right_unit2 id_type one_unique_element)
  then show "(mult2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>) \<circ>\<^sub>c x = (add2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,mult2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c x"
    using assms x_type by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2)
qed


lemma s0_is_right_id:
  assumes "m\<in>\<^sub>c  \<nat>\<^sub>c" 
  shows "m \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = m"
  by (simp add: add_respects_zero_on_right assms mult_respects_succ_right mult_respects_zero_right zero_type)
(*Proof: m \<cdot>\<^sub>\<nat> S(0) = m +\<^sub>\<nat> (m \<cdot>\<^sub>\<nat> 0) = m +\<^sub>\<nat> 0 =m*)









lemma mult_respects_zero_left:
  assumes m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c" 
  shows "zero \<cdot>\<^sub>\<nat> m = zero"
proof - 
  have triangle1: "mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c zero = zero"
    using mult_apply1_left mult_respects_zero_right by (typecheck_cfuncs, presburger)
  have triangle2: "mult2 \<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id\<^sub>c \<nat>\<^sub>c \<rangle>  \<circ>\<^sub>c zero = zero"
    by (typecheck_cfuncs, metis (no_types) cart_prod_extract_left cart_prod_extract_right triangle1)

  have square1: "mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c successor
               = mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
  proof (etcs_rule one_separator[where X="\<nat>\<^sub>c", where Y="\<nat>\<^sub>c"])
    fix m
    assume assms: "m \<in>\<^sub>c \<nat>\<^sub>c"
    have "mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c successor \<circ>\<^sub>c m =
        mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor \<circ>\<^sub>c m, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor \<circ>\<^sub>c m\<rangle>"
      by (typecheck_cfuncs, metis assms cart_prod_extract_left id_left_unit2 id_right_unit2 terminal_func_comp_elem)
    also have "... = mult2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c m, zero\<rangle>"
      by (typecheck_cfuncs, metis assms calculation cart_prod_extract_left)
    also have "... = zero"
      using assms mult_def mult_respects_zero_right by (typecheck_cfuncs, auto)
    also have "... = mult2 \<circ>\<^sub>c \<langle>m, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m\<rangle>"
      using assms by (typecheck_cfuncs, metis id_right_unit2 id_type mult_def mult_respects_zero_right one_unique_element)
    also have "... = mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m\<rangle>"
      using assms by (typecheck_cfuncs, simp add: id_left_unit2)
    also have "... =  mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c m"
      using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
    then show "(mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c successor) \<circ>\<^sub>c m = (mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c m"
      using calculation comp_associative2 assms by (typecheck_cfuncs, auto)
  qed
  have "mult2 \<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c successor  = id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c
                 mult2 \<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
    by (typecheck_cfuncs, smt (z3) add2_respects_zero_on_left cfunc_prod_comp comp_associative2 
                                   id_left_unit2 mult2_respects_succ_right terminal_func_comp)
  then have zero_commutes: "mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> =  mult2 \<circ>\<^sub>c \<langle>zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
    by (typecheck_cfuncs, metis cfunc_type_def comp_associative id_left_unit2 natural_number_object_func_unique square1 successor_type triangle1 triangle2)
  then have "zero \<cdot>\<^sub>\<nat> m = m \<cdot>\<^sub>\<nat> zero"
    unfolding mult_def  by (-,typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2 id_left_unit2 id_right_unit2 terminal_func_comp_elem assms)
  then show ?thesis
    by (simp add: assms mult_respects_zero_right)
qed




lemma s0_is_left_id:
  assumes "m \<in>\<^sub>c  \<nat>\<^sub>c"
  shows  "(successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> m = m"
proof - 
  have triangle: "(mult2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> ,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero = zero"
  proof - 
    have "(mult2 \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> ,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero =  mult2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c zero, id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero\<rangle>"
      by(etcs_assocr,typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
    also have "... =  mult2 \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero , zero\<rangle>"
      by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2 terminal_func_comp_elem)    
    also have "... = zero"
      using mult_def mult_respects_zero_right by (typecheck_cfuncs, presburger)
    then show ?thesis using calculation by auto
   qed
  have square: "(mult2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor =
          successor \<circ>\<^sub>c (mult2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id\<^sub>c \<nat>\<^sub>c\<rangle>)"
  proof - 
    have "(mult2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor = 
            mult2 \<circ>\<^sub>c (\<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c successor)"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = mult2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor, id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor\<rangle>"
      by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
    also have "... = mult2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, successor\<rangle>"
      using id_left_unit2 successor_type terminal_func_comp by force
    also have "... = (eval_func \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult1) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, successor\<rangle>"
      using assms by (typecheck_cfuncs, simp add: comp_associative2 mult2_def)
    also have "... = (eval_func \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult1 \<circ>\<^sub>c successor)) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id\<^sub>c \<nat>\<^sub>c\<rangle>"
      using  cfunc_cross_prod_comp_cfunc_prod id_right_unit2 by (typecheck_cfuncs, smt)
    also have "... = (eval_func \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c mult1) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id\<^sub>c \<nat>\<^sub>c\<rangle>"
      using assms mult1_property by argo
    also have "... = ((eval_func \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c mult1)) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id\<^sub>c \<nat>\<^sub>c\<rangle>"
      using comp_associative2 by (typecheck_cfuncs, blast)
    also have "... = ((eval_func \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult1)) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id\<^sub>c \<nat>\<^sub>c\<rangle>"
      using identity_distributes_across_composition by (typecheck_cfuncs, auto)
    also have "... = ((eval_func \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)),(eval_func \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>)) \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult1) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id\<^sub>c \<nat>\<^sub>c\<rangle>"
      using  comp_associative2 by (typecheck_cfuncs, auto)
    also have "... = (add2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)), (eval_func \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle>) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult1) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id\<^sub>c \<nat>\<^sub>c\<rangle>"
      using  transpose_func_def by (typecheck_cfuncs, auto)
    also have "... = (add2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)), (eval_func \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle>) \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, mult1\<rangle>"
      by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2)
    also have "... = add2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)), (eval_func \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c  \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, mult1\<rangle>"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = add2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , mult1\<rangle>,(eval_func \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, mult1\<rangle>\<rangle>"
      by (typecheck_cfuncs, simp add: cfunc_prod_comp)
    also have "... = add2 \<circ>\<^sub>c \<langle> successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,(eval_func \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, mult1\<rangle>\<rangle>"
      using left_cart_proj_cfunc_prod by (typecheck_cfuncs, presburger)
    also have "... = add2 \<circ>\<^sub>c \<langle> successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,(eval_func \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, mult1 \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>"
      by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2)
    also have "... = add2 \<circ>\<^sub>c \<langle> successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,(eval_func \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult1) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>"
      by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod)
    also have "... = add2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, mult2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>"
      by (typecheck_cfuncs, simp add: comp_associative2 mult2_def)
    also have "... = successor \<circ>\<^sub>c (mult2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> ,id\<^sub>c \<nat>\<^sub>c\<rangle>)"
      by (typecheck_cfuncs, simp add: add2_commutes_succ add2_respects_zero_on_left)
    then show ?thesis
      by (simp add: calculation)
  qed

  
  have id3: "mult2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id\<^sub>c \<nat>\<^sub>c\<rangle> = id\<^sub>c \<nat>\<^sub>c"
    by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2 natural_number_object_func_unique square triangle)
  have "m = id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m"
    using assms by (simp add: id_left_unit2)
  also have "... = mult2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c m"
    using assms id3 comp_associative2 by (typecheck_cfuncs, auto)
  also have "... = mult2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c zero , m\<rangle>"
    by (typecheck_cfuncs, metis cfunc_type_def comp_associative mult_apply1right mult_def assms)
  then show ?thesis
    unfolding mult_def using calculation by auto
qed




lemma mult_Left_Distributivity:
  assumes a_type[type_rule]: "a \<in>\<^sub>c \<nat>\<^sub>c" and b_type[type_rule]: "b \<in>\<^sub>c \<nat>\<^sub>c" and c_type[type_rule]: "c \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(a +\<^sub>\<nat> b)\<cdot>\<^sub>\<nat> c = (a \<cdot>\<^sub>\<nat> c) +\<^sub>\<nat> (b \<cdot>\<^sub>\<nat> c)"
proof -
  have f1: "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c
    (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
    (mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c zero) = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c 
            (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(
            add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
             (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
            (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero)"
  proof(etcs_rule one_separator[ where X = "(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<one>", where Y = "\<nat>\<^sub>c"])
    show "\<And>x. x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<one> \<Longrightarrow> (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
          (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
          (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,
                  mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x"
    proof-
      fix x 
      assume x_type[type_rule]: "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<one>"
     
      obtain p q where p_type[type_rule]: "p \<in>\<^sub>c \<nat>\<^sub>c" and q_type[type_rule]: "q \<in>\<^sub>c \<nat>\<^sub>c" and x_def:  "x = \<langle>\<langle>p,q\<rangle>, id \<one>\<rangle>"
        using x_type by (typecheck_cfuncs, metis cart_prod_decomp one_unique_element)
     
       
      have "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
          (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, id \<one>\<rangle> =
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
          (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,
                  mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, id \<one>\<rangle>"
      proof-
        have "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
              (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, id \<one>\<rangle>   =     
             ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
              (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>  )\<circ>\<^sub>c  (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero)) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, id \<one>\<rangle>" 
          by (typecheck_cfuncs, metis inv_transpose_func_def3 inv_transpose_of_composition)
        also have "... =  (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
              (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>  )\<circ>\<^sub>c  (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, id \<one>\<rangle>" 
          by (typecheck_cfuncs, metis comp_associative2 x_def)
        also have "... =  (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
              (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>)\<circ>\<^sub>c   \<langle>id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>p,q\<rangle>,zero \<circ>\<^sub>c  id \<one>\<rangle>"
          using cfunc_cross_prod_comp_cfunc_prod by (typecheck_cfuncs, force)
        also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
              (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>)\<circ>\<^sub>c   \<langle>\<langle>p,q\<rangle>,zero\<rangle>"
          by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2)        
        also have "... = (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c   \<langle>\<langle>p,q\<rangle>,zero\<rangle>"
          by (typecheck_cfuncs, simp add: transpose_func_def)  
        also have "... = mult2 \<circ>\<^sub>c  \<langle>add2\<circ>\<^sub>c \<langle>p,q\<rangle>,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero\<rangle>"
          by (typecheck_cfuncs, smt (z3) cfunc_cross_prod_comp_cfunc_prod comp_associative2)
        also have "... = mult2 \<circ>\<^sub>c  \<langle>add2\<circ>\<^sub>c \<langle>p,q\<rangle>, zero\<rangle>"
          using id_left_unit2 zero_type by force
        also have "... = (add2\<circ>\<^sub>c \<langle>p,q\<rangle>) \<cdot>\<^sub>\<nat> zero"
          by (simp add: mult_def)
        also have "... = zero"
          using mult_respects_zero_right by (typecheck_cfuncs, blast)
        also have "... = zero +\<^sub>\<nat> zero"
          by (simp add: add_respects_zero_on_left zero_type)
        also have "... = add2 \<circ>\<^sub>c\<langle>zero, zero\<rangle>"
          by (simp add: add_def)
        also have "... = add2 \<circ>\<^sub>c\<langle>p \<cdot>\<^sub>\<nat> zero,q \<cdot>\<^sub>\<nat> zero\<rangle>"
          by (typecheck_cfuncs, simp add: mult_respects_zero_right x_def)
        also have "... = add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>p,  zero\<rangle>, mult2 \<circ>\<^sub>c \<langle>q,  zero\<rangle>\<rangle> "
          by (simp add: mult_def)
        also have "... = add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, zero\<rangle>, 
                 (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, zero\<rangle>\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
                (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, zero\<rangle>,(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, zero\<rangle>\<rangle>\<rangle> "
          by (typecheck_cfuncs, metis mult_def mult_respects_zero_right right_cart_proj_cfunc_prod)
        also have "... = add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
                 (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
                (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle> \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, zero\<rangle>"
          by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2)
        also have "... =
              add2 \<circ>\<^sub>c(\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
                 (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
                (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>  \<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c\<langle>p,q\<rangle>, zero \<circ>\<^sub>c id \<one>\<rangle>)"
          using id_left_unit2 id_right_unit2   by (typecheck_cfuncs, auto)
        also have "... =
              add2 \<circ>\<^sub>c(\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
                 (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
                (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle> \<circ>\<^sub>c  (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, id \<one>\<rangle>)"
          by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod)
        also have "... =
              add2 \<circ>\<^sub>c(\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
                 (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
                (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle> \<circ>\<^sub>c  (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero) \<circ>\<^sub>c x)"
          using x_def by force
        also have "... =
              (add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
                 (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
                (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle> \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero)) \<circ>\<^sub>c x"
          using cfunc_type_def comp_associative x_type by (typecheck_cfuncs, auto)
        also have "... =  ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c 
                (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(
                add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
                 (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c
                (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> )) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero) \<circ>\<^sub>c x"
          using cfunc_type_def comp_associative transpose_func_def x_type by (typecheck_cfuncs, smt (verit))
        also have "... =  (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
              (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,
                      mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, id \<one>\<rangle>"
          using  x_def  by (typecheck_cfuncs, smt comp_associative2 inv_transpose_func_def3 inv_transpose_of_composition)
        show "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, id \<one>\<rangle> = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>, mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, id \<one>\<rangle>"
          by (simp add: \<open>(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero) \<circ>\<^sub>c x = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,id\<^sub>c \<one>\<rangle>\<close> calculation)
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
    proof(etcs_rule natural_number_object_func_unique[where X ="\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>", where f = "(add2 \<circ>\<^sub>c (add2\<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)), eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>"])
      show "(mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero =
      (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,
                mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero"
        by(etcs_rule same_evals_equal[where Z = \<one>,where X= "\<nat>\<^sub>c", where A = "\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"], typecheck_cfuncs, smt f1)   
      show "(mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor =
         (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
      proof(etcs_rule same_evals_equal[where Z ="\<nat>\<^sub>c",where X= "\<nat>\<^sub>c", where A = "\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"])
        show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor = eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
        proof(etcs_rule one_separator[where X ="(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c\<nat>\<^sub>c", where Y= "\<nat>\<^sub>c"])
          show "\<And>x. x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c(mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c x"
          proof - 
            fix x 
            assume x_type[type_rule]: "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c"
            obtain p q r where p_type[type_rule]: "p\<in>\<^sub>c \<nat>\<^sub>c" and q_type[type_rule]: "q \<in>\<^sub>c \<nat>\<^sub>c" and r_type[type_rule]: "r \<in>\<^sub>c \<nat>\<^sub>c" and x_def: "x = \<langle>\<langle>p,q\<rangle>,r\<rangle>"
              using cart_prod_decomp x_type by blast
           
  
            have fact5: "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
            ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c successor)) \<circ>\<^sub>c   \<langle>\<langle>p,q\<rangle>,r\<rangle>"
              using x_def by blast
            also have "... = ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c  (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f     successor) )\<circ>\<^sub>c   \<langle>\<langle>p,q\<rangle>,r\<rangle>"
              by (typecheck_cfuncs, metis identity_distributes_across_composition)
            also have "... = ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>) )\<circ>\<^sub>c   \<langle>\<langle>p,q\<rangle>,successor \<circ>\<^sub>c r\<rangle>"
              by (typecheck_cfuncs, smt (z3) cfunc_cross_prod_comp_cfunc_prod comp_associative2 id_left_unit2)
            also have "... = mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c   \<langle>\<langle>p,q\<rangle>,successor \<circ>\<^sub>c r\<rangle>"
              by (typecheck_cfuncs, simp add: comp_associative2 transpose_func_def)
            also have "... = mult2 \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>p,q\<rangle>, id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor \<circ>\<^sub>c r\<rangle>"
              using cfunc_cross_prod_comp_cfunc_prod by (typecheck_cfuncs, auto)
            also have "... =  (p +\<^sub>\<nat> q) \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c r)"
              by (typecheck_cfuncs, simp add: add_def id_left_unit2 mult_def)
            also have "... = (p +\<^sub>\<nat> q)  +\<^sub>\<nat>  ((p +\<^sub>\<nat> q) \<cdot>\<^sub>\<nat> r)"
              by (typecheck_cfuncs, simp add:  mult_respects_succ_right x_def)
            also have "... =  add2 \<circ>\<^sub>c \<langle> add2 \<circ>\<^sub>c  \<langle>p,q\<rangle>, mult2 \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c  \<langle>p,q\<rangle>, id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c r\<rangle>\<rangle>"
              using add_def id_left_unit2 mult_def x_def by (typecheck_cfuncs, auto)
            also have "... = add2 \<circ>\<^sub>c \<langle> add2 \<circ>\<^sub>c  \<langle>p,q\<rangle>,  mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle>\<rangle>"
              by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod x_def)
            also have "... = add2 \<circ>\<^sub>c \<langle> add2 \<circ>\<^sub>c  \<langle>p,q\<rangle>, (mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle>\<rangle>"
              by (typecheck_cfuncs, metis comp_associative2 x_def)
            also have "... = add2 \<circ>\<^sub>c \<langle> add2 \<circ>\<^sub>c  \<langle>p,q\<rangle>, ((id\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle>\<rangle>"
              by (typecheck_cfuncs, simp add: id_left_unit2)
            also have "... =  add2 \<circ>\<^sub>c \<langle> add2 \<circ>\<^sub>c  \<langle>p,q\<rangle>, (id\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle>\<rangle>"
              by (typecheck_cfuncs, metis id_left_unit2 x_def)
            also have "... = add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f (id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c  \<langle>\<langle>p,q\<rangle>, (mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle>\<rangle>"
              by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod x_def)
            also have "... = add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f (id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle>\<rangle>"
              by (typecheck_cfuncs, smt comp_associative2 flat_cancels_sharp inv_transpose_func_def3 x_def x_type)
            also have "... = add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f (id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,  eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>p,q\<rangle>, (mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c r\<rangle>\<rangle>"
              by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod x_def)
            also have "... = add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f (id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,  eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, (mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c r\<rangle>\<rangle>"
              using id_left_unit2  by (typecheck_cfuncs, auto)
            also have "... = add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f (id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c  \<langle>(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>))\<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, 
                                     (mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c r\<rangle>,  eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, (mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c r\<rangle>\<rangle>"
              by (typecheck_cfuncs, metis left_cart_proj_cfunc_prod)          
            also have "... = add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f (id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)), 
                                      eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<rangle>  \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, (mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c r\<rangle>"
              using cfunc_prod_comp  by (typecheck_cfuncs, force)
            also have "... = (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f (id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)), 
                                     eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)  \<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c  \<langle>p,q\<rangle>, (mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c r\<rangle>"
              using cfunc_type_def comp_associative id_left_unit2  by (typecheck_cfuncs, smt)
            also have "... =  ( (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f (id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)), 
                                      eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>))\<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c  \<langle>p,q\<rangle>, (mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c r\<rangle>"
              by (typecheck_cfuncs, simp add: transpose_func_def)        
            also have "... = ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f (id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)), 
                               eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>)\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>f (mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle>"
              by (typecheck_cfuncs , smt cfunc_cross_prod_comp_cfunc_prod cfunc_type_def comp_associative  x_def x_type)
            also have "... = ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c  (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f (id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)), 
                               eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle>"
              using   identity_distributes_across_composition by (typecheck_cfuncs, auto)
            also have "... = ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c  (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)), 
                               eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>) ) \<circ>\<^sub>c x"
              using x_def by blast
       show "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c(mult2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c x"
         using calculation x_def by blast
       qed
     qed
    qed

  show "(add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor = 
        (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>"
  proof(etcs_rule same_evals_equal[where Z = "\<nat>\<^sub>c", where X = "\<nat>\<^sub>c", where A = "\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c"])
    show  "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>, mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor = eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>"
    proof(etcs_rule one_separator[where X = "(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c", where Y = "\<nat>\<^sub>c"])
      show "\<And>x. x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>, mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c x"
      proof - 
        fix x 
        assume x_typ: "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c"
        obtain p q r where p_type[type_rule] :"p \<in>\<^sub>c \<nat>\<^sub>c" and q_type[type_rule]: "q \<in>\<^sub>c \<nat>\<^sub>c" and r_type[type_rule]: "r \<in>\<^sub>c \<nat>\<^sub>c" and x_def: "x= \<langle>\<langle>p,q\<rangle>,r\<rangle>"
          using x_typ cart_prod_decomp by blast     
        
        have "((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)  \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>),  (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<rangle>)\<^sup>\<sharp>  \<circ>\<^sub>c (add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>))\<circ>\<^sub>c x =  ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c  (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)  \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>),  (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<rangle>)\<^sup>\<sharp>  \<circ>\<^sub>c (add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle>"
          using x_def by blast
        also have "... =  ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)  \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>), (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<rangle>)\<^sup>\<sharp>  ) \<circ>\<^sub>c   (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),  (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),      (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle> "
          using  identity_distributes_across_composition  by (typecheck_cfuncs, auto)
        also have "... = ((add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>), (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<rangle>) \<circ>\<^sub>c   (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),  (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle> "
          using assms by (typecheck_cfuncs, simp add: comp_associative2 transpose_func_def)    
        also have "... =  (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>),  (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<rangle>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),  (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c(left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle>"
            by (typecheck_cfuncs , smt comp_associative2)
        also have "... = (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>), (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<rangle>)  \<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>p,q\<rangle>, (add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),  (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c  r\<rangle>"
          using cfunc_cross_prod_comp_cfunc_prod by (typecheck_cfuncs, force)
        also have "... =  (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>), (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<rangle>)  \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, (add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),  (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),  (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c  r\<rangle> "
          using  id_left_unit2 by (typecheck_cfuncs, auto)
        also have "... =  add2 \<circ>\<^sub>c ((add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>), (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<rangle> ) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, (add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),  (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c r\<rangle> "
          by (typecheck_cfuncs, smt comp_associative2)
        also have "... = add2 \<circ>\<^sub>c \<langle> add2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>),  id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)) \<rangle>  \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, (add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),  (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c  r\<rangle> "
          by (smt add2_type cfunc_cross_prod_comp_cfunc_prod eval_func_type id_type left_cart_proj_type)
        also have "... = add2 \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>),  (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)) \<rangle> \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, (add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c  (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c  r\<rangle> "
          by (metis eval_func_type id_left_unit2)
        also have "... =   add2 \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>) \<circ>\<^sub>c \<langle> \<langle>p,q\<rangle>, (add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),    (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c r\<rangle> , (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))  \<circ>\<^sub>c \<langle> \<langle>p,q\<rangle>, (add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),  (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c r\<rangle> \<rangle>"
          by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2)          
        also have "... =add2 \<circ>\<^sub>c \<langle> add2 \<circ>\<^sub>c \<langle>p,q\<rangle>  ,  (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))   \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>, (add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c  \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c                  (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),      (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c      r\<rangle>       \<rangle>" 
          by (typecheck_cfuncs, metis left_cart_proj_cfunc_prod)
        also have "... = add2 \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>p,q\<rangle>,  (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>p,q\<rangle>,(add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),  (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c  \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),  (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c r\<rangle> \<rangle>"
          using id_left_unit2 by (typecheck_cfuncs, auto)
        also have "... = add2 \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>p,q\<rangle>,  (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))  \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle> \<langle>p,q\<rangle>,r\<rangle> \<rangle>"
          by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
        also have "... = add2 \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>p,q\<rangle> ,(add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c  \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>) \<circ>\<^sub>c \<langle> \<langle>p,q\<rangle>,r\<rangle> \<rangle>"
          by (typecheck_cfuncs , smt comp_associative2 transpose_func_def)       
        also have "... = add2 \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>p,q\<rangle>, add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle> , mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle> \<circ>\<^sub>c \<langle> \<langle>p,q\<rangle>,r\<rangle> \<rangle>"
          by (typecheck_cfuncs , smt comp_associative2)
        also have "... = add2 \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>p,q\<rangle>, add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c \<langle> \<langle>p,q\<rangle>,r\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>   \<circ>\<^sub>c \<langle> \<langle>p,q\<rangle>,r\<rangle> \<rangle>  \<rangle>"
          by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2)
        also have "... =add2 \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>p,q\<rangle>, add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c \<langle> \<langle>p,q\<rangle>,r\<rangle>     , mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c  (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle> \<langle>p,q\<rangle>,r\<rangle> ,(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle> \<langle>p,q\<rangle>,r\<rangle>\<rangle>   \<rangle>  \<rangle>"
          by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2)
        also have "... = add2 \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>p,q\<rangle>,  add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle> \<langle>p,q\<rangle>,r\<rangle>, (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle> \<langle>p,q\<rangle>,r\<rangle>\<rangle> , mult2 \<circ>\<^sub>c  \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>p,q\<rangle>, r\<rangle>   \<rangle>  \<rangle>"
          by (typecheck_cfuncs, smt cart_prod_eq comp_associative2 left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
        also have "... = add2 \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>p,q\<rangle>,  add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c   \<langle>p,q\<rangle>, r\<rangle>, mult2 \<circ>\<^sub>c\<langle>q,r\<rangle>\<rangle>\<rangle>"
          using   left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod by (typecheck_cfuncs, auto)
        also have "... = add2 \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>p,q\<rangle>,  add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>p, r\<rangle>, mult2 \<circ>\<^sub>c\<langle>q,r\<rangle>\<rangle>\<rangle>"
          using  left_cart_proj_cfunc_prod by (typecheck_cfuncs, auto)
        also have "... = (p +\<^sub>\<nat> q) +\<^sub>\<nat> (p \<cdot>\<^sub>\<nat> r +\<^sub>\<nat> q \<cdot>\<^sub>\<nat> r)"
          by (simp add: add_def mult_def)
        also have "... = p +\<^sub>\<nat> (q +\<^sub>\<nat> (p \<cdot>\<^sub>\<nat> r +\<^sub>\<nat> q \<cdot>\<^sub>\<nat> r))"
          by (typecheck_cfuncs, metis add_associates)
        also have "... = p +\<^sub>\<nat> ((q +\<^sub>\<nat> p \<cdot>\<^sub>\<nat> r) +\<^sub>\<nat> q \<cdot>\<^sub>\<nat> r)"
          by (typecheck_cfuncs, simp add: add_associates mult_closure)
        also have "... = p +\<^sub>\<nat> ((p \<cdot>\<^sub>\<nat> r  +\<^sub>\<nat> q) +\<^sub>\<nat> q \<cdot>\<^sub>\<nat> r)"
          using add_commutes by (typecheck_cfuncs, auto)
        also have "... = p +\<^sub>\<nat> (p \<cdot>\<^sub>\<nat> r  +\<^sub>\<nat> (q +\<^sub>\<nat> q \<cdot>\<^sub>\<nat> r))"
          by (typecheck_cfuncs, simp add: add_associates)
        also have "... = (p +\<^sub>\<nat> p \<cdot>\<^sub>\<nat> r)  +\<^sub>\<nat> (q +\<^sub>\<nat> q \<cdot>\<^sub>\<nat> r)"
          by (typecheck_cfuncs, meson add_associates)
        also have "... = (p \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c r)) +\<^sub>\<nat> (q \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c r))"
          by (typecheck_cfuncs, simp add:  mult_respects_succ_right)
        also have "... = add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>p , (successor \<circ>\<^sub>c r) \<rangle>  , mult2 \<circ>\<^sub>c \<langle>q,successor \<circ>\<^sub>c r  \<rangle> \<rangle> "
          by (simp add: add_def mult_def)
        also have "... = add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c  \<langle>p,q\<rangle> , (successor \<circ>\<^sub>c r) \<rangle>  , mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c  \<langle>p,q\<rangle> , successor \<circ>\<^sub>c r \<rangle>\<rangle> "
          using left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod  by (typecheck_cfuncs, force)
        also have "... = add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,successor \<circ>\<^sub>c r\<rangle> , (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,successor \<circ>\<^sub>c r\<rangle> \<rangle>  , mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,successor \<circ>\<^sub>c r\<rangle> ,(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,successor \<circ>\<^sub>c r\<rangle> \<rangle>   \<rangle> "
          using left_cart_proj_cfunc_prod  right_cart_proj_cfunc_prod succ_n_type  by (typecheck_cfuncs, auto)
        also have "... = add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,successor \<circ>\<^sub>c r\<rangle>  , mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,successor \<circ>\<^sub>c r\<rangle>   \<rangle> "
          by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2)
        also have "... = add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c  (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle> \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,successor \<circ>\<^sub>c r\<rangle>"
          by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2)
        also have  "... = (add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,successor \<circ>\<^sub>c r\<rangle>"
          using  comp_associative2  by (typecheck_cfuncs, blast)
        also have "... = ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> )) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,successor \<circ>\<^sub>c r\<rangle>"
          by (typecheck_cfuncs, metis transpose_func_def)
        also have "... = ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> )) \<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>p,q\<rangle>,successor \<circ>\<^sub>c r\<rangle>"
          by (typecheck_cfuncs, smt (z3) cfunc_type_def id_left_unit)
        also have "... = ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> )) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor) \<circ>\<^sub>c  \<langle> \<langle>p,q\<rangle>, r\<rangle>"
          using cfunc_cross_prod_comp_cfunc_prod by (typecheck_cfuncs, force)
        also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c  \<langle> \<langle>p,q\<rangle>, r\<rangle>"
          by (typecheck_cfuncs, smt comp_associative2 inv_transpose_func_def3 inv_transpose_of_composition)
        also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c  x"
          using x_def by blast
        then show "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>,mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c x"
          by (simp add: calculation)
        qed
      qed
    qed
  qed

  then have flat_main_result: "mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) = add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c  (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>"
    by (typecheck_cfuncs, metis flat_cancels_sharp main_result)
  then have main_equation: "(a +\<^sub>\<nat> b)\<cdot>\<^sub>\<nat> c = mult2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
    using assms by (typecheck_cfuncs, simp add: add_def cfunc_cross_prod_comp_cfunc_prod id_left_unit2 mult_def)
  also have "... = add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>, mult2 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c    (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),(right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle> \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
    using cfunc_type_def comp_associative flat_main_result assms  by (typecheck_cfuncs, force)
  also have "... =  (a \<cdot>\<^sub>\<nat> c) +\<^sub>\<nat> (b \<cdot>\<^sub>\<nat> c)"
    unfolding mult_def add_def using assms by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2 left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  then show ?thesis
    by (simp add: calculation) 
qed





lemma mult_commutative:
  assumes a_type[type_rule]: "a \<in>\<^sub>c \<nat>\<^sub>c" and b_type[type_rule]: "b \<in>\<^sub>c \<nat>\<^sub>c"
  shows "a \<cdot>\<^sub>\<nat> b = b \<cdot>\<^sub>\<nat> a"

proof - 
  have main_result: "(mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> = (mult2)\<^sup>\<sharp>"
  proof(etcs_rule natural_number_object_func_unique[where X = "\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>", where f = "(add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>), eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>"])  
    show triangle: "(mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero = mult2\<^sup>\<sharp> \<circ>\<^sub>c zero"
    proof(etcs_rule same_evals_equal[where Z = "\<one>", where X = "\<nat>\<^sub>c", where A = "\<nat>\<^sub>c"])
      show equation1: "eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero =
                      eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2\<^sup>\<sharp> \<circ>\<^sub>c zero"
      proof(etcs_rule one_separator[where X = "\<nat>\<^sub>c\<times>\<^sub>c \<one>", where Y = "\<nat>\<^sub>c"])
        show "\<And>x. x \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<one> \<Longrightarrow>
         (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c  zero) \<circ>\<^sub>c x = 
         (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x"
        proof - 
          fix x 
          assume x_type[type_rule]: "x \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<one>"
          obtain p where p_type[type_rule]: "p \<in>\<^sub>c \<nat>\<^sub>c" and x_def:  "x = \<langle>p, id \<one>\<rangle>"
            by (typecheck_cfuncs, metis cart_prod_decomp one_unique_element)
          have "(eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x =
                (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c \<langle>p, id \<one>\<rangle>"
            using x_def by blast
          also have "... =  eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c \<langle>p,id\<^sub>c \<one>\<rangle>"
            by (typecheck_cfuncs, metis comp_associative2 x_def)
          also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero)\<circ>\<^sub>c \<langle>p,id\<^sub>c \<one>\<rangle>"
            by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2)
          also have "... = (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero)\<circ>\<^sub>c \<langle>p,id\<^sub>c \<one>\<rangle>"
            by (typecheck_cfuncs, metis cfunc_type_def comp_associative transpose_func_def)
          also have "... = (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c p, zero \<circ>\<^sub>c id\<^sub>c \<one>\<rangle>"
            by (typecheck_cfuncs, smt  cfunc_cross_prod_comp_cfunc_prod)
          also have "... =  mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>p, zero\<rangle>"
            by (typecheck_cfuncs, metis (full_types) comp_associative2 id_left_unit2 id_right_unit2)
          also have "... =  mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>p, zero\<rangle>, left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>p, zero\<rangle>\<rangle>"
            by (typecheck_cfuncs , metis cfunc_prod_comp)
          also have "... =  mult2 \<circ>\<^sub>c \<langle>zero, p\<rangle>"
            by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
          also have "... = zero"
            using x_def mult_def mult_respects_zero_left by (typecheck_cfuncs, force)
          also have "... = p \<cdot>\<^sub>\<nat> zero"
            by (typecheck_cfuncs, simp add: mult_respects_zero_right)
          also have "... = mult2 \<circ>\<^sub>c  \<langle>p,zero\<rangle>"
            by (simp add: mult_def)
          also have "... = mult2 \<circ>\<^sub>c  \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c p,zero \<circ>\<^sub>cid \<one>\<rangle>"
            by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2)
          also have "... = (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2\<^sup>\<sharp>)  \<circ>\<^sub>c  \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c p,zero \<circ>\<^sub>cid \<one>\<rangle>"
            using transpose_func_def by (typecheck_cfuncs, auto)
          also have "... = (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2\<^sup>\<sharp>)  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero) \<circ>\<^sub>c \<langle>p, id \<one>\<rangle>"
            using cfunc_cross_prod_comp_cfunc_prod  by (typecheck_cfuncs, auto)
          also have "... = (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c \<langle>p, id \<one>\<rangle>"
            by (typecheck_cfuncs, smt cfunc_type_def comp_associative inv_transpose_func_def3 inv_transpose_of_composition)
          then show "(eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x = (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x"
            by (metis calculation x_def)
        qed
      qed
    qed
    show square1: "(mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
    successor = (add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
    (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>"
    proof(etcs_rule same_evals_equal[where Z = "\<nat>\<^sub>c", where X = "\<nat>\<^sub>c", where A = "\<nat>\<^sub>c"])
      show eqn2: "eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor =
                  eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>"
      proof(etcs_rule one_separator[where X ="\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c ", where Y = "\<nat>\<^sub>c"])
        show "\<And>x. x \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
         (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c x"
        proof - 
          fix x 
          assume x_type[type_rule]: "x \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
          obtain p q where p_type[type_rule]: "p \<in>\<^sub>c \<nat>\<^sub>c" and q_type[type_rule]: "q \<in>\<^sub>c \<nat>\<^sub>c" and x_def: "x = \<langle>p,q\<rangle>"
            using cart_prod_decomp x_type by blast
         

          have "(eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
                ((eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor)) \<circ>\<^sub>c x"
            by (typecheck_cfuncs , simp add: sharp_comp transpose_func_def)
          also have "... =  (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c \<langle>p,q\<rangle>"
            by (typecheck_cfuncs, metis  comp_associative2 x_def)
          also have "... =  (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>)  \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c p,successor \<circ>\<^sub>cq\<rangle>"
            using cfunc_cross_prod_comp_cfunc_prod  by (typecheck_cfuncs, auto)
          also have "... =  (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>)  \<circ>\<^sub>c \<langle>p,successor \<circ>\<^sub>cq\<rangle>"
            using id_left_unit2  by (typecheck_cfuncs, force)
          also have "... =  (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)  \<circ>\<^sub>c \<langle>p,successor \<circ>\<^sub>cq\<rangle>"
            by (typecheck_cfuncs, simp add: transpose_func_def)
          also have "... =  mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>  \<circ>\<^sub>c \<langle>p,successor \<circ>\<^sub>cq\<rangle>"
            using comp_associative2  by (typecheck_cfuncs, auto)
          also have "... =  mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>p,successor \<circ>\<^sub>cq\<rangle> ,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>p,successor \<circ>\<^sub>cq\<rangle>\<rangle>"
            using cfunc_prod_comp  by (typecheck_cfuncs, auto)
          also have "... =  mult2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c q ,p\<rangle>"
            using left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod   by (typecheck_cfuncs, auto)
          also have "... = (successor \<circ>\<^sub>c q) \<cdot>\<^sub>\<nat> p"
            by (simp add: mult_def)
          also have "... = p +\<^sub>\<nat> (q \<cdot>\<^sub>\<nat> p)"
            by (typecheck_cfuncs, metis succ_n_type mult_Left_Distributivity mult_respects_succ_right s0_is_left_id zero_type)
          also have "... =  add2 \<circ>\<^sub>c\<langle>p,  mult2 \<circ>\<^sub>c \<langle>q,p\<rangle>\<rangle>"
            by (simp add: add_def mult_def)
          also have "... =  add2 \<circ>\<^sub>c\<langle>p,  mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>p,q\<rangle>,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>p,q\<rangle>\<rangle>\<rangle>"
            by (typecheck_cfuncs, metis left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
          also have "... =  add2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>p,q\<rangle>,  mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>p,q\<rangle> \<rangle>  "
            by (typecheck_cfuncs , smt cfunc_prod_comp id_left_unit2 left_cart_proj_cfunc_prod)
          also have "... = add2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c , mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>  \<circ>\<^sub>c \<langle>p,q\<rangle>"
            by (typecheck_cfuncs , smt cfunc_prod_comp comp_associative2)             
          also have "... = (add2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c ,  mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)  \<circ>\<^sub>c x"  
            using comp_associative2 x_def by (typecheck_cfuncs, blast)
          also have "... = (add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>)\<rangle>) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_cross_prod transpose_func_def)
          also have "... = (add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>)) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, simp add: cfunc_prod_comp)
          also have "... = (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>)) \<circ>\<^sub>c x"
            using cfunc_type_def comp_associative transpose_func_def by (typecheck_cfuncs, smt)
          also have "... = (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c x"
            by (typecheck_cfuncs,  simp add: identity_distributes_across_composition)
          then show "(eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c x"
            by (simp add: calculation)
        qed
      qed
    qed
    show "mult2\<^sup>\<sharp> \<circ>\<^sub>c successor = (add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c mult2\<^sup>\<sharp>"
    proof(etcs_rule same_evals_equal[where Z = "\<nat>\<^sub>c", where X = "\<nat>\<^sub>c", where A = "\<nat>\<^sub>c"])
      show "eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2\<^sup>\<sharp> \<circ>\<^sub>c successor =  eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c mult2\<^sup>\<sharp>"
      proof(etcs_rule one_separator[where X ="\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c ", where Y = "\<nat>\<^sub>c"])
        show eqn4: "\<And>x. x \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
         (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c mult2\<^sup>\<sharp>) \<circ>\<^sub>c x"
        proof - 
          fix x 
          assume x_type[type_rule]: "x \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
          obtain p q where p_type[type_rule]: "p \<in>\<^sub>c \<nat>\<^sub>c" and q_type[type_rule]: "q \<in>\<^sub>c \<nat>\<^sub>c" and x_def: "x = \<langle>p,q\<rangle>"
            using cart_prod_decomp x_type by blast
          

          have "(eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
                ((eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor)) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, metis inv_transpose_func_def3 inv_transpose_of_composition)
          also have "... = (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c x"
            using comp_associative2  by (typecheck_cfuncs, auto)
          also have "... = mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c \<langle>p,q\<rangle>"
            by (typecheck_cfuncs , simp add: transpose_func_def x_def)
          also have "... = mult2 \<circ>\<^sub>c  \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c p,successor \<circ>\<^sub>c q\<rangle>"
            using cfunc_cross_prod_comp_cfunc_prod  by (typecheck_cfuncs, auto)
          also have "... = mult2 \<circ>\<^sub>c  \<langle>p,successor \<circ>\<^sub>c q\<rangle>"
            using id_left_unit2 by (typecheck_cfuncs, presburger)
          also have "... = p \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c q)"
            by (simp add: mult_def)
          also have "... = p +\<^sub>\<nat> (p \<cdot>\<^sub>\<nat>  q)"
            by (typecheck_cfuncs, simp add: mult_respects_succ_right)
          also have "... = add2 \<circ>\<^sub>c \<langle>p ,(p\<cdot>\<^sub>\<nat>q)\<rangle>"
            by (simp add: add_def)
          also have "... = add2 \<circ>\<^sub>c \<langle>p , mult2 \<circ>\<^sub>c\<langle>p,q\<rangle>\<rangle>"
            by (simp add: mult_def)
          also have "... = add2 \<circ>\<^sub>c \<langle>p ,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2\<^sup>\<sharp>)  \<circ>\<^sub>c \<langle>p,   q\<rangle>\<rangle>"
            by (typecheck_cfuncs , smt comp_associative2 transpose_func_def x_def)
          also have "... = add2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c p ,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2\<^sup>\<sharp>)  \<circ>\<^sub>c \<langle>p,   q\<rangle>\<rangle>"
            using id_left_unit2  by (typecheck_cfuncs, force)
          also have "... = add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c p, mult2\<^sup>\<sharp> \<circ>\<^sub>c  q\<rangle> ,eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c p, mult2\<^sup>\<sharp> \<circ>\<^sub>c  q\<rangle>\<rangle>"
            by (typecheck_cfuncs , smt cfunc_cross_prod_comp_cfunc_prod left_cart_proj_cfunc_prod)
          also have "... = add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>  \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c p, mult2\<^sup>\<sharp> \<circ>\<^sub>c  q\<rangle>"
            using cfunc_prod_comp by (typecheck_cfuncs, auto)           
          also have "... = add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>fmult2\<^sup>\<sharp>) \<circ>\<^sub>c x"
            using cfunc_cross_prod_comp_cfunc_prod x_def  by (typecheck_cfuncs, auto)
          also have "... = (add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>),eval_func \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c ((id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>fmult2\<^sup>\<sharp>) \<circ>\<^sub>c x)"
            by (typecheck_cfuncs, metis cfunc_type_def comp_associative)
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
    by (typecheck_cfuncs, metis  transpose_func_def)
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
  assumes a_type[type_rule]: "a \<in>\<^sub>c \<nat>\<^sub>c" and b_type[type_rule]: "b \<in>\<^sub>c \<nat>\<^sub>c" and c_type[type_rule]: "c \<in>\<^sub>c \<nat>\<^sub>c"
  shows "a \<cdot>\<^sub>\<nat> (b \<cdot>\<^sub>\<nat> c) = (a \<cdot>\<^sub>\<nat> b) \<cdot>\<^sub>\<nat> c"
proof -  
  have main_result: "(mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> = 
                     (mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp>"
    proof(etcs_rule natural_number_object_func_unique[where X = "\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<^esup>", where f = "(add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>"])
      show "(mult2 \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero =
    (mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero"
      proof(etcs_rule same_evals_equal[where Z = \<one>, where X = "\<nat>\<^sub>c", where A = "(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"])
        show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero =
              eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero"
        proof(etcs_rule one_separator[where X = "(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<one>", where Y = "\<nat>\<^sub>c"])
          show "\<And>x. x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<one> \<Longrightarrow>
           (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c  id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x"
          proof - 
            fix x 
            assume x_type[type_rule]: "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<one>"
            obtain y where y_type[type_rule]: "y \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c" and x_def: "x = \<langle>y, id \<one>\<rangle>"
              by (typecheck_cfuncs, metis cart_prod_decomp one_unique_element)
            obtain p q where p_type[type_rule]: "p \<in>\<^sub>c \<nat>\<^sub>c" and q_type[type_rule]: "q \<in>\<^sub>c \<nat>\<^sub>c" and y_def: "y = \<langle>p,q\<rangle>"
              by (typecheck_cfuncs, metis cart_prod_decomp)            

            have "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x = 
                (((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>)) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f  zero)) \<circ>\<^sub>c x"
              by (typecheck_cfuncs, metis inv_transpose_func_def3 inv_transpose_of_composition)
            also have "... = ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c  id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>)) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f  zero) \<circ>\<^sub>c x"
              using comp_associative2 x_type by (typecheck_cfuncs, auto)
            also have "... = (mult2 \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c ((id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f  zero) \<circ>\<^sub>c x)"
              using  transpose_func_def by (typecheck_cfuncs, auto)
            also have "... = (mult2 \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c  \<langle>id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>p,q\<rangle>,zero \<circ>\<^sub>c id \<one>\<rangle>"
              by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod x_def y_def)
            also have "... = (mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c  \<langle>\<langle>p,q\<rangle>,zero\<rangle>"
              by (typecheck_cfuncs, metis id_left_unit2 id_right_unit2 y_def)
            also have "... = mult2 \<circ>\<^sub>c ((mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c  \<langle>\<langle>p,q\<rangle>,zero\<rangle>)"
              using comp_associative2  by (typecheck_cfuncs, auto)
            also have "... = mult2 \<circ>\<^sub>c   \<langle>mult2\<circ>\<^sub>c \<langle>p,q\<rangle>,id\<^sub>c \<nat>\<^sub>c\<circ>\<^sub>c zero\<rangle>"
              using cfunc_cross_prod_comp_cfunc_prod y_type by (typecheck_cfuncs, auto)
            also have "... = (mult2\<circ>\<^sub>c \<langle>p,q\<rangle>) \<cdot>\<^sub>\<nat> zero"
              using id_left_unit2 mult_def zero_type by auto
            also have "... = zero"
              using comp_type mult2_type mult_respects_zero_right  by (typecheck_cfuncs, blast)
            also have "... = mult2 \<circ>\<^sub>c  \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c p ,mult2 \<circ>\<^sub>c \<langle>q,zero\<rangle>\<rangle>"
              using mult_def mult_respects_zero_right y_def by (typecheck_cfuncs, presburger)
            also have "... = mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>p , \<langle>q,zero\<rangle>  \<rangle>"
              by (typecheck_cfuncs , smt cfunc_cross_prod_comp_cfunc_prod y_def)
            also have "... = mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c  \<langle>p,q\<rangle>, \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c  \<langle>p,q\<rangle>  ,zero \<rangle> \<rangle>"
              by (typecheck_cfuncs, metis left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod y_def)
            also have "... = mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,zero\<rangle>,
                                \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,zero\<rangle>  , (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,zero\<rangle>  \<rangle>  \<rangle>"
              using left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod  by (typecheck_cfuncs, auto)
            also have "... = mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,zero\<rangle>,
                                \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,zero\<rangle>  \<rangle>"
              using cfunc_prod_comp comp_associative2  by (typecheck_cfuncs, auto)  
            also have "... = mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
                                \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>\<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,zero\<rangle>"
              using cfunc_prod_comp comp_associative2  by (typecheck_cfuncs, auto)
            also have "... = mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
                                \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>\<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>p,q\<rangle>,zero \<circ>\<^sub>cid\<^sub>c \<one>\<rangle>"
              using id_left_unit2 id_right_unit2 by (typecheck_cfuncs, auto)
            also have "... = (mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
                                \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f zero)  \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,id\<^sub>c \<one>\<rangle>"
              by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod comp_associative2)       
            also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),    \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> )) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f zero)  \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,id\<^sub>c \<one>\<rangle>"
              by (typecheck_cfuncs , smt cfunc_type_def comp_associative transpose_func_def y_type)        
            also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero)) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,id\<^sub>c \<one>\<rangle>"
              by (typecheck_cfuncs, smt comp_associative2 inv_transpose_func_def3 inv_transpose_of_composition transpose_func_def)        
            also have "... = ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero))) \<circ>\<^sub>c x"
              using comp_associative2 x_def y_def by (typecheck_cfuncs, blast)
            then show "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c x"
             by (simp add: calculation)
         qed
       qed
     qed
     show "(mult2 \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor = (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
     proof(etcs_rule same_evals_equal[where Z = "\<nat>\<^sub>c", where X = "\<nat>\<^sub>c", where A = "(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)"])
       show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor = eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
       proof(etcs_rule one_separator[where X ="(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c", where Y = "\<nat>\<^sub>c"])
         show "\<And>x. x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(mult2 \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c x"
         proof - 
           fix x 
           assume x_type[type_rule]: "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c"
           obtain y r where y_type[type_rule]: "y \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)" and r_type[type_rule]:  "r \<in>\<^sub>c \<nat>\<^sub>c" and x_def: "x = \<langle>y,r\<rangle>"
             using cart_prod_decomp  by (typecheck_cfuncs, blast)
           obtain p q where p_type[type_rule]: "p  \<in>\<^sub>c \<nat>\<^sub>c" and q_type[type_rule]: "q \<in>\<^sub>c \<nat>\<^sub>c" and y_def: "y = \<langle>p,q\<rangle>"
             using cart_prod_decomp  by (typecheck_cfuncs, blast)

           have "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f  (mult2 \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x = 
                ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor)) \<circ>\<^sub>c x"
             by (typecheck_cfuncs, metis inv_transpose_func_def3 inv_transpose_of_composition)
           also have "... = ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor) \<circ>\<^sub>c x)"
             using comp_associative2  by (typecheck_cfuncs, auto)
           also have "... = (mult2 \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c ((id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor) \<circ>\<^sub>c x)"
             by (typecheck_cfuncs, simp add: transpose_func_def)
           also have "... = (mult2 \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c  \<langle>id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c y,successor \<circ>\<^sub>c r\<rangle>"
             using cfunc_cross_prod_comp_cfunc_prod x_def by (typecheck_cfuncs, auto)
           also have "... = (mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c  \<langle>y,successor \<circ>\<^sub>c r\<rangle>"
             using id_left_unit2 by (typecheck_cfuncs, presburger)
           also have "... = mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c  \<langle>y,successor \<circ>\<^sub>c r\<rangle>"
             using comp_associative2  by (typecheck_cfuncs, auto)
           also have "... = mult2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c y,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (successor \<circ>\<^sub>c r)\<rangle>"
             by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod)
           also have "... = mult2 \<circ>\<^sub>c \<langle>p \<cdot>\<^sub>\<nat> q, successor \<circ>\<^sub>c r\<rangle>"
             using id_left_unit2 mult_def y_def by (typecheck_cfuncs, presburger)
           also have "... = (p \<cdot>\<^sub>\<nat> q) \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c r)"
             by (simp add: mult_def)
           also have "... = (p \<cdot>\<^sub>\<nat> q) +\<^sub>\<nat> ((p \<cdot>\<^sub>\<nat> q)\<cdot>\<^sub>\<nat> r)"
             by (typecheck_cfuncs, simp add: mult_closure mult_respects_succ_right x_def y_def)
           also have "... = add2 \<circ>\<^sub>c\<langle>p \<cdot>\<^sub>\<nat> q,(p \<cdot>\<^sub>\<nat> q)\<cdot>\<^sub>\<nat> r\<rangle>"
             by (simp add: add_def)
           also have "... = add2 \<circ>\<^sub>c\<langle>mult2\<circ>\<^sub>c \<langle>p,q\<rangle>,mult2\<circ>\<^sub>c \<langle>(p \<cdot>\<^sub>\<nat> q),r\<rangle>\<rangle>"
             using mult_def by fastforce
           also have "... = add2 \<circ>\<^sub>c\<langle>mult2\<circ>\<^sub>c \<langle>p,q\<rangle>,mult2\<circ>\<^sub>c \<langle>mult2\<circ>\<^sub>c \<langle>p,q\<rangle>, id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c r\<rangle>\<rangle>"
             using id_left_unit2 mult_def by (typecheck_cfuncs, presburger)
           also have "... =  add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c  \<langle>p,q\<rangle> ,(mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c\<langle>\<langle>p,q\<rangle>,r\<rangle>\<rangle>"
             by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod comp_associative2 x_def x_type y_def)
           also have "... = add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c\<langle>\<langle>p,q\<rangle>,r\<rangle> ,eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>))\<circ>\<^sub>c\<langle>\<langle>p,q\<rangle>,r\<rangle>   \<rangle>"
             by (typecheck_cfuncs, smt comp_associative2 left_cart_proj_cfunc_prod transpose_func_def x_def y_def)
           also have "... = add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<nat>\<^sub>c , eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>))\<rangle>  \<circ>\<^sub>c\<langle>\<langle>p,q\<rangle>,r\<rangle>"
            using cfunc_prod_comp comp_associative2 by (typecheck_cfuncs, auto)
          also have "... = (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<nat>\<^sub>c) , eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>))\<rangle>  ) \<circ>\<^sub>c\<langle>\<langle>p,q\<rangle>,r\<rangle>"
            using comp_associative2 id_left_unit2 by (typecheck_cfuncs, auto)
          also have "... = (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)), eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>))\<rangle>  ) \<circ>\<^sub>c\<langle>\<langle>p,q\<rangle>,r\<rangle>"
            by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_cross_prod)
          also have "... = ((add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)), eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<rangle>)  \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>))) \<circ>\<^sub>c\<langle>\<langle>p,q\<rangle>,r\<rangle>"
            by (typecheck_cfuncs, smt cfunc_prod_comp cfunc_type_def comp_associative)
          also have "... = (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<rangle>) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>))\<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle>"  
            using comp_associative2  by (typecheck_cfuncs, auto)
          also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>)) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>))\<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle>"
            by (typecheck_cfuncs , smt comp_associative2 transpose_func_def)
          also have "... =  (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>)\<circ>\<^sub>c ((mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>))  \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle>"
            by (typecheck_cfuncs, smt comp_associative2 inv_transpose_func_def3 inv_transpose_of_composition transpose_func_def)
          also have "... = ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c))\<circ>\<^sub>c  (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f ((add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<^esup>)),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>)\<circ>\<^sub>c ((mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>) ))  \<circ>\<^sub>c x "
            using comp_associative2 x_def y_def by (typecheck_cfuncs, blast)
          then show "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c x"
            by (simp add: calculation)
        qed
      qed
    qed
    show "(mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor = (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>"
    proof(etcs_rule same_evals_equal[where Z = "\<nat>\<^sub>c", where X = "\<nat>\<^sub>c", where A = "(\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)"])
      show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor = eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>"
      proof(etcs_rule one_separator[where X ="(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c", where Y = "\<nat>\<^sub>c"])
        show "\<And>x. x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,
         \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
         (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c 
         (mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,
         \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c x"
        proof - 
          fix x
          assume x_type[type_rule]: "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c"
          obtain y r where y_type[type_rule]: "y \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c" and r_type[type_rule]:  "r \<in>\<^sub>c \<nat>\<^sub>c" and x_def: "x = \<langle>y,r\<rangle>"
            using cart_prod_decomp x_type by blast
          obtain p q where p_type[type_rule]: "p \<in>\<^sub>c \<nat>\<^sub>c" and q_type[type_rule]: "q \<in>\<^sub>c \<nat>\<^sub>c" and y_def:  "y = \<langle>p,q\<rangle>"
            using cart_prod_decomp y_type by blast


          have trip_shft: 
             "\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj  (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c, 
             \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj  (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c, 
              right_cart_proj  (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<rangle>\<rangle> \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle> = \<langle>p,\<langle>q,r\<rangle>\<rangle>"         
          proof - 
            have "\<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj  (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,  \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj  (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,   right_cart_proj  (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<rangle>\<rangle> \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle>  =  \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj  (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle>, \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj  (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c, right_cart_proj  (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<rangle>\<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle>\<rangle>"
              by (typecheck_cfuncs,  smt cfunc_prod_comp cfunc_type_def comp_associative)
            also have "... = \<langle>p,  \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj  (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle>, right_cart_proj  (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle>\<rangle>\<rangle>"
              by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 left_cart_proj_cfunc_prod)
            also have "... = \<langle>p, \<langle>q, r\<rangle>\<rangle>"
              by (typecheck_cfuncs, metis left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
            then show ?thesis using calculation by auto
          qed
          obtain g where g_def: "g = (mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c 
                                     \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
                                \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>
                                \<rangle>)\<^sup>\<sharp>"
          and g_type[type_rule]: "g: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
            by (typecheck_cfuncs, blast)

          


          have "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x 
              = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> )\<circ>\<^sub>c( (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor) \<circ>\<^sub>c x) "
            by (typecheck_cfuncs , smt comp_associative2 inv_transpose_func_def3 inv_transpose_of_composition x_type)
          also have "... = (mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)    \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f  successor) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle>"
            by (typecheck_cfuncs, metis flat_cancels_sharp inv_transpose_func_def3 x_def y_def) 
          also have "... = (mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
        \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>)
        \<circ>\<^sub>c \<langle>id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>p,q\<rangle>,successor  \<circ>\<^sub>c r\<rangle>"
            by (typecheck_cfuncs , smt cfunc_cross_prod_comp_cfunc_prod)
          also have "... = (mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,successor  \<circ>\<^sub>c r\<rangle>"
            by (typecheck_cfuncs, metis id_left_unit2)
          also have "... = mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>\<rangle>\<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,successor  \<circ>\<^sub>c r\<rangle>"
            using cfunc_type_def comp_associative  by (typecheck_cfuncs, fastforce)
          also have "... = mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,successor  \<circ>\<^sub>c r\<rangle> ,\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle>    \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,successor  \<circ>\<^sub>c r\<rangle>   \<rangle>"
            by (typecheck_cfuncs, smt cfunc_prod_comp cfunc_type_def comp_associative)
          also have "... = mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>p,q\<rangle> ,\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,successor  \<circ>\<^sub>c r\<rangle>  , (right_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,successor  \<circ>\<^sub>c r\<rangle>\<rangle>\<rangle>"
            by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 left_cart_proj_cfunc_prod)
          also have "... = mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>p ,\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>p,q\<rangle>  , successor  \<circ>\<^sub>c r  \<rangle>  \<rangle>"
            by (typecheck_cfuncs, smt left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)    
          also have "... = mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c  \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>p,\<langle>q,successor  \<circ>\<^sub>c r\<rangle>\<rangle>"
            by (typecheck_cfuncs, metis right_cart_proj_cfunc_prod)
          also have "... = mult2 \<circ>\<^sub>c  \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c p, mult2 \<circ>\<^sub>c \<langle>q,successor  \<circ>\<^sub>c r\<rangle>\<rangle>"
            using cfunc_cross_prod_comp_cfunc_prod  by (typecheck_cfuncs, auto)
          also have "... =   p \<cdot>\<^sub>\<nat> (q  \<cdot>\<^sub>\<nat> (successor  \<circ>\<^sub>c r))"
            using id_left_unit2 mult_def  by (typecheck_cfuncs, auto)
          also have "... = (q  \<cdot>\<^sub>\<nat> (successor  \<circ>\<^sub>c r))  \<cdot>\<^sub>\<nat> p"
            by (typecheck_cfuncs, simp add: mult_closure mult_commutative)
          also have "... = (q +\<^sub>\<nat> (q \<cdot>\<^sub>\<nat> r)) \<cdot>\<^sub>\<nat> p"
            by (typecheck_cfuncs, simp add: mult_respects_succ_right)
          also have "... = (q \<cdot>\<^sub>\<nat> p) +\<^sub>\<nat> ((q \<cdot>\<^sub>\<nat> r) \<cdot>\<^sub>\<nat> p)"
            by (typecheck_cfuncs, simp add: mult_Left_Distributivity mult_closure)
          also have "... = (p \<cdot>\<^sub>\<nat> q) +\<^sub>\<nat> (p \<cdot>\<^sub>\<nat> (q \<cdot>\<^sub>\<nat> r))"
            by (typecheck_cfuncs, simp add: mult_closure mult_commutative)
          also have "... = add2 \<circ>\<^sub>c \<langle>(p \<cdot>\<^sub>\<nat> q), (p \<cdot>\<^sub>\<nat> (q \<cdot>\<^sub>\<nat> r))\<rangle>"
            by (simp add: add_def)
          also have "... = add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>p,q\<rangle>, mult2\<circ>\<^sub>c \<langle>p , mult2\<circ>\<^sub>c\<langle>q,r\<rangle>\<rangle>\<rangle>"
            by (simp add: mult_def)
          also have "... = add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>p,q\<rangle>,r\<rangle>, mult2\<circ>\<^sub>c \<langle>id \<nat>\<^sub>c \<circ>\<^sub>c  p , mult2\<circ>\<^sub>c\<langle>q,r\<rangle>\<rangle>\<rangle>"
            by(typecheck_cfuncs, metis id_left_unit2 left_cart_proj_cfunc_prod)
          also have "... = add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c x,  mult2\<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>p ,\<langle>q,r\<rangle>\<rangle>\<rangle>"
            by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod x_def y_def)   
          also have "... = add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c x,  mult2\<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c         left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c  \<langle>\<langle>p,q\<rangle>,r\<rangle>\<rangle>"
            by (simp add: trip_shft)
          also have "... = add2 \<circ>\<^sub>c \<langle>(mult2 \<circ>\<^sub>c id (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)  \<circ>\<^sub>c  left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c x,  mult2\<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c x\<rangle>"
            using cfunc_type_def comp_associative id_left_unit2 x_def y_def by (typecheck_cfuncs, smt)
          also have "... = add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (id (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)  \<circ>\<^sub>c  left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) , mult2\<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c         left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle> \<rangle> \<circ>\<^sub>c x"
            by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 x_type)
          also have "... = add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>) \<circ>\<^sub>c (id (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f g)), mult2\<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>\<rangle> \<circ>\<^sub>c x"
            by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_cross_prod)
          also have "... = add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>) \<circ>\<^sub>c (id (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f g)), eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f g)\<rangle> \<circ>\<^sub>c x"
            using g_def transpose_func_def by (typecheck_cfuncs, auto)
          also have "... = ((add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)) ,  eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>) \<circ>\<^sub>c (id (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f g)) \<circ>\<^sub>c x"
            by (etcs_assocr, typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
          also have "... = ((eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f  (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)) , eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c (id (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f g)) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, simp add: transpose_func_def)
          also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c ( id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)) , eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c id (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f g) \<circ>\<^sub>c x" 
            by (etcs_assocr, typecheck_cfuncs)
          also have "... = (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c ( id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f(add2 \<circ>\<^sub>c\<langle>mult2 \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>)) , eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>cg)) \<circ>\<^sub>c x"
            by (typecheck_cfuncs, metis identity_distributes_across_composition)
          then show  "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor) \<circ>\<^sub>c x =
                      (eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>),eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c x "
            using g_def by (simp add: calculation)
          qed
        qed
      qed
    qed

  have main_result_flat: "mult2 \<circ>\<^sub>c mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c =
       mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>"
    by (typecheck_cfuncs, metis flat_cancels_sharp main_result)

  have "(a \<cdot>\<^sub>\<nat>  b) \<cdot>\<^sub>\<nat> c = mult2 \<circ>\<^sub>c \<langle>a \<cdot>\<^sub>\<nat> b, c\<rangle>"
    by (simp add: mult_def)
  also have "... = mult2 \<circ>\<^sub>c \<langle> mult2 \<circ>\<^sub>c \<langle>a,b\<rangle>, id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c c\<rangle>"
    using assms(3) id_left_unit2 mult_def by auto
  also have "... = mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, c\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
  also have "... = (mult2 \<circ>\<^sub>c (mult2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, c\<rangle>"
    using assms by (typecheck_cfuncs, meson comp_associative2)
  also have "... =  mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c \<langle>  \<langle>a,b\<rangle>, c\<rangle>"
    by (typecheck_cfuncs, smt (z3) cfunc_type_def comp_associative domain_comp main_result_flat assms)
  also have "... =  mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c \<langle>  \<langle>a,b\<rangle>, c\<rangle> ,\<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c \<langle>  \<langle>a,b\<rangle>, c\<rangle> ,right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c \<langle>  \<langle>a,b\<rangle>, c\<rangle> \<rangle> \<rangle>"
    using assms cfunc_prod_comp comp_associative2 by (typecheck_cfuncs, force)
  also have "... =  mult2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f mult2) \<circ>\<^sub>c \<langle>a ,\<langle>b ,c\<rangle>\<rangle>"
    by (typecheck_cfuncs, smt assms left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  also have "... =  mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  a ,mult2 \<circ>\<^sub>c \<langle>b, c\<rangle>\<rangle>"
    using assms cfunc_cross_prod_comp_cfunc_prod by (typecheck_cfuncs, force)
  also have "... =  mult2 \<circ>\<^sub>c \<langle>a, b \<cdot>\<^sub>\<nat> c \<rangle>"
    using assms(1) id_left_unit2 mult_def by auto
  also have "... = a \<cdot>\<^sub>\<nat> (b \<cdot>\<^sub>\<nat> c )"
    by (simp add: mult_def)
  then show ?thesis using calculation by auto
qed




lemma mult_right_distributivity:
  assumes "a \<in>\<^sub>c  \<nat>\<^sub>c"  "b\<in>\<^sub>c  \<nat>\<^sub>c"  "c\<in>\<^sub>c  \<nat>\<^sub>c"
  shows "a \<cdot>\<^sub>\<nat> ( b +\<^sub>\<nat> c)   = (a \<cdot>\<^sub>\<nat> b) +\<^sub>\<nat>  (a \<cdot>\<^sub>\<nat> c)"
  using add_type assms mult_Left_Distributivity mult_commutative by auto





lemma mult_cancellative_contrapositve:
  assumes "a \<in>\<^sub>c \<nat>\<^sub>c" "b \<in>\<^sub>c \<nat>\<^sub>c" "c \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "a \<noteq> b"
  shows "a \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c c) \<noteq> b \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c c)"
proof(cases "leq \<circ>\<^sub>c \<langle>a, b\<rangle> = \<t>")
  assume ab: "leq \<circ>\<^sub>c \<langle>a,b\<rangle> = \<t>"
  have f1: "a \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c c) = (a  \<cdot>\<^sub>\<nat> c) +\<^sub>\<nat>  a"
    using add_commutes assms(1,3) mult_closure mult_respects_succ_right by fastforce  
  obtain k where k_type[type_rule]: "k \<in>\<^sub>c \<nat>\<^sub>c" and k_def: "k +\<^sub>\<nat> a = b"
    using assms ab leq_true_implies_exists by auto
  have f2: "((k  \<cdot>\<^sub>\<nat> c) +\<^sub>\<nat>  k)+\<^sub>\<nat> ((a  \<cdot>\<^sub>\<nat> c) +\<^sub>\<nat>  a ) = b \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c c)"
    using add_commutes assms(1,3) k_def mult_Left_Distributivity mult_respects_succ_right by (typecheck_cfuncs, fastforce)
  have "(k  \<cdot>\<^sub>\<nat> c) +\<^sub>\<nat>  k \<noteq> zero"
    by (typecheck_cfuncs, metis add_monotonic add_respects_zero_on_left assms exists_implies_leq_true k_def lqe_antisymmetry)
  then show "a \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c c) \<noteq> b \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c c)"
    by (typecheck_cfuncs, metis  add_cancellative add_respects_zero_on_left add_type assms(1,3) f1 f2 k_type mult_type zero_type)
next
  assume "leq \<circ>\<^sub>c \<langle>a,b\<rangle> \<noteq> \<t>"
  then have ba: "leq \<circ>\<^sub>c \<langle>b,a\<rangle> = \<t>"
    using assms(1,2) lqe_connexity by blast    
  obtain k where k_type[type_rule]: "k \<in>\<^sub>c \<nat>\<^sub>c" and k_def: "k +\<^sub>\<nat> b = a" and k_nonzero: "k \<noteq> zero"
    by (metis add_respects_zero_on_left assms(1,2,4) ba leq_true_implies_exists)
  have f1: "b \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c c) = (b  \<cdot>\<^sub>\<nat> c) +\<^sub>\<nat>  b"
    using add_commutes assms(2,3) mult_closure mult_respects_succ_right by fastforce  
  have f2: "((k  \<cdot>\<^sub>\<nat> c) +\<^sub>\<nat>  k)+\<^sub>\<nat> ((b  \<cdot>\<^sub>\<nat> c) +\<^sub>\<nat>  b ) = a \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c c)"
    using add_commutes assms(2,3) k_def mult_Left_Distributivity mult_respects_succ_right by (typecheck_cfuncs, fastforce)
  have "(k  \<cdot>\<^sub>\<nat> c) +\<^sub>\<nat>  k \<noteq> zero"
    by (typecheck_cfuncs, metis assms(3) exists_implies_leq_true k_nonzero lqe_antisymmetry zero_is_smallest)
  then show "a \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c c) \<noteq> b \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c c)"
    by (metis add_cancellative add_respects_zero_on_left add_type assms(2,3) f1 f2 k_type mult_type zero_type)
qed

lemma mult_cancellative:
  assumes "a \<in>\<^sub>c \<nat>\<^sub>c" "b \<in>\<^sub>c \<nat>\<^sub>c" "c \<in>\<^sub>c \<nat>\<^sub>c" "c \<noteq> zero"
  shows  "(a \<cdot>\<^sub>\<nat> c = b \<cdot>\<^sub>\<nat> c) = (a = b)"
  using assms mult_cancellative_contrapositve nonzero_is_succ by blast

lemma l_mult_cancellative:
  assumes "a \<in>\<^sub>c \<nat>\<^sub>c" "b \<in>\<^sub>c \<nat>\<^sub>c" "c \<in>\<^sub>c \<nat>\<^sub>c" "c \<noteq> zero"
  shows  "(c \<cdot>\<^sub>\<nat> a = c \<cdot>\<^sub>\<nat> b) = (a = b)"
  by (metis assms mult_cancellative_contrapositve mult_commutative nonzero_is_succ)




lemma mult_monotonic:
  assumes m_type: "m \<in>\<^sub>c \<nat>\<^sub>c" and n_type: "n \<in>\<^sub>c \<nat>\<^sub>c" and u_type: "u \<in>\<^sub>c \<nat>\<^sub>c" and v_type: "v \<in>\<^sub>c \<nat>\<^sub>c"
  assumes m_leq_n: "leq \<circ>\<^sub>c \<langle>m, n\<rangle> = \<t>" 
  assumes u_leq_v: "leq \<circ>\<^sub>c \<langle>u, v\<rangle> = \<t>" 
  shows "leq \<circ>\<^sub>c \<langle>m \<cdot>\<^sub>\<nat> u, n \<cdot>\<^sub>\<nat> v\<rangle> = \<t>"
proof - 
  obtain k where k_def: "k \<in>\<^sub>c \<nat>\<^sub>c \<and> k +\<^sub>\<nat> m = n"
    using leq_true_implies_exists m_leq_n m_type n_type by auto
  obtain j where j_def:  "j \<in>\<^sub>c \<nat>\<^sub>c \<and> j +\<^sub>\<nat> u = v"
    using leq_true_implies_exists u_leq_v u_type v_type by auto
  have "n \<cdot>\<^sub>\<nat> v = (k +\<^sub>\<nat> m) \<cdot>\<^sub>\<nat> (j +\<^sub>\<nat> u)"
    by (simp add: j_def k_def)
  also have "... = ((k +\<^sub>\<nat> m)\<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> ((k +\<^sub>\<nat> m)\<cdot>\<^sub>\<nat> u)"
    using j_def k_def mult_right_distributivity n_type u_type by blast
  also have "... = ((k \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> (k \<cdot>\<^sub>\<nat> u)) +\<^sub>\<nat> ((m \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> (m \<cdot>\<^sub>\<nat> u))"
    by (typecheck_cfuncs, metis j_def k_def m_type mult_Left_Distributivity mult_right_distributivity u_type v_type)
  also have "... = ((k \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> (k \<cdot>\<^sub>\<nat> u) +\<^sub>\<nat> (m \<cdot>\<^sub>\<nat> j)) +\<^sub>\<nat> (m \<cdot>\<^sub>\<nat> u)" 
    by (typecheck_cfuncs, simp add: add_associates j_def k_def m_type u_type)
  then show "leq \<circ>\<^sub>c \<langle>m \<cdot>\<^sub>\<nat> u, n \<cdot>\<^sub>\<nat> v\<rangle> = \<t>"
    by (metis add_type calculation exists_implies_leq_true j_def k_def m_type mult_closure u_type)
qed

lemma equal_sqrs_equal: 
  assumes m_type: "m \<in>\<^sub>c \<nat>\<^sub>c" and n_type: "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes eq_sqr: "m \<cdot>\<^sub>\<nat> m = n \<cdot>\<^sub>\<nat> n"
  shows "m = n"
proof(rule ccontr)
  assume "m \<noteq> n"
  show False
  proof(cases "leq \<circ>\<^sub>c \<langle>m, n\<rangle> = \<t>")
    assume "leq \<circ>\<^sub>c \<langle>m,n\<rangle> = \<t>"
    have mm_leq_mn: "leq \<circ>\<^sub>c \<langle>m \<cdot>\<^sub>\<nat> m, m \<cdot>\<^sub>\<nat> n\<rangle> = \<t>"
      using \<open>leq \<circ>\<^sub>c \<langle>m,n\<rangle> = \<t>\<close> lqe_connexity m_type mult_monotonic n_type by blast
    have mn_leq_nn: "leq \<circ>\<^sub>c \<langle>m \<cdot>\<^sub>\<nat> n, n \<cdot>\<^sub>\<nat> n\<rangle> = \<t>"
      using \<open>leq \<circ>\<^sub>c \<langle>m,n\<rangle> = \<t>\<close> lqe_connexity m_type mult_monotonic n_type by blast
    have mn_neq_nn: "m \<cdot>\<^sub>\<nat> n \<noteq> n \<cdot>\<^sub>\<nat> n"
      using \<open>leq \<circ>\<^sub>c \<langle>m,n\<rangle> = \<t>\<close> \<open>m \<noteq> n\<close> lqe_antisymmetry m_type mult_cancellative n_type zero_is_smallest by blast
    have "m \<cdot>\<^sub>\<nat> n \<noteq> m \<cdot>\<^sub>\<nat> n"
      using eq_sqr lqe_antisymmetry m_type mm_leq_mn mn_leq_nn mn_neq_nn mult_closure n_type by auto
    then show False
      by simp
  next
    assume "leq \<circ>\<^sub>c \<langle>m,n\<rangle> \<noteq> \<t>"
    then have "leq \<circ>\<^sub>c \<langle>n,m\<rangle> = \<t>"
      using lqe_connexity m_type n_type by blast
    have mm_leq_mn: "leq \<circ>\<^sub>c \<langle>n \<cdot>\<^sub>\<nat> n, n \<cdot>\<^sub>\<nat> m\<rangle> = \<t>"
      using \<open>leq \<circ>\<^sub>c \<langle>n,m\<rangle> = \<t>\<close> lqe_connexity m_type mult_monotonic n_type by blast
    have mn_leq_nn: "leq \<circ>\<^sub>c \<langle>n \<cdot>\<^sub>\<nat> m, m \<cdot>\<^sub>\<nat> m\<rangle> = \<t>"
      using \<open>leq \<circ>\<^sub>c \<langle>n,m\<rangle> = \<t>\<close> lqe_connexity m_type mult_monotonic n_type by blast
    have mn_neq_nn: "n \<cdot>\<^sub>\<nat> m \<noteq> m \<cdot>\<^sub>\<nat> m"
      using \<open>leq \<circ>\<^sub>c \<langle>n,m\<rangle> = \<t>\<close> \<open>m \<noteq> n\<close> lqe_antisymmetry m_type mult_cancellative n_type zero_is_smallest by blast
    have "n \<cdot>\<^sub>\<nat> m \<noteq> n \<cdot>\<^sub>\<nat> m"
      using eq_sqr lqe_antisymmetry m_type mm_leq_mn mn_leq_nn mn_neq_nn mult_closure n_type by auto
    then show False
      by simp
  qed
qed

lemma mult_leq_cancellative: 
  assumes n_type: "n \<in>\<^sub>c \<nat>\<^sub>c" and u_type: "u \<in>\<^sub>c \<nat>\<^sub>c" and v_type: "v \<in>\<^sub>c \<nat>\<^sub>c"
  assumes n_nonzer: "n \<noteq> zero"
  assumes nu_leq_nv: "leq \<circ>\<^sub>c \<langle>n \<cdot>\<^sub>\<nat> u, n \<cdot>\<^sub>\<nat> v\<rangle> = \<t>"
  shows "leq \<circ>\<^sub>c \<langle>u, v\<rangle> = \<t>"
proof(cases "u=v")
  show "u = v \<Longrightarrow> leq \<circ>\<^sub>c \<langle>u,v\<rangle> = \<t>"
    using lqe_connexity v_type by blast
next 
  assume neq: "u \<noteq> v" 
  show "leq \<circ>\<^sub>c \<langle>u,v\<rangle> = \<t>"
  proof(rule ccontr)
    assume "leq \<circ>\<^sub>c \<langle>u,v\<rangle> \<noteq> \<t>"
    then have "leq \<circ>\<^sub>c \<langle>v,u\<rangle> = \<t>"
      using lqe_connexity u_type v_type by blast
    then have "leq \<circ>\<^sub>c \<langle>n \<cdot>\<^sub>\<nat> v,n \<cdot>\<^sub>\<nat> u\<rangle> = \<t>"
      using lqe_connexity mult_monotonic n_type u_type v_type by blast
    then have "n \<cdot>\<^sub>\<nat> v = n \<cdot>\<^sub>\<nat> u"
      by (simp add: lqe_antisymmetry mult_closure n_type nu_leq_nv u_type v_type)
    then have "v = u"
      using l_mult_cancellative n_nonzer n_type u_type v_type by blast
    then show False
      using neq by blast
  qed
qed

(*
lemma mult_monotonic_converse:
  assumes m_type: "m \<in>\<^sub>c \<nat>\<^sub>c" and n_type: "n \<in>\<^sub>c \<nat>\<^sub>c" and u_type: "u \<in>\<^sub>c \<nat>\<^sub>c" and v_type: "v \<in>\<^sub>c \<nat>\<^sub>c"
  assumes m_nonzero: "m \<noteq> zero"
  assumes m_leq_n: "leq \<circ>\<^sub>c \<langle>m, n\<rangle> = \<t>" 
  assumes mu_leq_nv: "leq \<circ>\<^sub>c \<langle>m \<cdot>\<^sub>\<nat> u, n \<cdot>\<^sub>\<nat> v\<rangle> = \<t>"
  shows u_leq_v: "leq \<circ>\<^sub>c \<langle>u, v\<rangle> = \<t>"
(*NOT TRUE*) 
 3 < 5 and 3*6 < 4*5 as 18 < 20 nevertheless it is false that 6<5.
*)

lemma FOIL:
  assumes "a \<in>\<^sub>c \<nat>\<^sub>c" "b \<in>\<^sub>c \<nat>\<^sub>c" "c \<in>\<^sub>c \<nat>\<^sub>c" "d \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(a +\<^sub>\<nat> b) \<cdot>\<^sub>\<nat> (c +\<^sub>\<nat> d)  = (a \<cdot>\<^sub>\<nat> c) +\<^sub>\<nat> (a \<cdot>\<^sub>\<nat> d) +\<^sub>\<nat> (b \<cdot>\<^sub>\<nat> c) +\<^sub>\<nat> (b \<cdot>\<^sub>\<nat> d)"
  using assms by (typecheck_cfuncs, metis add_associates mult_Left_Distributivity mult_right_distributivity)

lemma FOIL_2:
  assumes "a \<in>\<^sub>c \<nat>\<^sub>c" "b \<in>\<^sub>c \<nat>\<^sub>c" "c \<in>\<^sub>c \<nat>\<^sub>c" "d \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(a +\<^sub>\<nat> b) \<cdot>\<^sub>\<nat> (c +\<^sub>\<nat> d)  = (a \<cdot>\<^sub>\<nat> c) +\<^sub>\<nat> (a \<cdot>\<^sub>\<nat> d) +\<^sub>\<nat> (c \<cdot>\<^sub>\<nat> b) +\<^sub>\<nat> (b \<cdot>\<^sub>\<nat> d)"
  using assms by (typecheck_cfuncs, simp add: FOIL mult_commutative)



(*Parity results:*)

lemma nth_even_is_times_two:
  "nth_even = mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>"
proof (etcs_rule natural_number_object_func_unique[where f="successor \<circ>\<^sub>c successor", where X="\<nat>\<^sub>c"])

  show "nth_even \<circ>\<^sub>c zero = (mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero"
  proof -
    have "(mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero
      = mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = mult2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero, zero\<rangle>"
      by (typecheck_cfuncs, simp add: cart_prod_extract_right)
    also have "... = zero"
      using mult_def mult_respects_zero_right succ_n_type zero_type by auto
    also have "... = nth_even \<circ>\<^sub>c zero"
      by (simp add: nth_even_def2)
    then show ?thesis
      using calculation by auto
  qed

  show "nth_even \<circ>\<^sub>c successor = (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even"
    by (simp add: nth_even_successor)

  show "(mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor =
    (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
  proof -
    have "(mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor
      = mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c successor"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, successor\<rangle>"
      by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 id_left_unit2 terminal_func_comp)
    also have "... = add2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c  \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>"
      using mult2_respects_succ_right by (typecheck_cfuncs, blast)
    also have "... = add2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero \<circ>\<^sub>c  \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = successor \<circ>\<^sub>c successor \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c  \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>"
      by (typecheck_cfuncs, simp add: add2_commutes_succ add2_respects_succ_right)
    also have "... = successor \<circ>\<^sub>c successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
      by (typecheck_cfuncs, simp add: add2_respects_zero_on_left)
    also have "... = (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
      by (typecheck_cfuncs, smt comp_associative2)
    then show ?thesis
      using calculation by auto
  qed
qed

lemma nth_even_is_times_twoB:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "nth_even \<circ>\<^sub>c n = (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> n"
proof - 
  have "nth_even \<circ>\<^sub>c n  = (mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c n"
    using nth_even_is_times_two by auto
  also have "... = mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c n"
    using assms by (typecheck_cfuncs, simp add: comp_associative2)
  also have "... = mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c n, id \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
  also have "... = mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c id(\<one>), id \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>"
    using assms by (typecheck_cfuncs, metis terminal_func_unique)
  also have "... = mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero), n\<rangle>"
    using assms by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2)
  also have "... = (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> n"
    by (simp add: mult_def)
  then show ?thesis using calculation by auto
qed

lemma nth_odd_is_succ_times_two:
  "nth_odd = successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>"
proof (etcs_rule natural_number_object_func_unique[where f="successor \<circ>\<^sub>c successor", where X="\<nat>\<^sub>c"])
  show "nth_odd \<circ>\<^sub>c zero =
    (successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero"
  proof -
    have "(successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero
      = successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero, zero\<rangle>"
      by (typecheck_cfuncs, simp add: cart_prod_extract_right)
    also have "... = successor \<circ>\<^sub>c zero"
      using mult_def mult_respects_zero_right succ_n_type zero_type by auto
    also have "... = nth_odd \<circ>\<^sub>c zero"
      by (simp add: nth_odd_def2)
    then show ?thesis
      using calculation by auto
  qed

  show "nth_odd \<circ>\<^sub>c successor = (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_odd"
    by (simp add: nth_odd_successor)

  show "(successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor =
    (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c  successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
  proof -
    have "(successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor
      = successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c successor"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, successor\<rangle>"
      by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 id_left_unit2 terminal_func_comp)
    also have "... = successor \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c  \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>"
      using mult2_respects_succ_right by (typecheck_cfuncs, auto)
    also have "... = successor \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero \<circ>\<^sub>c  \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c  \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>"
      by (typecheck_cfuncs, simp add: add2_commutes_succ add2_respects_succ_right)
    also have "... = successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
      by (typecheck_cfuncs, simp add: add2_respects_zero_on_left)
    also have "... = (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
      by (typecheck_cfuncs, smt comp_associative2)
    then show ?thesis
      using calculation by auto
  qed
qed

lemma nth_odd_is_succ_times_twoB:
 assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
 shows "nth_odd \<circ>\<^sub>c n = successor \<circ>\<^sub>c((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> n)"
proof - 
  have "nth_odd \<circ>\<^sub>c n = (successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c n"
    by (simp add: nth_odd_is_succ_times_two)
  also have "... = successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c n"
    using assms by (typecheck_cfuncs, simp add: cfunc_type_def comp_associative)
  also have "... = successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c n, id \<nat>\<^sub>c \<circ>\<^sub>c n \<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
  also have "... = successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<circ>\<^sub>c id(\<one>), id \<nat>\<^sub>c \<circ>\<^sub>c n \<rangle>"
    using assms by (typecheck_cfuncs, metis terminal_func_unique)
  also have "... = successor \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero), n \<rangle>"
    using assms by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2)
  also have "... = successor \<circ>\<^sub>c((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> n)"
    by (simp add: mult_def)
  then show ?thesis using calculation by auto
qed

lemma add_evens_is_even:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "j \<in>\<^sub>c \<nat>\<^sub>c \<and> (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j = m"
  assumes "k \<in>\<^sub>c \<nat>\<^sub>c \<and> (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k = n"
  shows   "(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> (j +\<^sub>\<nat> k) = m +\<^sub>\<nat> n"
proof - 
  have m_pls_n: "m +\<^sub>\<nat> n = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k)"
    using assms(3,4) by blast
  also have "... = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)) \<cdot>\<^sub>\<nat> (j +\<^sub>\<nat> k)"
    by (typecheck_cfuncs, simp add: assms(3,4) mult_right_distributivity)
  then show ?thesis
    by (simp add: m_pls_n)
qed


lemma add_odds_is_even:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "j \<in>\<^sub>c \<nat>\<^sub>c \<and> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = m"
  assumes "k \<in>\<^sub>c \<nat>\<^sub>c \<and> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = n"
  shows   "(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> ((j +\<^sub>\<nat> k) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero)) = (m +\<^sub>\<nat> n)"
proof - 
  have m_pls_n: "m +\<^sub>\<nat> n = (((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero)) +\<^sub>\<nat> (((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero))"
    using assms(3,4) by blast
  also have "... = (((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k)) +\<^sub>\<nat> ((successor \<circ>\<^sub>c zero) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero))"
    by (typecheck_cfuncs, simp add: add_associates_mix_commutes assms(3,4))
  also have "... = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> (j +\<^sub>\<nat> k)) +\<^sub>\<nat> ((successor \<circ>\<^sub>c zero) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero))"
    by (typecheck_cfuncs, simp add: assms(3,4) mult_right_distributivity)
  also have "... = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> (j +\<^sub>\<nat> k)) +\<^sub>\<nat> (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero)"
    by (simp add: one_plus_one_is_two)
  also have "... = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> (j +\<^sub>\<nat> k)) +\<^sub>\<nat> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c zero))"
    by (typecheck_cfuncs, simp add: s0_is_right_id)
  also have "... = (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> ((j +\<^sub>\<nat> k) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero))"
    by (typecheck_cfuncs, simp add: assms(3,4) mult_right_distributivity)
  then show ?thesis
    by (simp add: calculation)
qed


lemma add_mixed_is_odd: 
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "j \<in>\<^sub>c \<nat>\<^sub>c \<and> (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j = m"
  assumes "k \<in>\<^sub>c \<nat>\<^sub>c \<and> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = n"
  shows   "((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> (j +\<^sub>\<nat> k) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero)) = m +\<^sub>\<nat> n"
  using add_associates assms(3,4) mult_closure mult_right_distributivity succ_n_type zero_type by force




lemma mult_even_is_even:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "j \<in>\<^sub>c \<nat>\<^sub>c \<and> (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j = m"
  shows   "(successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> (j \<cdot>\<^sub>\<nat> n) = m \<cdot>\<^sub>\<nat> n"
proof - 
  have " m \<cdot>\<^sub>\<nat> n = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j) \<cdot>\<^sub>\<nat> n"
    using assms(3) by presburger
  also have "... = (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> (j \<cdot>\<^sub>\<nat> n)"
    by (typecheck_cfuncs, simp add: assms(2,3) mult_associative)
  then show ?thesis
    by (simp add: calculation)
qed

lemma mult_odds_is_odd:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "\<exists>j. j \<in>\<^sub>c \<nat>\<^sub>c \<and> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = m"
  assumes "\<exists>k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = n"
  shows   "\<exists>l. l \<in>\<^sub>c \<nat>\<^sub>c \<and> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> l) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = m \<cdot>\<^sub>\<nat> n"
proof - 
  obtain j where j_def: "j \<in>\<^sub>c \<nat>\<^sub>c \<and> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = m"
    using assms(3) by blast
  obtain k where k_def: "k \<in>\<^sub>c \<nat>\<^sub>c \<and> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = n"
    using assms(4) by blast
  have "m \<cdot>\<^sub>\<nat> n = (((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j) \<cdot>\<^sub>\<nat> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k)) +\<^sub>\<nat> 
                 (((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j)  \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c zero)) +\<^sub>\<nat>
               ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k)  \<cdot>\<^sub>\<nat>  (successor \<circ>\<^sub>c zero) +\<^sub>\<nat> 
                (successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat>   (successor \<circ>\<^sub>c zero)"
    using FOIL_2 j_def k_def mult_closure succ_n_type zero_type by auto
  also have "... = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> (j \<cdot>\<^sub>\<nat> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k))) +\<^sub>\<nat> 
                   ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> (j \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c zero))) +\<^sub>\<nat>
                   ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> (k \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c zero))) +\<^sub>\<nat> 
                (successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat>   (successor \<circ>\<^sub>c zero)"
    by (simp add: j_def k_def mult_associative mult_closure succ_n_type zero_type)
  also have "... = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> 
        ( (j \<cdot>\<^sub>\<nat> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k)) +\<^sub>\<nat> (j \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c zero)) +\<^sub>\<nat> (k \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c zero))))
        +\<^sub>\<nat>  (successor \<circ>\<^sub>c zero)"
    by (smt assms(2) j_def k_def mult_closure mult_right_distributivity s0_is_right_id succ_n_type zero_type)
  then show ?thesis
    by (typecheck_cfuncs, metis add_type calculation j_def k_def mult_closure)
qed

lemma even_or_odd2:
  assumes n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(\<exists> m. m \<in>\<^sub>c \<nat>\<^sub>c \<and>  n = successor \<circ>\<^sub>c((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> m)) \<or> 
         (\<exists> m. m \<in>\<^sub>c \<nat>\<^sub>c \<and>  n =              (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> m)"
  by (typecheck_cfuncs, metis nth_even_is_times_twoB nth_even_or_nth_odd nth_odd_is_succ_times_twoB)





lemma not_even_and_odd2:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "\<not>((\<exists> m. m \<in>\<^sub>c \<nat>\<^sub>c \<and>  n = successor \<circ>\<^sub>c((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> m)) \<and> 
           (\<exists> m. m \<in>\<^sub>c \<nat>\<^sub>c \<and>  n =              (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> m))"
  by (smt (z3) assms comp_associative2 halve_nth_even halve_nth_odd halve_type id_left_unit2 n_neq_succ_n nth_even_is_times_twoB nth_even_type nth_odd_def2 nth_odd_is_succ_times_twoB)


lemma add_evens_is_even2:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "is_even \<circ>\<^sub>c m = \<t>" "is_even \<circ>\<^sub>c n = \<t>"
  shows "is_even \<circ>\<^sub>c (m +\<^sub>\<nat> n) = \<t>"
proof-
  obtain p where m_def: "p \<in>\<^sub>c \<nat>\<^sub>c \<and> m = nth_even \<circ>\<^sub>c p"
    using assms(1,3) is_even_exists_nth_even by blast
  obtain q where n_def: "q \<in>\<^sub>c \<nat>\<^sub>c \<and> n = nth_even \<circ>\<^sub>c q"
    using assms(2,4) is_even_exists_nth_even by blast
  have m_def2: "m = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> p)"
    by (simp add: m_def nth_even_is_times_twoB)
  have n_def2: "n = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> q)"
    by (simp add: n_def nth_even_is_times_twoB)
  have "m +\<^sub>\<nat> n  = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> (p +\<^sub>\<nat> q))"  
    using m_def m_def2 mult_right_distributivity n_def n_def2 by (typecheck_cfuncs, auto)
  then have "m +\<^sub>\<nat> n  = nth_even \<circ>\<^sub>c (p +\<^sub>\<nat> q)"
    by (simp add: add_type m_def n_def nth_even_is_times_twoB)
  then have "is_even \<circ>\<^sub>c (m +\<^sub>\<nat> n) = (is_even \<circ>\<^sub>c  nth_even) \<circ>\<^sub>c (p +\<^sub>\<nat> q)"
    by (typecheck_cfuncs, metis  comp_associative2 m_def n_def)
  also have "... =  (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c (p +\<^sub>\<nat> q)"
    by (simp add: is_even_nth_even_true)
  also have "... = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c (p +\<^sub>\<nat> q)"
    using comp_associative2 m_def n_def by (typecheck_cfuncs, fastforce)
  also have "... = \<t> \<circ>\<^sub>c id(\<one>)"
    by (typecheck_cfuncs, metis m_def n_def terminal_func_unique)
  also have "... = \<t>"
    by (typecheck_cfuncs, simp add: id_right_unit2)
  then show ?thesis
    by (simp add: calculation)
qed

lemma add_odds_is_even2:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "is_odd \<circ>\<^sub>c m = \<t>" "is_odd \<circ>\<^sub>c n = \<t>"
  shows "is_even \<circ>\<^sub>c (m +\<^sub>\<nat> n) = \<t>"
proof-
  obtain p where m_def: "p \<in>\<^sub>c \<nat>\<^sub>c \<and> m = nth_odd \<circ>\<^sub>c p"
    using assms(1,3) is_odd_exists_nth_odd by blast
  obtain q where n_def: "q \<in>\<^sub>c \<nat>\<^sub>c \<and> n = nth_odd \<circ>\<^sub>c q"
    using assms(2,4) is_odd_exists_nth_odd by blast
  have m_def2: "m = successor \<circ>\<^sub>c ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> p) "
    using m_def nth_odd_is_succ_times_twoB by blast
  then have m_def3: "m = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> p) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero)"
    using add_respects_succ1 add_respects_zero_on_right m_def m_def2 by (typecheck_cfuncs, auto)
  have n_def2: "n = successor \<circ>\<^sub>c ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> q)"
    using n_def nth_odd_is_succ_times_twoB by blast
  have n_def3: "n= ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> q) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero)"
    using add_respects_succ1 add_respects_zero_on_right n_def n_def2 by (typecheck_cfuncs, auto)
  have "(m +\<^sub>\<nat> n) = (successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> ((p +\<^sub>\<nat> q) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero))"
    using add_odds_is_even assms(1,2) m_def m_def3 n_def n_def3 by auto  
  then have "(m +\<^sub>\<nat> n) = nth_even \<circ>\<^sub>c ((p +\<^sub>\<nat> q) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero))"
    by (typecheck_cfuncs, simp add:  m_def n_def nth_even_is_times_twoB)
  then have "is_even \<circ>\<^sub>c (m +\<^sub>\<nat> n) = (is_even \<circ>\<^sub>c  nth_even) \<circ>\<^sub>c ((p +\<^sub>\<nat> q) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero))"
    using   comp_associative2 m_def n_def by (typecheck_cfuncs, auto)
  also have  "...  =  (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c ((p +\<^sub>\<nat> q) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero))"
    by (typecheck_cfuncs, simp add:  is_even_nth_even_true)
  also have "...  =  \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c ((p +\<^sub>\<nat> q) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero))"
    using  comp_associative2 m_def n_def by (typecheck_cfuncs, auto)
  also have "... = \<t> \<circ>\<^sub>c id(\<one>)"
    by (typecheck_cfuncs, metis m_def n_def terminal_func_unique)
  also have "... = \<t>"
    by (typecheck_cfuncs, simp add: id_right_unit2)
  then show ?thesis
    by (simp add: calculation)
qed

lemma add_mixed_is_odd2:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "is_odd \<circ>\<^sub>c m = \<t>" "is_even \<circ>\<^sub>c n = \<t>"
  shows "is_odd \<circ>\<^sub>c (m +\<^sub>\<nat> n) = \<t>"
  by (typecheck_cfuncs, smt add_evens_is_even2 add_respects_succ3 assms cfunc_type_def comp_associative comp_type is_even_def2 is_odd_not_is_even successor_type)

lemma mult_evens_is_even2:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "is_even \<circ>\<^sub>c m = \<t>" 
  shows "is_even \<circ>\<^sub>c (m \<cdot>\<^sub>\<nat> n) = \<t>"
proof - 
  obtain p where m_def: "p \<in>\<^sub>c \<nat>\<^sub>c \<and> m = nth_even \<circ>\<^sub>c p"
    using assms(1,3) is_even_exists_nth_even by blast
  have m_def2: "m = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> p)"
    by (simp add: m_def nth_even_is_times_twoB)
  then have mn_def: "m \<cdot>\<^sub>\<nat> n = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> (p \<cdot>\<^sub>\<nat> n))"
    by (simp add: assms(2) m_def mult_associative succ_n_type zero_type)
  then have "(m \<cdot>\<^sub>\<nat> n) = nth_even \<circ>\<^sub>c (p \<cdot>\<^sub>\<nat> n)"
    by (simp add: assms(2) m_def mult_closure nth_even_is_times_twoB)
  then have "is_even \<circ>\<^sub>c (m \<cdot>\<^sub>\<nat> n) = (is_even \<circ>\<^sub>c  nth_even) \<circ>\<^sub>c (p \<cdot>\<^sub>\<nat> n)"
    by (typecheck_cfuncs, metis assms(2) comp_associative2 m_def)
  also have "... =  (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c (p \<cdot>\<^sub>\<nat> n)"
    by (simp add: is_even_nth_even_true)
  also have "... = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c (p \<cdot>\<^sub>\<nat> n)"
    using assms(2) comp_associative2 m_def by (typecheck_cfuncs, fastforce)
  also have "... = \<t> \<circ>\<^sub>c id(\<one>)"
    by (typecheck_cfuncs, metis assms(2) m_def terminal_func_unique)
  also have "... = \<t>"
    by (typecheck_cfuncs, simp add: id_right_unit2)
  then show ?thesis
    by (simp add: calculation)
qed

lemma mult_odds_is_odd2:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "is_odd \<circ>\<^sub>c m = \<t>" "is_odd \<circ>\<^sub>c n = \<t>" 
  shows "is_odd \<circ>\<^sub>c (m \<cdot>\<^sub>\<nat> n) = \<t>"
proof - 
  obtain p where m_def: "p \<in>\<^sub>c \<nat>\<^sub>c \<and> m = nth_odd \<circ>\<^sub>c p"
    using assms(1,3) is_odd_exists_nth_odd by blast
  obtain q where n_def: "q \<in>\<^sub>c \<nat>\<^sub>c \<and> n = nth_odd \<circ>\<^sub>c q"
    using assms(2,4) is_odd_exists_nth_odd by blast
  have m_def2: "m = successor \<circ>\<^sub>c ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> p) "
    using m_def nth_odd_is_succ_times_twoB by blast
  then have m_def3: "m = ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> p) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero)"
    using add_respects_succ1 add_respects_zero_on_right m_def m_def2 by (typecheck_cfuncs, auto)
  then have m_def4: "\<exists>j. j \<in>\<^sub>c \<nat>\<^sub>c \<and> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = m"
    using m_def by blast
  
  have n_def2: "n = successor \<circ>\<^sub>c ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> q)"
    using n_def nth_odd_is_succ_times_twoB by blast
  have n_def3: "n= ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> q) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero)"
    using add_respects_succ1 add_respects_zero_on_right n_def n_def2 by (typecheck_cfuncs, auto)
  then have n_def4: "\<exists>k. k \<in>\<^sub>c \<nat>\<^sub>c \<and> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> k) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = n"
    using n_def by blast
  
  have "\<exists>l. l \<in>\<^sub>c \<nat>\<^sub>c \<and> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> l) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = m \<cdot>\<^sub>\<nat> n"
    by (rule mult_odds_is_odd, simp_all add: assms m_def4 n_def4)
  then obtain l where mn_def: "l \<in>\<^sub>c \<nat>\<^sub>c \<and> ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> l) +\<^sub>\<nat> (successor \<circ>\<^sub>c zero) = m \<cdot>\<^sub>\<nat> n"
    by blast
  then have "m \<cdot>\<^sub>\<nat> n = successor \<circ>\<^sub>c ((successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero) \<cdot>\<^sub>\<nat> l)"
    using add_respects_succ1 add_respects_zero_on_right mn_def by (typecheck_cfuncs, auto)
  then have "m \<cdot>\<^sub>\<nat> n = nth_odd \<circ>\<^sub>c l"
    by (simp add: mn_def nth_odd_is_succ_times_twoB)
  then have "is_odd \<circ>\<^sub>c (m \<cdot>\<^sub>\<nat> n) = (is_odd \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c l"
    using comp_associative2 mn_def by (typecheck_cfuncs, auto)
  also have "... = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c l"
    by (simp add: is_odd_nth_odd_true)
  also have "... = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>  \<circ>\<^sub>c l"
    using comp_associative2 mn_def by (typecheck_cfuncs, auto)
  also have "... = \<t> \<circ>\<^sub>c id(\<one>)"
    using id_type mn_def one_unique_element terminal_func_comp terminal_func_type by fastforce
  also have "... = \<t>"
    by (typecheck_cfuncs, simp add: id_right_unit2)
  then show ?thesis
    by (simp add: calculation)
qed


lemma prod_of_consecutive_nats_is_even:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "is_even \<circ>\<^sub>c (n \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c n)) = \<t>"
  by (metis add_odds_is_even2 assms even_or_odd mult_evens_is_even2 mult_odds_is_odd2 mult_respects_succ_right mult_type succ_n_type)       






end