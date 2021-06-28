theory ETCS_Add
  imports ETCS_Axioms
begin

(*Defining addition on N*)

definition add1 :: "cfunc" where
   "add1 = (THE u. u: \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<and>
   triangle_commutes one \<nat>\<^sub>c  (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) zero u ((left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>) \<and>
   square_commutes \<nat>\<^sub>c  (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) u (successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f) successor u)"

lemma add1_property: "(add1: \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<and>
   triangle_commutes one \<nat>\<^sub>c  (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) zero add1 ((left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>) \<and>
   square_commutes \<nat>\<^sub>c  (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) add1 (successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f) successor add1)"
  unfolding add1_def
proof (rule theI')
  have q_type: "((left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>) :  one \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
    by typecheck_cfuncs
  have f_type: "(successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f) : (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<rightarrow> (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)"
    by (simp add: exp_func_type successor_type)
  show "\<exists>!x. x : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<and>
         triangle_commutes one \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) zero x ((left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>) \<and>
         square_commutes \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) x (successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f)
          successor x"
    using q_type f_type natural_number_object_property by auto
qed

lemma add1_type[type_rule]: "add1:  \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
  by (simp add: add1_property)
 
lemma add1_0_eq: "add1 \<circ>\<^sub>c zero = (left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>"
  using add1_property triangle_commutes_def by blast

lemma add1_comp_succ_eq: "add1 \<circ>\<^sub>c successor = (successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f) \<circ>\<^sub>c add1"
  using add1_property square_commutes_def by auto

definition add2 :: "cfunc"
  where "add2 = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f add1)"

lemma add2_type[type_rule]: "add2:  \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c"
  unfolding add2_def
proof - 
  have "id \<nat>\<^sub>c \<times>\<^sub>f add1 : \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<times>\<^sub>c(\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)"
    by (simp add: add1_property cfunc_cross_prod_type id_type)
  then show "eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add1 : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    using comp_type eval_func_type by blast
qed

lemma add2_apply:
  assumes "m : X \<rightarrow> \<nat>\<^sub>c" "n : X \<rightarrow> \<nat>\<^sub>c"
  shows "add2 \<circ>\<^sub>c \<langle>m, n\<rangle> = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, add1 \<circ>\<^sub>c n\<rangle>"
  unfolding add2_def using assms 
  by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod comp_associative2 id_left_unit2)

definition add :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" (infixl "+\<^sub>\<nat>" 65)
  where "m +\<^sub>\<nat> n = add2\<circ>\<^sub>c\<langle>m, n\<rangle>"

lemma add_type[type_rule]:
  assumes "m : X \<rightarrow> \<nat>\<^sub>c" "n : X \<rightarrow> \<nat>\<^sub>c"
  shows "m +\<^sub>\<nat> n : X \<rightarrow> \<nat>\<^sub>c"
  unfolding add_def using assms by typecheck_cfuncs

lemma add_def2:
  assumes "m\<in>\<^sub>c  \<nat>\<^sub>c" "n\<in>\<^sub>c  \<nat>\<^sub>c"
  shows "m +\<^sub>\<nat> n = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, add1 \<circ>\<^sub>c n\<rangle>"
  unfolding add_def using assms by (typecheck_cfuncs, simp add: add2_apply)

lemma add_respects_zero_on_right:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c"
  shows "m +\<^sub>\<nat> zero = m"
proof -
  have "m +\<^sub>\<nat> zero =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, add1 \<circ>\<^sub>c zero\<rangle>"
    by (simp add: add_def2 assms zero_type)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, (left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> \<rangle>"
    by (simp add: add1_0_eq)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c \<circ>\<^sub>c m, (left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> \<circ>\<^sub>c id one \<rangle>"
    using assms by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c ((id \<nat>\<^sub>c \<times>\<^sub>f  (left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>) \<circ>\<^sub>c  \<langle>m, id one \<rangle>)"
    using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
  also have "... =  (left_cart_proj \<nat>\<^sub>c one) \<circ>\<^sub>c \<langle>m,id one\<rangle>"
    using assms by (typecheck_cfuncs, simp add: comp_associative2 transpose_func_def)
  also have "... = m"
    using assms id_type left_cart_proj_cfunc_prod by blast
  then show "m +\<^sub>\<nat> zero = m"
    by (simp add: calculation)
qed

lemma zero_betaN_type: 
  shows "(zero \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>): X \<rightarrow> \<nat>\<^sub>c"
  using comp_type terminal_func_type zero_type by blast

lemma add_apply1:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n\<in>\<^sub>c \<nat>\<^sub>c"
  shows "m +\<^sub>\<nat> n = add2 \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<circ>\<^sub>c n"
  unfolding add_def using assms cart_prod_extract_right by auto 

lemma add_apply1_left:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n\<in>\<^sub>c \<nat>\<^sub>c"
  shows "m +\<^sub>\<nat> n = add2 \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<circ>\<^sub>c m"
  unfolding add_def using assms cart_prod_extract_left by auto 


(*We make this unusual result its own lemma since it will be used in the commutativity proof*)
lemma id_N_def2:
  shows  "add2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle> = id \<nat>\<^sub>c"
proof (rule natural_number_object_func_unique[where f= successor,  where X= "\<nat>\<^sub>c"])
  show "add2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by (meson add2_type cfunc_prod_type comp_type id_type terminal_func_type zero_type)
  show "id\<^sub>c \<nat>\<^sub>c : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by (simp add: id_type)
  show "successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by (simp add: successor_type)
  show "(add2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero = id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
  proof - 
    have "(add2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero = 
           add2 \<circ>\<^sub>c \<langle>(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>)\<circ>\<^sub>c zero,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero\<rangle>"
      by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2)
    also have "... =add2 \<circ>\<^sub>c \<langle>zero,zero \<rangle>"
      by (typecheck_cfuncs, simp add: cart_prod_extract_right cfunc_prod_comp)
    also have "... = zero"
      using add_def add_respects_zero_on_right zero_type by auto
    also have "... = id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
      by (metis cfunc_type_def id_left_unit zero_type)
    then show ?thesis  using calculation by auto
  qed
  show "(add2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor =
      successor \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
  proof - 
    have "(add2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor =
         add2 \<circ>\<^sub>c (\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c successor) "
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... =  add2 \<circ>\<^sub>c \<langle>(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor\<rangle>"
      by (typecheck_cfuncs, simp add: cfunc_prod_comp)
    also have "... =  add2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> ,  successor\<rangle>"
      by (typecheck_cfuncs, smt comp_associative2 id_left_unit2 terminal_func_comp)
    also have "... = (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add1) \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>"
      unfolding add2_def
      by auto
    also have "... =  eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,  add1 \<circ>\<^sub>c successor\<rangle>"
      using add2_apply add2_def by (typecheck_cfuncs, auto)
    also have "... =  eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,  successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c add1\<rangle>"
      by (simp add: add1_comp_succ_eq)
    also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  (id \<nat>\<^sub>c \<times>\<^sub>f successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f)\<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, add1\<rangle>"
      by (smt \<open>id\<^sub>c \<nat>\<^sub>c : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<close> add1_property cfunc_cross_prod_comp_cfunc_prod cfunc_type_def id_left_unit square_commutes_def zero_betaN_type)
    also have "... = (successor  \<circ>\<^sub>c  eval_func \<nat>\<^sub>c \<nat>\<^sub>c ) \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, add1\<rangle>"
      by (typecheck_cfuncs, smt comp_associative2 exp_func_def2 flat_cancels_sharp inv_transpose_func_def2)
    also have "... = successor \<circ>\<^sub>c eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add1) \<circ>\<^sub>c \<langle>zero\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>"
      by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod comp_associative2 id_left_unit2 id_right_unit2)
    also have "... = successor \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
      by (typecheck_cfuncs, simp add: add2_def comp_associative2)
    then show ?thesis using calculation by auto
  qed
  show " id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor = successor \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c"
    by (metis cfunc_type_def id_left_unit id_right_unit successor_type)
qed

lemma add2_respects_zero_on_left:
  assumes "f : X \<rightarrow> \<nat>\<^sub>c"
  shows "add2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>, f\<rangle> = f"
proof -
  have "add2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>, f\<rangle> = add2 \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c f"
    using assms by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 id_left_unit2 terminal_func_comp)
  also have "... = id \<nat>\<^sub>c \<circ>\<^sub>c f"
    using assms by (typecheck_cfuncs, simp add: comp_associative2 id_N_def2)
  also have "... = f"
    using assms id_left_unit2 by auto
  then show ?thesis
    using calculation by auto
qed

lemma add_respects_zero_on_left:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c"
  shows "zero +\<^sub>\<nat> m = m"
  using assms
  by (typecheck_cfuncs, unfold add_apply1, typecheck_cfuncs, simp add: comp_associative2 id_N_def2 id_left_unit2)

lemma add2_respects_succ_right:
  assumes "m : X \<rightarrow> \<nat>\<^sub>c" "n : X \<rightarrow> \<nat>\<^sub>c" 
  shows "add2 \<circ>\<^sub>c \<langle>m, successor  \<circ>\<^sub>c n\<rangle>  = successor \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>m, n\<rangle>"
proof -
  have fact1: "add1 \<circ>\<^sub>c n : X \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
    using add1_type assms(2) comp_type by blast
  have "add2 \<circ>\<^sub>c \<langle>m, successor  \<circ>\<^sub>c n\<rangle> =  eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, add1 \<circ>\<^sub>c (successor \<circ>\<^sub>c n)\<rangle>"
    using assms add2_apply by (typecheck_cfuncs, blast)
  also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c add1 \<circ>\<^sub>c n\<rangle>"
    using assms by (typecheck_cfuncs, simp add: add1_comp_succ_eq comp_associative2)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m, successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c add1 \<circ>\<^sub>c n\<rangle>"
    by (metis assms(1) cfunc_type_def id_left_unit)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c ((id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f) \<circ>\<^sub>c \<langle>m,add1 \<circ>\<^sub>c n\<rangle>)"
    using  cfunc_cross_prod_comp_cfunc_prod
    by (smt add1_property assms(1) fact1 id_type square_commutes_def)
  also have "... = successor \<circ>\<^sub>c (eval_func  \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>m,add1 \<circ>\<^sub>c n\<rangle>)"
    using assms successor_type
    by (unfold exp_func_def2, typecheck_cfuncs, simp add: comp_associative2 transpose_func_def)
  also have "... = successor \<circ>\<^sub>c (add2 \<circ>\<^sub>c \<langle>m,n\<rangle>)"
    using add2_apply assms by auto
  then show ?thesis 
    using calculation by auto
qed

lemma add2_commutes_succ:
  assumes "m : X \<rightarrow> \<nat>\<^sub>c" "n : X \<rightarrow> \<nat>\<^sub>c" 
  shows "add2 \<circ>\<^sub>c \<langle>successor  \<circ>\<^sub>c m,  n\<rangle>  =  add2 \<circ>\<^sub>c \<langle>m, successor  \<circ>\<^sub>c n\<rangle>"
proof - 
  have "eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ((add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor))\<^sup>\<sharp> \<circ>\<^sub>c zero)) = 
    eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor))\<^sup>\<sharp>)\<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero)"
    using identity_distributes_across_composition by (typecheck_cfuncs, auto)
  also have "... = add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero)"
    by (typecheck_cfuncs, simp add: cfunc_type_def comp_associative transpose_func_def)
  also have "... = add2  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor \<circ>\<^sub>c zero))"
    using identity_distributes_across_composition successor_type zero_type by auto
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add1) \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  (successor \<circ>\<^sub>c zero))"
    by (typecheck_cfuncs, simp add: add2_def comp_associative2)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add1 \<circ>\<^sub>c (successor \<circ>\<^sub>c zero)))"
    by (metis add1_property comp_type identity_distributes_across_composition successor_type zero_type)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c (add1\<circ>\<^sub>c zero)))"
    by (typecheck_cfuncs, simp add: add1_comp_succ_eq comp_associative2)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c  (left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>))"
    by (simp add: add1_0_eq)
  also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f)  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>)"
    using add1_property identity_distributes_across_composition square_commutes_def triangle_commutes_def by auto
  also have "... = (successor \<circ>\<^sub>c eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>)"
    by (typecheck_cfuncs, smt comp_associative2 exp_func_def2 flat_cancels_sharp inv_transpose_func_def2)
  also have "... = successor \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one)"
    by (typecheck_cfuncs, metis cfunc_type_def comp_associative transpose_func_def)
  then have fact2: " eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ((add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor))\<^sup>\<sharp> \<circ>\<^sub>c zero)) = 
   successor \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one)"
    using calculation by auto
  have fact3: "eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one))\<^sup>\<sharp>) = successor \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one)"
    by (typecheck_cfuncs, simp add: transpose_func_def)  
  then have fact4: "(successor \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one))\<^sup>\<sharp> = (add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor))\<^sup>\<sharp> \<circ>\<^sub>c zero"
    by (typecheck_cfuncs, simp add: fact2 fact3 same_evals_equal) 
  have fact5: "eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f((add2 \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>\<circ>\<^sub>c zero)) =
              successor \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one)" (*page 13 big aligned equation*)
  proof -
    have "eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f((add2 \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>\<circ>\<^sub>c zero))
     = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f((add2 \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>fzero)"
      by (typecheck_cfuncs, simp add: identity_distributes_across_composition)
    also have "... = (add2 \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>fzero)"
      by (typecheck_cfuncs, simp add: comp_associative2 transpose_func_def)
    also have "... =  add2 \<circ>\<^sub>c (successor \<times>\<^sub>f zero)"
      by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_cross_prod comp_associative2 id_left_unit2 id_right_unit2)
    also have "... = add2 \<circ>\<^sub>c ((id\<^sub>c \<nat>\<^sub>c\<circ>\<^sub>c successor)  \<times>\<^sub>f (zero \<circ>\<^sub>c id\<^sub>c one))"
      using id_left_unit2 id_right_unit2 successor_type zero_type by auto
    also have "... =  add2 \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>fzero)  \<circ>\<^sub>c(successor \<times>\<^sub>f id\<^sub>c one)"
      by (smt cfunc_cross_prod_comp_cfunc_cross_prod id_type successor_type zero_type)
    also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add1) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>fzero) \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c one)"
      by (typecheck_cfuncs, smt add2_def comp_associative2)
    also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>) \<circ>\<^sub>c  (successor \<times>\<^sub>f id\<^sub>c one)"
      by (typecheck_cfuncs, simp add: add1_0_eq cfunc_cross_prod_comp_cfunc_cross_prod id_left_unit2 id_right_unit2)
    also have "... = (left_cart_proj \<nat>\<^sub>c one)  \<circ>\<^sub>c  (successor \<times>\<^sub>f id\<^sub>c one)"
      by (typecheck_cfuncs, simp add: comp_associative2 transpose_func_def)
    also have "... = successor \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one)"
      by (simp add: id_type left_cart_proj_cfunc_cross_prod successor_type)
    then show ?thesis using calculation by auto
  qed

  have fact6: "successor \<circ>\<^sub>c add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor))
              = add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor)) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor))"
  proof - 
    have "successor \<circ>\<^sub>c add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor)) = 
        (successor \<circ>\<^sub>c  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add1))  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor))"
      by (typecheck_cfuncs, simp add: add2_def comp_associative2)
    also have "... = (eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ( successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f))) \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add1))  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor))"
      unfolding exp_func_def using exponential_square_diagram square_commutes_def successor_type cfunc_type_def comp_type transpose_func_def by auto 
    also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ( successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c add1)) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor))"
      by (typecheck_cfuncs, smt comp_associative2 inv_transpose_func_def2 inv_transpose_of_composition)
    also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (  add1 \<circ>\<^sub>c successor)) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor))"
      by (simp add: add1_comp_succ_eq)
    also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f   add1)\<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  successor) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  successor)"
      by (typecheck_cfuncs, simp add: comp_associative2 identity_distributes_across_composition)
    also have "... =  add2 \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  successor) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  successor)"
      unfolding add2_def using comp_associative2 by (typecheck_cfuncs, fastforce)
    then show ?thesis using calculation by auto
  qed
  have fact6b: "successor \<circ>\<^sub>c add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor))
    = (( add2 \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor)))\<^sup>\<sharp> \<circ>\<^sub>c successor)\<^sup>\<flat>"
    by (typecheck_cfuncs, smt comp_associative2 fact6 inv_transpose_func_def2 inv_transpose_of_composition transpose_func_def)

  have fact6c: "(add2 \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor)))\<^sup>\<sharp> \<circ>\<^sub>c successor
    = successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f  \<circ>\<^sub>c (add2  \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor)))\<^sup>\<sharp>"
  proof -
    have "(add2 \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor)))\<^sup>\<sharp> \<circ>\<^sub>c successor
      = (successor \<circ>\<^sub>c add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor)))\<^sup>\<sharp>"
      by (typecheck_cfuncs, simp add: fact6b sharp_cancels_flat)
    also have "... = successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f  \<circ>\<^sub>c (add2  \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor)))\<^sup>\<sharp>"
      using transpose_of_comp by (typecheck_cfuncs, blast)
    then show ?thesis using calculation by auto
  qed

  have fact6d: "(successor \<circ>\<^sub>c add2 \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))
              = add2 \<circ>\<^sub>c (successor \<times>\<^sub>f successor)"
  proof - 
    have "(successor \<circ>\<^sub>c add2 \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))
              = successor  \<circ>\<^sub>c eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add1)) \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)"
      by (typecheck_cfuncs, simp add: add2_def comp_associative2)
    also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add1)) \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)"
    proof -
      have "eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor \<circ>\<^sub>c eval_func \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> = successor \<circ>\<^sub>c eval_func \<nat>\<^sub>c \<nat>\<^sub>c"
        using transpose_func_def by (typecheck_cfuncs, blast)
      then show ?thesis
       by (typecheck_cfuncs, metis  cfunc_type_def comp_associative exp_func_def2)
    qed
    also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  (successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c add1)) \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)"
      by (typecheck_cfuncs, simp add: comp_associative2 identity_distributes_across_composition)
    also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  ( add1 \<circ>\<^sub>c successor)) \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)"
      by (simp add: add1_comp_succ_eq)
    also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add1) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)"
      by (typecheck_cfuncs, simp add: comp_associative2 identity_distributes_across_composition)
    also have "... = add2 \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)"
      using add2_def comp_associative2 by (typecheck_cfuncs, fastforce)
    also have "... = add2 \<circ>\<^sub>c (successor \<times>\<^sub>f successor)"
    proof -
      have "successor \<times>\<^sub>f successor = (id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<times>\<^sub>f (successor \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c)"
        by (metis (no_types) cfunc_type_def id_left_unit id_right_unit successor_type)
      then show ?thesis
        by (metis (no_types) cfunc_cross_prod_comp_cfunc_cross_prod id_type successor_type)
    qed
    then show ?thesis using calculation by auto
  qed

  have fact6d: "(successor \<circ>\<^sub>c add2 \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) = 
               ((add2 \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c successor)\<^sup>\<flat>"
  proof - 
    have "(successor \<circ>\<^sub>c add2 \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) =  
        add2 \<circ>\<^sub>c (successor \<times>\<^sub>f successor)"
      by (simp add: fact6d)
    also have "... = (add2 \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor))"
      by (smt cfunc_cross_prod_comp_cfunc_cross_prod id_left_unit2 id_right_unit2 id_type successor_type)
    also have "... = ((add2 \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c successor)\<^sup>\<flat>"
      by (typecheck_cfuncs, smt comp_associative2 inv_transpose_func_def2 inv_transpose_of_composition transpose_func_def)
    then show ?thesis using calculation by auto
  qed


  have fact6e: "(add2 \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c successor = 
                successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c (add2 \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>" 
  proof - 
    have "(add2 \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c successor = 
          (successor  \<circ>\<^sub>c add2 \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>"
      by (typecheck_cfuncs, simp add: fact6d sharp_cancels_flat)
    also have "... = successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c (add2 \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>"
      using transpose_of_comp by (typecheck_cfuncs, blast)
    then show ?thesis using calculation by auto
  qed
  
  have fact8: " (add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  (successor)))\<^sup>\<sharp> = 
                (add2 \<circ>\<^sub>c ((successor) \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c ))\<^sup>\<sharp>" 
  proof (rule natural_number_object_func_unique[where f= "successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f",  where X= "\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"])
    show sg1: "(add2 \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
      by typecheck_cfuncs
    show sg2: "(add2 \<circ>\<^sub>c successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
      by typecheck_cfuncs
    show sg3: "successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f : \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
      by typecheck_cfuncs
    show sg4: " (add2 \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor)\<^sup>\<sharp> \<circ>\<^sub>c zero =
              (add2 \<circ>\<^sub>c successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: fact2 fact5 same_evals_equal)
    show sg5: "(add2 \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor)\<^sup>\<sharp> \<circ>\<^sub>c successor =
               successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c (add2 \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor)\<^sup>\<sharp>"
      by (simp add: fact6c)
    show sg6: "(add2 \<circ>\<^sub>c successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor =
                 successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c (add2 \<circ>\<^sub>c successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
      by (simp add: fact6e)
  qed
    
  have fact9: "(add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  (successor))) = 
                (add2 \<circ>\<^sub>c ((successor) \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c ))"
    by (typecheck_cfuncs, metis fact8 flat_cancels_sharp)
  show "add2 \<circ>\<^sub>c \<langle>successor  \<circ>\<^sub>c m,  n\<rangle>  =  add2 \<circ>\<^sub>c \<langle>m, successor  \<circ>\<^sub>c n\<rangle>"
  proof - 
    have "add2 \<circ>\<^sub>c \<langle>successor  \<circ>\<^sub>c m,  n\<rangle>  = add2 \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c ) \<circ>\<^sub>c  \<langle>m,n\<rangle>"
      by (smt assms cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_type successor_type)
    also have "... = add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  (successor)) \<circ>\<^sub>c  \<langle>m,n\<rangle>"
      using assms by (typecheck_cfuncs, simp add: comp_associative2 fact9)
    also have "... = add2 \<circ>\<^sub>c \<langle>m, successor  \<circ>\<^sub>c n\<rangle>"
      using assms cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_type successor_type by fastforce
    then show ?thesis
      using calculation by auto
  qed
qed

lemma add_respects_succ1:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c" 
  shows "m +\<^sub>\<nat> (successor  \<circ>\<^sub>c n)  =  successor\<circ>\<^sub>c (m +\<^sub>\<nat> n)"
  using add_def add2_respects_succ_right assms by auto


lemma add_respects_succ2:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c" 
  shows "m +\<^sub>\<nat> (successor  \<circ>\<^sub>c n)  =  (successor\<circ>\<^sub>c m) +\<^sub>\<nat> n"
  using add_def add2_commutes_succ assms(1) assms(2) by presburger

lemma succ_n_type: 
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "successor \<circ>\<^sub>c n \<in>\<^sub>c \<nat>\<^sub>c"
  using assms comp_type successor_type by blast

lemma add_respects_succ3: 
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c" 
  shows "(successor\<circ>\<^sub>c m) +\<^sub>\<nat> n = successor\<circ>\<^sub>c (m +\<^sub>\<nat> n)"
  using add_respects_succ1 add_respects_succ2 assms(1) assms(2) by auto

lemma add_pi1_pi0_1xsEqs_s_add_pi1_pi_0:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "add2 \<circ>\<^sub>c \<langle> right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c ,  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<rangle>
     \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor)\<circ>\<^sub>c \<langle>m,n\<rangle> = 
      successor \<circ>\<^sub>c add2 \<circ>\<^sub>c  \<langle> right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c ,  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<rangle>\<circ>\<^sub>c \<langle>m,n\<rangle>"
proof - 
  have "add2 \<circ>\<^sub>c \<langle> right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c ,  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<rangle>
        \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor)\<circ>\<^sub>c \<langle>m,n\<rangle> = 
        add2 \<circ>\<^sub>c \<langle> right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c ,  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<rangle>
     \<circ>\<^sub>c \<langle>m,successor \<circ>\<^sub>c n\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
  also have "... = add2 \<circ>\<^sub>c \<langle> right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m,successor \<circ>\<^sub>c n\<rangle> ,  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m,successor \<circ>\<^sub>c n\<rangle> \<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp)
  also have "... = add2 \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c n , m\<rangle>"
    using assms by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  also have "... = (successor \<circ>\<^sub>c n)  +\<^sub>\<nat> m"
    by (simp add: add_def)
  also have "... = successor  \<circ>\<^sub>c (n  +\<^sub>\<nat> m)"
    using add_respects_succ1 add_respects_succ2 assms by auto
  also have "... = successor \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>n , m\<rangle>"
    by (simp add: add_def)
  also have "... = successor \<circ>\<^sub>c add2 \<circ>\<^sub>c
                 \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m , n\<rangle> , 
                  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m , n\<rangle>\<rangle>"
    using assms(1) assms(2) left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod by auto
  also have "... = successor \<circ>\<^sub>c add2 \<circ>\<^sub>c  \<langle> right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c ,  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<rangle>\<circ>\<^sub>c \<langle>m,n\<rangle>"
    using swap_def assms left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod swap_ap by auto
  then show ?thesis using calculation by auto
qed

lemma pointfree_add_pi1_pi0_1xsEqs_s_add_pi1_pi_0:
  shows "add2 \<circ>\<^sub>c \<langle> right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c ,  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor)
    = successor \<circ>\<^sub>c add2 \<circ>\<^sub>c  \<langle> right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c ,  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<rangle>"
proof (rule one_separator[where X="\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c", where Y="\<nat>\<^sub>c"])
  have cross_type: "id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
    by (simp add: cfunc_cross_prod_type id_type successor_type)
  show "add2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor
          : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    using add2_type comp_type cross_type swap_type unfolding swap_def by blast
  show "successor \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>
          : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    using add2_type comp_type successor_type swap_type unfolding swap_def by blast
next
  fix x
  assume x_type: "x \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
  then show "(add2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c x
    = (successor \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c x"
    by (typecheck_cfuncs, smt add_pi1_pi0_1xsEqs_s_add_pi1_pi_0 cart_prod_decomp comp_associative2)
qed

lemma add_commutes:
  assumes "m : A \<rightarrow> \<nat>\<^sub>c" "n : A \<rightarrow> \<nat>\<^sub>c" 
  shows "m +\<^sub>\<nat> n  = n +\<^sub>\<nat> m"
proof - 
  have "eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ((add2  \<circ>\<^sub>c 
    \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c),(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero)) = 
    left_cart_proj \<nat>\<^sub>c one"
  proof-
    have "eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ((add2  \<circ>\<^sub>c
    \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c),(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero)) = 
    eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add2 \<circ>\<^sub>c
    \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c),(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>)  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero)"
      by (typecheck_cfuncs, simp add: identity_distributes_across_composition)
    also have "... = add2 \<circ>\<^sub>c
   \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c),(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero)"
      by (typecheck_cfuncs, simp add: cfunc_type_def comp_associative transpose_func_def)
    also have "... = add2 \<circ>\<^sub>c
   \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c),(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c
   \<langle>(left_cart_proj \<nat>\<^sub>c one),zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c one)\<rangle>"
      by (metis cfunc_cross_prod_def cfunc_type_def id_domain id_left_unit left_cart_proj_type zero_type)
    also have "... = add2 \<circ>\<^sub>c
   \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c one),zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c one)\<rangle>,
    (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c one),zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c one)\<rangle>
   \<rangle>"
      by (typecheck_cfuncs, simp add: cfunc_prod_comp)
    also have "... = add2 \<circ>\<^sub>c
\<langle>zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c one), (left_cart_proj \<nat>\<^sub>c one)\<rangle>"
      by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
    also have "... =  add2 \<circ>\<^sub>c
\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c(left_cart_proj \<nat>\<^sub>c one), (left_cart_proj \<nat>\<^sub>c one)\<rangle>"
      by (typecheck_cfuncs, metis terminal_func_unique)
    also have "... =  add2 \<circ>\<^sub>c
\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c(left_cart_proj \<nat>\<^sub>c one), id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one)\<rangle>"
      by (typecheck_cfuncs, simp add: id_left_unit2)
    also have "... =  add2 \<circ>\<^sub>c
\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one) "
      by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
    also have "... = id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one)"
      by (typecheck_cfuncs, simp add: comp_associative2 id_N_def2)
    also have "... = left_cart_proj \<nat>\<^sub>c one"
    by (metis cfunc_type_def id_left_unit left_cart_proj_type)
   then show ?thesis using calculation by auto
    qed
  
    then have fact0: "((add2  \<circ>\<^sub>c
    \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c),(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero)
   = (left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>"
      by (typecheck_cfuncs, simp add: transpose_func_unique)

  have fact1: "((add2 \<circ>\<^sub>c 
        \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c), (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
        successor)\<^sup>\<flat> = 
        successor \<circ>\<^sub>c 
        add2 \<circ>\<^sub>c 
        \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c), (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle>"
  proof - 
     have "((add2 \<circ>\<^sub>c 
        \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c), (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
        successor)\<^sup>\<flat> = 
    (add2 \<circ>\<^sub>c \<langle> right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c ,  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<rangle>)\<^sup>\<sharp>\<^sup>\<flat>
     \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor)"
       using inv_transpose_of_composition by (typecheck_cfuncs, blast)
    also have "... =  (add2 \<circ>\<^sub>c \<langle> right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c ,  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<rangle>)
     \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor)"
      by (typecheck_cfuncs, simp add: flat_cancels_sharp)
    also have "... =  successor \<circ>\<^sub>c 
        add2 \<circ>\<^sub>c 
        \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c), (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>"
      using comp_associative2 pointfree_add_pi1_pi0_1xsEqs_s_add_pi1_pi_0 by (typecheck_cfuncs, auto)
    then show ?thesis
      using calculation by auto
 qed

  have fact2: "((add2 \<circ>\<^sub>c 
        \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c), (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
        successor) = 
        successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c 
        (add2 \<circ>\<^sub>c 
        \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c), (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>"
    by (typecheck_cfuncs, metis fact1 sharp_cancels_flat transpose_of_comp)

  have add1_def2: "(add2 \<circ>\<^sub>c 
        \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c), (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp> = add1"
    using add1_0_eq add1_property fact0 fact2 natural_number_object_func_unique square_commutes_def
    by (typecheck_cfuncs, auto)

  show "m +\<^sub>\<nat> n  = n +\<^sub>\<nat> m"
  proof - 
    have "m +\<^sub>\<nat> n = add2 \<circ>\<^sub>c \<langle>m,n\<rangle>"
      by (simp add: add_def)
    also have step1: "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add1)\<circ>\<^sub>c \<langle>m,n\<rangle>"
      using assms by (typecheck_cfuncs, simp add: add2_def comp_associative2)
    also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add2 \<circ>\<^sub>c 
        \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c), (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>)\<circ>\<^sub>c \<langle>m,n\<rangle>"
      by (simp add: add1_def2)
    also have "... =  (add2 \<circ>\<^sub>c 
        \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c), (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>) \<circ>\<^sub>c \<langle>m,n\<rangle>"
      using assms add1_def2 add2_def transpose_func_def step1 by (typecheck_cfuncs, fastforce)
    also have "... = (add2 \<circ>\<^sub>c 
        \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>m,n\<rangle>, (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>m,n\<rangle> \<rangle>) "
      using assms by (typecheck_cfuncs, metis cfunc_prod_comp comp_associative2)
    also have "... = add2 \<circ>\<^sub>c \<langle>n,m\<rangle>"
      using assms(1) assms(2) left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod by auto
    also have "...= n +\<^sub>\<nat> m"
      by (simp add: add_def)
 then show ?thesis using calculation by auto
qed
qed

lemma add_associates:
  assumes "a \<in>\<^sub>c \<nat>\<^sub>c" "b \<in>\<^sub>c \<nat>\<^sub>c" "c \<in>\<^sub>c \<nat>\<^sub>c" 
  shows   "a +\<^sub>\<nat> (b +\<^sub>\<nat> c) = (a +\<^sub>\<nat> b ) +\<^sub>\<nat> c"
proof - 

  have triangle: "(add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero = 
    (add2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero"
    (is "?lhs = ?rhs")
  proof (rule same_evals_equal[where X="\<nat>\<^sub>c", where A="\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c", where Z="one"]) 
    show lhs_type: "?lhs : one \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
      by typecheck_cfuncs
    show rhs_type: "?rhs : one \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
      by typecheck_cfuncs
    
    have lhs_eval: "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f ?lhs)
      = (add2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) one)"
    (is "?lhs1 = ?rhs1")
    proof (rule one_separator[where X="(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c one", where Y="\<nat>\<^sub>c"])
      show LHS_type: "?lhs1 : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one \<rightarrow> \<nat>\<^sub>c"
        by typecheck_cfuncs
      show RHS_type: "?rhs1 : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one \<rightarrow> \<nat>\<^sub>c"
        by typecheck_cfuncs
    next
      fix x
      assume "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one"
      then obtain a b where "x = \<langle>\<langle>a,b\<rangle>, id one\<rangle>" and a_type: "a \<in>\<^sub>c \<nat>\<^sub>c" and b_type: "b \<in>\<^sub>c \<nat>\<^sub>c"
        by (metis cart_prod_decomp id_type terminal_func_unique)
      then show "?lhs1 \<circ>\<^sub>c x = ?rhs1 \<circ>\<^sub>c x"
      proof auto
        have "(eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c 
            (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
              (add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero)) \<circ>\<^sub>c
            \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>
          = eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c
            (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
              (add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c
            (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>"
          using a_type b_type by (typecheck_cfuncs, smt comp_associative2 inv_transpose_func_def2 inv_transpose_of_composition transpose_func_def)
        also have "... = (add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c
          ((id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>)"
          using a_type b_type by (typecheck_cfuncs, smt comp_associative2 transpose_func_def)
        also have "... = (add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, zero\<rangle>"
          using a_type b_type by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2)
        also have "... = add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c (associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, zero\<rangle>)"
          using a_type b_type by (typecheck_cfuncs, simp add: cfunc_type_def comp_associative)
          also have "... = (add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2)) \<circ>\<^sub>c \<langle>a, \<langle>b, zero\<rangle>\<rangle>"
          using a_type b_type by (typecheck_cfuncs, simp add: associate_right_ap comp_associative2)
        also have "... = add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c \<langle>a, \<langle>b, zero\<rangle>\<rangle>"
          using a_type b_type by (typecheck_cfuncs, simp add: comp_associative2)
        also have "... = add2 \<circ>\<^sub>c \<langle>a, add2 \<circ>\<^sub>c \<langle>b, zero\<rangle>\<rangle>"
          using a_type b_type by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
        also have "... = add2 \<circ>\<^sub>c \<langle>a, b\<rangle>"
          using add_def add_respects_zero_on_right b_type by auto
        also have "... = add2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) one \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>"
          using a_type b_type by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod)
        also have "... = (add2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) one) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>"
          using a_type b_type by (typecheck_cfuncs, simp add: comp_associative2)
        then show "?lhs1 \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, id\<^sub>c one\<rangle> = ?rhs1 \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, id\<^sub>c one\<rangle>"
          using calculation by auto
      qed
    qed

    have rhs_eval: "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f ?rhs) 
      = (add2 \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) one)"
    (is "?lhs1 = ?rhs1")
    proof (rule one_separator[where X="(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c one", where Y="\<nat>\<^sub>c"])
      show LHS_type: "?lhs1 : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one \<rightarrow> \<nat>\<^sub>c"
        by typecheck_cfuncs
      show RHS_type: "?rhs1 : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one \<rightarrow> \<nat>\<^sub>c"
        by typecheck_cfuncs
    next
      fix x
      assume "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one"
      then obtain a b where "x = \<langle>\<langle>a,b\<rangle>, id one\<rangle>" and a_type: "a \<in>\<^sub>c \<nat>\<^sub>c" and b_type: "b \<in>\<^sub>c \<nat>\<^sub>c"
        by (metis cart_prod_decomp id_type terminal_func_unique)
      then show "?lhs1 \<circ>\<^sub>c x = ?rhs1 \<circ>\<^sub>c x"
      proof auto
        have "?lhs1  \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>  =  
          eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c
          (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c
          \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>"
          using a_type b_type by (typecheck_cfuncs, simp add: comp_associative2)
        also have "... =  
          eval_func  \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<circ>\<^sub>c 
            ((id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f  id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>) \<circ>\<^sub>c
              (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f zero)) \<circ>\<^sub>c
              \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>"
          using a_type b_type by (typecheck_cfuncs, simp add: identity_distributes_across_composition)
        also have "... = add2 \<circ>\<^sub>c ((add2 \<times>\<^sub>f  id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,zero\<rangle>)"
          using a_type b_type
          by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod comp_associative2 flat_cancels_sharp id_left_unit2 id_right_unit2 inv_transpose_func_def2)
        also have "... = add2 \<circ>\<^sub>c \<langle> add2 \<circ>\<^sub>c \<langle>a,b\<rangle>,zero\<rangle>"
          using a_type b_type by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
        also have "... = add2 \<circ>\<^sub>c \<langle>a,b\<rangle>"
          using a_type b_type add_def add_respects_zero_on_right by (typecheck_cfuncs, auto)
        also have "... = ?rhs1 \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>"
          using a_type b_type by (typecheck_cfuncs, smt comp_associative2 left_cart_proj_cfunc_prod)
        then show "?lhs1 \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle> = ?rhs1 \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>"
          using calculation by auto
      qed
    qed

    show "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f ?lhs)
        = eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f ?rhs)"
      by (simp add: lhs_eval rhs_eval)
  qed

  thm associate_right_def

  have square1: "(add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor 
      = successor\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>\<^sub>f \<circ>\<^sub>c (add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
  proof -
    have "add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor)  =
        successor \<circ>\<^sub>c add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c"
    proof (typecheck_cfuncs, rule_tac one_separator[where X="(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c", where Y="\<nat>\<^sub>c"], simp_all)
      fix x
      assume "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c"
      then obtain a b c where element_types: "a \<in>\<^sub>c \<nat>\<^sub>c" "b \<in>\<^sub>c \<nat>\<^sub>c" "c \<in>\<^sub>c \<nat>\<^sub>c" and x_def: "x = \<langle>\<langle>a,b\<rangle>,c\<rangle>"
        using cart_prod_decomp by blast
      then show  "(add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor)) \<circ>\<^sub>c x
          = (successor \<circ>\<^sub>c add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c x"
      proof auto
        have "add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle> = 
          add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, successor \<circ>\<^sub>c c\<rangle>"
          using element_types by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
        also have "... = add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c \<langle>a,\<langle>b,successor \<circ>\<^sub>c c\<rangle> \<rangle>"
          using element_types by (typecheck_cfuncs, simp add: associate_right_ap)
        also have "... = add2 \<circ>\<^sub>c \<langle>a, add2 \<circ>\<^sub>c \<langle>b,successor \<circ>\<^sub>c c\<rangle> \<rangle>"
          using element_types by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
        also have "... = a +\<^sub>\<nat> (b +\<^sub>\<nat> (successor \<circ>\<^sub>c c))"
          unfolding add_def by auto
        also have "... = a +\<^sub>\<nat> (successor \<circ>\<^sub>c (b +\<^sub>\<nat> c))"
          by (simp add: add_respects_succ1 element_types)
        also have "... = successor \<circ>\<^sub>c (a +\<^sub>\<nat> (b +\<^sub>\<nat> c))"
          by (simp add: add_respects_succ1 add_type element_types)
        also have "... = successor \<circ>\<^sub>c add2  \<circ>\<^sub>c \<langle>a,add2 \<circ>\<^sub>c \<langle>b,c\<rangle>\<rangle>"
          by (simp add: add_def)
        also have "... = successor \<circ>\<^sub>c add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c \<langle>a,\<langle>b,c\<rangle>\<rangle>"
          using element_types by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
        also have "... = successor \<circ>\<^sub>c add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
          using element_types associate_right_ap by auto
        then show "(add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>
            = (successor \<circ>\<^sub>c add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
          using calculation element_types by (typecheck_cfuncs, auto simp add: comp_associative2)
      qed
    qed
    then have "((add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>)\<^sup>\<flat>  \<circ>\<^sub>c (id\<^sub>c(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor)
        = successor \<circ>\<^sub>c (add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)"
      using cfunc_type_def comp_associative flat_cancels_sharp by (typecheck_cfuncs, auto)
    then have "((add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor)\<^sup>\<flat>
          = successor \<circ>\<^sub>c (add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)"
        by (typecheck_cfuncs, simp add: inv_transpose_of_composition)
    (*And by taking sharps of both sides we arrive at*)
    then show "(add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor
        = successor\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>\<^sub>f \<circ>\<^sub>c (add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
      by (typecheck_cfuncs, metis sharp_cancels_flat transpose_of_comp)
  qed

  have square2: "successor\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>\<^sub>f \<circ>\<^sub>c (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>
      = (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>  \<circ>\<^sub>c successor"
  proof -
    have "add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor)
        = successor \<circ>\<^sub>c add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)"
    proof (typecheck_cfuncs, rule_tac one_separator[where X="(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c", where Y="\<nat>\<^sub>c"], simp_all)
      fix x
      assume "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c"
      then obtain a b c where element_types: "a \<in>\<^sub>c \<nat>\<^sub>c" "b \<in>\<^sub>c \<nat>\<^sub>c" "c \<in>\<^sub>c \<nat>\<^sub>c" and x_def: "x = \<langle>\<langle>a,b\<rangle>,c\<rangle>"
        using cart_prod_decomp by blast
      then show "(add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor) \<circ>\<^sub>c x
          = (successor \<circ>\<^sub>c add2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c x"
      proof auto
        have "add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>
          = add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,successor \<circ>\<^sub>c c\<rangle>"
          using element_types by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
        also have "... = add2 \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>a,b\<rangle>, successor \<circ>\<^sub>c  c\<rangle>"
          using element_types by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
        also have "... = (a +\<^sub>\<nat> b) +\<^sub>\<nat> (successor \<circ>\<^sub>c  c)"
          by (simp add: add_def)
        also have "... = successor \<circ>\<^sub>c ((a +\<^sub>\<nat> b) +\<^sub>\<nat> c)"
          by (simp add: add_respects_succ2 add_respects_succ3 add_type element_types)
        also have "... = successor \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>a,b\<rangle>, c\<rangle>"
          by (simp add: add_def)
        also have "... = successor \<circ>\<^sub>c add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, c\<rangle>"
          using element_types by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
        then show "(add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>
            = (successor \<circ>\<^sub>c add2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
          using element_types calculation cfunc_type_def comp_associative by (typecheck_cfuncs, auto)
      qed
    qed
    then have "((add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)\<^sup>\<flat> \<circ>\<^sub>c id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor
        = successor \<circ>\<^sub>c add2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c"
      using comp_associative2 flat_cancels_sharp by (typecheck_cfuncs, auto)
    then have "((add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c successor)\<^sup>\<flat>
        = successor \<circ>\<^sub>c add2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c"
      by (typecheck_cfuncs, simp add: inv_transpose_of_composition)
    then have "(add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c successor
        = successor\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>\<^sub>f \<circ>\<^sub>c (add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>"
      by (typecheck_cfuncs, metis sharp_cancels_flat transpose_of_comp)
    then show ?thesis
      by auto
  qed

  thm triangle square1 square2
  have "(add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>
      = (add2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
    by (typecheck_cfuncs, metis exp_func_type natural_number_object_func_unique square1 square2 successor_type triangle)
  then have "add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c
      = add2 \<circ>\<^sub>c add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c"
    by (typecheck_cfuncs, metis transpose_func_def)
  then have "add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>
      = add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)  \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
    using assms cfunc_type_def comp_associative comp_type by (typecheck_cfuncs, auto)
  then have "add2 \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add2) \<circ>\<^sub>c \<langle>a,\<langle>b,c\<rangle>\<rangle>
      = add2 \<circ>\<^sub>c (add2 \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)  \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"
    using assms associate_right_ap by auto
  then have "add2 \<circ>\<^sub>c \<langle>a, add2 \<circ>\<^sub>c \<langle>b,c\<rangle>\<rangle>
      = add2 \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>a,b\<rangle>, c\<rangle>"
    using assms by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_type)
  then show "a +\<^sub>\<nat> (b +\<^sub>\<nat> c) = a +\<^sub>\<nat> b +\<^sub>\<nat> c"
    unfolding add_def by auto
qed

lemma add2_cancellative:  
  assumes "a \<in>\<^sub>c \<nat>\<^sub>c" "b \<in>\<^sub>c \<nat>\<^sub>c" 
  shows "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>, add2 \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<rangle>
    = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
proof -
  obtain a_b_add_eq where
    a_b_add_eq_type: "a_b_add_eq : \<nat>\<^sub>c \<rightarrow> \<Omega>" and
    a_b_add_eq_def: "a_b_add_eq = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>, add2 \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<rangle>"
    using assms by typecheck_cfuncs

  have "a_b_add_eq = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
  proof (rule natural_number_object_func_unique[where X=\<Omega>, where f="id \<Omega>"])
    show "a_b_add_eq : \<nat>\<^sub>c \<rightarrow> \<Omega>"
      using a_b_add_eq_type by auto
    show "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
      using assms by typecheck_cfuncs
    show "id\<^sub>c \<Omega> : \<Omega> \<rightarrow> \<Omega>"
      using id_type by auto
  
    show "a_b_add_eq \<circ>\<^sub>c zero = (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c zero"
    proof -
      have "a_b_add_eq \<circ>\<^sub>c zero = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>, add2 \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c zero"
        unfolding a_b_add_eq_def using assms by (typecheck_cfuncs, simp add: comp_associative2)
      also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c zero, zero\<rangle>, add2 \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c zero, zero\<rangle>\<rangle>"
        using assms by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 id_left_unit2)
      also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>a, zero\<rangle>, add2 \<circ>\<^sub>c \<langle>b, zero\<rangle>\<rangle>"
         using assms by (typecheck_cfuncs, metis id_right_unit2 id_type one_unique_element)
      also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a, b\<rangle>"
        using add_def add_respects_zero_on_right assms by auto
      also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c zero, b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c zero\<rangle> "
        using assms by (typecheck_cfuncs, metis  id_right_unit2 id_type terminal_func_unique)
      also have "... = (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c zero"
        using assms by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2)
      then show ?thesis
        using calculation by auto
    qed
  
    show "a_b_add_eq \<circ>\<^sub>c successor = id\<^sub>c \<Omega> \<circ>\<^sub>c a_b_add_eq"
    proof (rule one_separator[where X ="\<nat>\<^sub>c", where Y = "\<Omega>"])
      show "a_b_add_eq \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<Omega>"
        using a_b_add_eq_type comp_type successor_type by auto
      show "id\<^sub>c \<Omega> \<circ>\<^sub>c a_b_add_eq : \<nat>\<^sub>c \<rightarrow> \<Omega>"
        using a_b_add_eq_type comp_type id_type by auto
    next
      fix n
      assume n_type: "n \<in>\<^sub>c \<nat>\<^sub>c"
  
      have true_or_false: "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle> add2 \<circ>\<^sub>c \<langle>a , n\<rangle>,  add2 \<circ>\<^sub>c \<langle>b ,  n\<rangle>\<rangle> \<in>\<^sub>c \<Omega>"
        by (metis add_def add_type assms(1) assms(2) cfunc_prod_type comp_type eq_pred_type n_type)
       
      have "(a_b_add_eq \<circ>\<^sub>c successor) \<circ>\<^sub>c n = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>, add2 \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c successor \<circ>\<^sub>c n"
        using assms n_type unfolding a_b_add_eq_def by (typecheck_cfuncs, smt comp_associative2)
      also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor \<circ>\<^sub>c n, successor \<circ>\<^sub>c n\<rangle>, add2 \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor \<circ>\<^sub>c n,  successor \<circ>\<^sub>c n\<rangle>\<rangle>"
        using assms n_type by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 id_left_unit2)
      also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>a , successor \<circ>\<^sub>c n\<rangle>, add2 \<circ>\<^sub>c \<langle>b,  successor \<circ>\<^sub>c n\<rangle>\<rangle>"
        using assms n_type  by (typecheck_cfuncs, metis id_right_unit2 id_type one_unique_element)
      also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle> successor \<circ>\<^sub>c  add2 \<circ>\<^sub>c \<langle>a , n\<rangle>, successor \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>b , n\<rangle>\<rangle>"
        using assms n_type by (typecheck_cfuncs, metis add2_respects_succ_right)
      also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle> add2 \<circ>\<^sub>c \<langle>a , n\<rangle>,  add2 \<circ>\<^sub>c \<langle>b ,  n\<rangle>\<rangle>"
        (is "?LHS=?RHS")
      proof(cases "?RHS = \<t>")
        assume rhs_true: "?RHS = \<t>"
        then have "add2 \<circ>\<^sub>c \<langle>a , n\<rangle> = add2 \<circ>\<^sub>c \<langle>b , n\<rangle>"
          using assms n_type eq_pred_iff_eq by (typecheck_cfuncs, blast)
        then show "?LHS = ?RHS"
          by (metis  add_def add_type assms(1) eq_pred_iff_eq n_type succ_n_type)
      next
        assume rhs_not_true: "?RHS \<noteq> \<t>"
        have not_equal: "add2 \<circ>\<^sub>c \<langle>a , n\<rangle> \<noteq> add2 \<circ>\<^sub>c \<langle>b , n\<rangle>"
          using assms n_type rhs_not_true eq_pred_iff_eq by (typecheck_cfuncs, blast)
        then have "successor \<circ>\<^sub>c  add2 \<circ>\<^sub>c \<langle>a , n\<rangle> \<noteq> successor \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>b , n\<rangle>"
          using assms n_type  not_equal succ_inject  by (typecheck_cfuncs, blast)          
        then have "?LHS \<noteq>  \<t>"
          using assms n_type  eq_pred_iff_eq  by (typecheck_cfuncs, blast)
        then have lhs_false: "?LHS = \<f>"
          using assms n_type true_false_only_truth_values by (typecheck_cfuncs, fastforce)
        have  rhs_false: "?RHS = \<f>"
          using rhs_not_true true_false_only_truth_values true_or_false by auto
        show "?LHS = ?RHS"
          by (simp add: lhs_false rhs_false)
      qed
      also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle> add2 \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c n,  add2 \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , id \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c n\<rangle>"
        using assms n_type cart_prod_extract_right by (typecheck_cfuncs, auto)
      also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle> add2 \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>,  add2 \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , id \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c n"
        using assms n_type by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2)
      also have "... = a_b_add_eq \<circ>\<^sub>c n"
        using assms n_type by (typecheck_cfuncs, simp add: a_b_add_eq_def comp_associative2)
      also have "... = (id\<^sub>c \<Omega> \<circ>\<^sub>c a_b_add_eq) \<circ>\<^sub>c n"
        using a_b_add_eq_type id_left_unit2 by auto
      then show  "(a_b_add_eq \<circ>\<^sub>c successor) \<circ>\<^sub>c n = (id\<^sub>c \<Omega> \<circ>\<^sub>c a_b_add_eq) \<circ>\<^sub>c n"
        using calculation by auto
    qed
  
    show "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c successor = id\<^sub>c \<Omega> \<circ>\<^sub>c eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
      using assms
      by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 id_left_unit2 terminal_func_comp)
  qed
  then show ?thesis
    unfolding a_b_add_eq_def by auto
qed

lemma add_cancellative:
  assumes "a \<in>\<^sub>c \<nat>\<^sub>c" "b \<in>\<^sub>c \<nat>\<^sub>c" "c \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(a +\<^sub>\<nat> c = b +\<^sub>\<nat> c) = (a = b)"
proof - 
  obtain a_b_add_eq where
    a_b_add_eq_type: "a_b_add_eq : \<nat>\<^sub>c \<rightarrow> \<Omega>" and
    a_b_add_eq_def: "a_b_add_eq = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>, add2 \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<rangle>"
    using assms by typecheck_cfuncs

  have "a_b_add_eq = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
    unfolding a_b_add_eq_def using add2_cancellative assms successor_type by blast 
  then have "a_b_add_eq \<circ>\<^sub>c c = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c c"
    using assms comp_associative2 by (typecheck_cfuncs, auto)
  then have "a_b_add_eq \<circ>\<^sub>c c = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c c, b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c c\<rangle>"
    using assms by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 terminal_func_comp)
  then have "a_b_add_eq \<circ>\<^sub>c c = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a ,b\<rangle>"
    by (metis assms id_right_unit2 id_type one_unique_element terminal_func_comp terminal_func_type)
  then have "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>, add2 \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c c = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a,b\<rangle>"
    unfolding a_b_add_eq_def using assms comp_associative2 by (typecheck_cfuncs, auto)
  then have "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>(add2 \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c c, (add2 \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c c\<rangle> = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a,b\<rangle>"
    using assms cfunc_prod_comp by (typecheck_cfuncs, auto)
  then have "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c c, add2 \<circ>\<^sub>c \<langle>b \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c c\<rangle> = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a,b\<rangle>"
    using assms comp_associative2 by (typecheck_cfuncs, auto)
  then have "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>a, c\<rangle>, add2 \<circ>\<^sub>c \<langle>b, c\<rangle>\<rangle> = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a,b\<rangle>"
    using assms cart_prod_extract_right by auto
  then have "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a +\<^sub>\<nat> c, b +\<^sub>\<nat> c\<rangle> = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>a,b\<rangle>"
    unfolding add_def by auto
  then show "(a +\<^sub>\<nat> c = b +\<^sub>\<nat> c) = (a = b)"
    by (metis add_type assms eq_pred_iff_eq)
qed

end