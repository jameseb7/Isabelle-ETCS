theory ETCS_Add
  imports ETCS_Axioms
begin

(*Defining addition on N*)

definition add_curried :: "cfunc" where
   "add_curried = (THE u. u: \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<and>
   triangle_commutes one \<nat>\<^sub>c  (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) zero u ((left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>) \<and>
   square_commutes \<nat>\<^sub>c  (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) u (successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f) successor u)"

lemma add_curried_property: "(add_curried: \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<and>
   triangle_commutes one \<nat>\<^sub>c  (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) zero add_curried ((left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>) \<and>
   square_commutes \<nat>\<^sub>c  (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) add_curried (successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f) successor add_curried)"
  unfolding add_curried_def
proof (rule theI')
  have q_type: "((left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>) :  one \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
    by (simp add: left_cart_proj_type transpose_func_def)
  have f_type: "(successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f) : (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<rightarrow> (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)"
    by (simp add: exp_func_type successor_type)
  show "\<exists>!x. x : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<and>
         triangle_commutes one \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) zero x ((left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>) \<and>
         square_commutes \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) x (successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f)
          successor x"
    using q_type f_type natural_number_object_property by auto
qed

lemma add_curried_type: "add_curried:  \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
  by (simp add: add_curried_property)
 
lemma add_curried_0_eq: "add_curried \<circ>\<^sub>c zero = (left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>"
  using add_curried_property triangle_commutes_def by blast

lemma add_curried_comp_succ_eq: "add_curried \<circ>\<^sub>c successor = (successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f) \<circ>\<^sub>c add_curried"
  using add_curried_property square_commutes_def by auto

definition add_uncurried :: "cfunc"
  where "add_uncurried = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f add_curried)"

lemma add_uncurried_type: "add_uncurried:  \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c"
  unfolding add_uncurried_def
proof - 
  have "id \<nat>\<^sub>c \<times>\<^sub>f add_curried : \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<times>\<^sub>c(\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)"
    by (simp add: add_curried_property cfunc_cross_prod_type id_type)
  then show "eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_curried : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    using comp_type eval_func_type by blast
qed

lemma add_uncurried_apply:
  assumes "m : X \<rightarrow> \<nat>\<^sub>c" "n : X \<rightarrow> \<nat>\<^sub>c"
  shows "add_uncurried \<circ>\<^sub>c \<langle>m, n\<rangle> = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, add_curried \<circ>\<^sub>c n\<rangle>"
  by (smt add_curried_property add_uncurried_def assms cfunc_cross_prod_comp_cfunc_prod comp_associative id_left_unit2 id_type)


definition add :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" (infixl "+\<^sub>\<nat>" 65)
  where "m +\<^sub>\<nat> n = add_uncurried\<circ>\<^sub>c\<langle>m, n\<rangle>"

lemma add_def2:
  assumes "m\<in>\<^sub>c  \<nat>\<^sub>c" "n\<in>\<^sub>c  \<nat>\<^sub>c"
  shows "m +\<^sub>\<nat> n = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, add_curried \<circ>\<^sub>c n\<rangle>"
  unfolding add_def add_uncurried_def
  by (smt add_curried_type assms cfunc_cross_prod_comp_cfunc_prod cfunc_type_def comp_associative id_left_unit id_type)



lemma add_respects_zero_on_right:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c"
  shows "m +\<^sub>\<nat> zero = m"
proof -
  have projsharp_type: "(left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>: one \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
    by (simp add: left_cart_proj_type transpose_func_def)
  
  have "m +\<^sub>\<nat> zero =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, add_curried \<circ>\<^sub>c zero\<rangle>"
    by (simp add: add_def2 assms zero_type)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, (left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> \<rangle>"
    by (simp add: add_curried_0_eq)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c \<circ>\<^sub>c m, (left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> \<circ>\<^sub>c id one \<rangle>"
    by (metis assms cfunc_type_def id_left_unit id_right_unit projsharp_type)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c ((id \<nat>\<^sub>c \<times>\<^sub>f  (left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>) \<circ>\<^sub>c  \<langle>m, id one \<rangle>)"
    by (smt assms cfunc_cross_prod_comp_cfunc_prod id_type projsharp_type)
  also have "... =  (left_cart_proj \<nat>\<^sub>c one) \<circ>\<^sub>c \<langle>m,id one\<rangle>"
    by (metis comp_associative left_cart_proj_type transpose_func_def)
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
  shows "m +\<^sub>\<nat> n = add_uncurried \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<circ>\<^sub>c n"
  unfolding add_def 
proof - 
  have fact1: "m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>:\<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    using assms(1) comp_type terminal_func_type by blast
  have "add_uncurried \<circ>\<^sub>c \<langle>m,n\<rangle> = add_uncurried \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c id one  ,id \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>"
    by (metis assms cfunc_type_def id_left_unit id_right_unit)
  also have "... = add_uncurried \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c n)  ,id \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>"
    by (metis assms(2) comp_type id_type one_unique_element terminal_func_type)
  also have "... = add_uncurried \<circ>\<^sub>c \<langle>(m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c n  ,id \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>"
    using comp_associative by auto
  also have "... = add_uncurried \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<circ>\<^sub>c n"
    using assms(2) cfunc_prod_comp fact1 id_type by fastforce
  then show "add_uncurried \<circ>\<^sub>c \<langle>m,n\<rangle> = add_uncurried \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c n"  using calculation by auto
qed

lemma add_apply1_left:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n\<in>\<^sub>c \<nat>\<^sub>c"
  shows "m +\<^sub>\<nat> n = add_uncurried \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<circ>\<^sub>c m"
  unfolding add_def 
proof - 
  have fact1: "n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>:\<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    using assms(2) comp_type terminal_func_type by blast
  have "add_uncurried \<circ>\<^sub>c \<langle>m,n\<rangle> = add_uncurried \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c \<circ>\<^sub>c m, n \<circ>\<^sub>c id one\<rangle>"
    by (metis assms cfunc_type_def id_left_unit id_right_unit)
  also have "... = add_uncurried \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c \<circ>\<^sub>c m, n \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m)\<rangle>"
    by (metis assms(1) comp_type id_type one_unique_element terminal_func_type)
  also have "... = add_uncurried \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c \<circ>\<^sub>c m, (n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c m\<rangle>"
    using comp_associative by auto
  also have "... = add_uncurried \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<rangle> \<circ>\<^sub>c m"
    using assms(1) cfunc_prod_comp fact1 id_type by fastforce
  then show "add_uncurried \<circ>\<^sub>c \<langle>m,n\<rangle> = add_uncurried \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c m" 
    using calculation by auto
qed

(*We make this unusual result its own lemma since it will be used in the commutativity proof*)
lemma id_N_def2:
  shows  "add_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle> = id \<nat>\<^sub>c"
  proof (rule natural_number_object_func_unique[where f= successor,  where X= "\<nat>\<^sub>c"])
    show "add_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
      by (meson add_uncurried_type cfunc_prod_type comp_type id_type terminal_func_type zero_type)
    show "id\<^sub>c \<nat>\<^sub>c : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
      by (simp add: id_type)
    show "successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
      by (simp add: successor_type)
    show "(add_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero = id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
    proof - 
      have "(add_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c zero = 
             add_uncurried \<circ>\<^sub>c \<langle>(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>)\<circ>\<^sub>c zero,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero\<rangle>"
        by (smt cfunc_prod_comp comp_associative comp_type id_type terminal_func_type zero_type)
      also have "... =add_uncurried \<circ>\<^sub>c \<langle>zero,zero \<rangle>"
        by (metis cfunc_type_def comp_associative comp_type id_left_unit id_right_unit id_type one_unique_element terminal_func_type zero_type)
      also have "... = zero"
        using add_def add_respects_zero_on_right zero_type by auto
      also have "... = id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
        by (metis cfunc_type_def id_left_unit zero_type)
      then show ?thesis  using calculation by auto
    qed
    show "(add_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor =
    successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
    proof - 
      have "(add_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c successor =
           add_uncurried \<circ>\<^sub>c (\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c successor) "
        by (simp add: comp_associative)
      also have "... =  add_uncurried \<circ>\<^sub>c \<langle>(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor\<rangle>"
        using cfunc_prod_comp id_type comp_type  successor_type zero_betaN_type by fastforce
      also have "... =  add_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> ,  successor\<rangle>"
        by (metis cfunc_type_def comp_associative comp_type id_left_unit successor_type terminal_func_type terminal_func_unique)
      also have "... = (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_curried) \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,successor\<rangle>"
        unfolding add_uncurried_def
        by auto
      also have "... =  eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,  add_curried \<circ>\<^sub>c successor\<rangle>"
        by (smt \<open>id\<^sub>c \<nat>\<^sub>c : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<close> add_curried_property cfunc_cross_prod_comp_cfunc_prod cfunc_type_def comp_associative id_left_unit successor_type zero_betaN_type)
      also have "... =  eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,  successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c add_curried\<rangle>"
        by (simp add: add_curried_comp_succ_eq)
      also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  (id \<nat>\<^sub>c \<times>\<^sub>f successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f)\<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, add_curried\<rangle>"
        by (smt \<open>id\<^sub>c \<nat>\<^sub>c : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<close> add_curried_property cfunc_cross_prod_comp_cfunc_prod cfunc_type_def id_left_unit square_commutes_def zero_betaN_type)
      also have "... = (successor  \<circ>\<^sub>c  eval_func \<nat>\<^sub>c \<nat>\<^sub>c ) \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, add_curried\<rangle>"
        unfolding exp_func_def
        using \<open>successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<close> cfunc_type_def codomain_comp comp_associative compatible_comp_ETCS_func domain_comp eval_func_type transpose_func_def by auto
      also have "... = successor \<circ>\<^sub>c eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_curried) \<circ>\<^sub>c \<langle>zero\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>"
        by (smt \<open>id\<^sub>c \<nat>\<^sub>c : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<close> add_curried_property cfunc_cross_prod_comp_cfunc_prod cfunc_type_def comp_associative id_left_unit id_right_unit zero_betaN_type)
      also have "... = successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>"
        by (simp add: add_uncurried_def comp_associative)
      then show ?thesis using calculation by auto
    qed
    show " id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor = successor \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c"
      by (metis cfunc_type_def id_left_unit id_right_unit successor_type)
  qed



lemma add_respects_zero_on_left:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c"
  shows "zero +\<^sub>\<nat> m = m"
    by (metis add_apply1 assms cfunc_type_def comp_associative id_left_unit zero_type id_N_def2)

lemma add_uncurried_respects_zero_on_left:
  assumes "f : X \<rightarrow> \<nat>\<^sub>c"
  shows "add_uncurried \<circ>\<^sub>c \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>, f\<rangle> = f"
  by (smt assms cfunc_prod_comp comp_associative id_N_def2 id_left_unit2 id_type terminal_func_comp zero_betaN_type)

lemma add_uncurried_respects_succ_right:
  assumes "m : X \<rightarrow> \<nat>\<^sub>c" "n : X \<rightarrow> \<nat>\<^sub>c" 
  shows "add_uncurried \<circ>\<^sub>c \<langle>m, successor  \<circ>\<^sub>c n\<rangle>  = successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c \<langle>m, n\<rangle>"
proof -
  have fact1: "add_curried \<circ>\<^sub>c n : X \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
    using add_curried_type assms(2) comp_type by blast
  have "add_uncurried \<circ>\<^sub>c \<langle>m, successor  \<circ>\<^sub>c n\<rangle> =  eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, add_curried \<circ>\<^sub>c (successor \<circ>\<^sub>c n)\<rangle>"
    using add_uncurried_apply assms successor_type by auto
  also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m, successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c add_curried \<circ>\<^sub>c n\<rangle>"
    by (simp add: add_curried_comp_succ_eq comp_associative)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c m, successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c add_curried \<circ>\<^sub>c n\<rangle>"
    by (metis assms(1) cfunc_type_def id_left_unit)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c ((id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f) \<circ>\<^sub>c \<langle>m,add_curried \<circ>\<^sub>c n\<rangle>)"
    using  cfunc_cross_prod_comp_cfunc_prod
    by (smt add_curried_property assms(1) fact1 id_type square_commutes_def)
  also have "... = successor \<circ>\<^sub>c (eval_func  \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c \<langle>m,add_curried \<circ>\<^sub>c n\<rangle>)"
    using cfunc_type_def codomain_comp comp_associative compatible_comp_ETCS_func domain_comp eval_func_type exp_func_def successor_type transpose_func_def by auto
  also have "... = successor \<circ>\<^sub>c (add_uncurried \<circ>\<^sub>c \<langle>m,n\<rangle>)"
    using add_uncurried_apply assms by auto
  then show ?thesis 
    using calculation by auto
qed



lemma add_uncurried_commutes_succ:
  assumes "m : X \<rightarrow> \<nat>\<^sub>c" "n : X \<rightarrow> \<nat>\<^sub>c" 
  shows "add_uncurried \<circ>\<^sub>c \<langle>successor  \<circ>\<^sub>c m,  n\<rangle>  =  add_uncurried \<circ>\<^sub>c \<langle>m, successor  \<circ>\<^sub>c n\<rangle>"
proof - 
  have fact00: "(successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c):  \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c"
    by (simp add: cfunc_cross_prod_type id_type successor_type)
  then have fact01: "(add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>:  \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
    using add_uncurried_type transpose_func_def by auto
  then have fact02: "(add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c zero :  one \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
    using comp_type zero_type by blast
  have fact03: "(successor  \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one))\<^sup>\<sharp> :  one \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
    using comp_type left_cart_proj_type successor_type transpose_func_def by blast
  have fact0: "(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor): \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c"
    by (simp add: cfunc_cross_prod_type id_type successor_type)
  then have fact1: "(add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor))\<^sup>\<sharp>: \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
    using add_uncurried_type transpose_func_def by auto
  have fact04: "(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ( successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f)): \<nat>\<^sub>c\<times>\<^sub>c(\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<rightarrow> \<nat>\<^sub>c\<times>\<^sub>c(\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)"
    using add_curried_property cfunc_cross_prod_type id_type square_commutes_def by auto
  have fact05: "(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_curried) : \<nat>\<^sub>c\<times>\<^sub>c(\<nat>\<^sub>c) \<rightarrow> \<nat>\<^sub>c\<times>\<^sub>c(\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)"
    by (simp add: add_curried_type cfunc_cross_prod_type id_type)
  have fact2: "successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c  (left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>: one \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
    by (meson add_curried_property comp_type square_commutes_def triangle_commutes_def)
  have fact21: "(successor \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one)) :\<nat>\<^sub>c\<times>\<^sub>c  one \<rightarrow>  \<nat>\<^sub>c"
    using cfunc_type_def codomain_comp compatible_comp_ETCS_func domain_comp left_cart_proj_type successor_type by auto
  then have fact22: "(successor \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one))\<^sup>\<sharp>: one \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
    using transpose_func_def by blast
  have fact23: "(add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor))\<^sup>\<sharp> \<circ>\<^sub>c zero: one \<rightarrow>  \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
    using fact1 zero_type by auto
  have "eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ((add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor))\<^sup>\<sharp> \<circ>\<^sub>c zero)) = 
    eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor))\<^sup>\<sharp>)\<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero)"
    using fact1 identity_distributes_across_composition zero_type by auto
  also have "... = add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero)"
    by (metis add_uncurried_type comp_associative comp_type fact0 transpose_func_def)
  also have "... = add_uncurried  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor \<circ>\<^sub>c zero))"
    using identity_distributes_across_composition successor_type zero_type by auto
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_curried) \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  (successor \<circ>\<^sub>c zero))"
    by (simp add: add_uncurried_def comp_associative)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add_curried \<circ>\<^sub>c (successor \<circ>\<^sub>c zero)))"
    by (metis add_curried_property comp_type identity_distributes_across_composition successor_type zero_type)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c (add_curried\<circ>\<^sub>c zero)))"
    by (simp add: add_curried_comp_succ_eq comp_associative)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c  (left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>))"
    by (simp add: add_curried_0_eq)
  also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f)  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>)"
    using add_curried_property identity_distributes_across_composition square_commutes_def triangle_commutes_def by auto
  also have "... = (successor \<circ>\<^sub>c eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>)"
    using cfunc_type_def codomain_comp comp_associative compatible_comp_ETCS_func domain_comp eval_func_type exp_func_def successor_type transpose_func_def by auto
  also have "... = successor \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one)"
    by (metis comp_associative left_cart_proj_type transpose_func_def)
  then have fact2: " eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ((add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor))\<^sup>\<sharp> \<circ>\<^sub>c zero)) = 
   successor \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one)"
    using calculation by auto
  have fact3: "eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one))\<^sup>\<sharp>) = successor \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one)"
    using cfunc_type_def codomain_comp compatible_comp_ETCS_func domain_comp left_cart_proj_type successor_type transpose_func_def by auto 
  then have fact4: "(successor \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one))\<^sup>\<sharp> =
(add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor))\<^sup>\<sharp> \<circ>\<^sub>c zero"
    using transpose_func_unique fact2 fact21 fact23 by auto
  have fact5: "eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f((add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>\<circ>\<^sub>c zero)) =
              successor \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one)" (*page 13 big aligned equation*)
  proof -
    have "eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f((add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>\<circ>\<^sub>c zero))
     = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f((add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>fzero)"
      using fact01 identity_distributes_across_composition zero_type by auto
    also have "... = (add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>fzero)"
      by (metis add_uncurried_type comp_associative comp_type fact00 transpose_func_def)
    also have "... =  add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f zero)"
      by (smt cfunc_cross_prod_comp_cfunc_cross_prod cfunc_type_def comp_associative id_left_unit id_right_unit id_type successor_type zero_type)
    also have "... = add_uncurried \<circ>\<^sub>c ((id\<^sub>c \<nat>\<^sub>c\<circ>\<^sub>c successor)  \<times>\<^sub>f (zero \<circ>\<^sub>c id\<^sub>c one))"
      by (metis cfunc_type_def id_left_unit id_right_unit successor_type zero_type)
    also have "... =  add_uncurried \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>fzero)  \<circ>\<^sub>c(successor \<times>\<^sub>f id\<^sub>c one)"
      by (smt cfunc_cross_prod_comp_cfunc_cross_prod id_type successor_type zero_type)
    also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_curried) \<circ>\<^sub>c
        (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>fzero)  \<circ>\<^sub>c(successor \<times>\<^sub>f id\<^sub>c one)"
      by (simp add: add_uncurried_def comp_associative)
    also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>) \<circ>\<^sub>c  (successor \<times>\<^sub>f id\<^sub>c one)"
      by (metis add_curried_0_eq add_curried_property comp_associative identity_distributes_across_composition zero_type)
    also have "... = (left_cart_proj \<nat>\<^sub>c one)  \<circ>\<^sub>c  (successor \<times>\<^sub>f id\<^sub>c one)"
      by (metis comp_associative left_cart_proj_type transpose_func_def)
    also have "... = successor \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one)"
      by (simp add: id_type left_cart_proj_cfunc_cross_prod successor_type)
    then show ?thesis using calculation by auto
  qed

  have fact6: "successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor))
              = add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor)) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor))"
  proof - 
    have "successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor)) = 
        (successor \<circ>\<^sub>c  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add_curried))  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor))"
      by (simp add: add_uncurried_def comp_associative)
    also have "... = (eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ( successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f))) \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add_curried))  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor))"
      unfolding exp_func_def using exponential_square_diagram square_commutes_def successor_type cfunc_type_def comp_type transpose_func_def by auto 
    also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ( successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c add_curried)) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor))"
      by (smt add_curried_property cfunc_cross_prod_comp_cfunc_cross_prod comp_associative id_domain id_right_unit id_type square_commutes_def)
    also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (  add_curried \<circ>\<^sub>c successor)) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor))"
      by (simp add: add_curried_comp_succ_eq)
    also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f   add_curried)\<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  successor) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  successor)"
      using add_curried_property comp_associative identity_distributes_across_composition successor_type by auto
    also have "... =  add_uncurried \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  successor) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  successor)"
      by (simp add: add_uncurried_def comp_associative)
    then show ?thesis using calculation by auto
  qed

  

  have fact6b: "successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor))
    = (( add_uncurried \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor)))\<^sup>\<sharp> \<circ>\<^sub>c successor)\<^sup>\<flat>"
    by (smt add_curried_comp_succ_eq add_curried_type add_uncurried_def comp_associative comp_type flat_type inv_transpose_of_composition sharp_cancels_flat successor_type transpose_func_def transpose_of_comp)



  have fact6c: "(add_uncurried \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor)))\<^sup>\<sharp> \<circ>\<^sub>c successor
= successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f  \<circ>\<^sub>c (add_uncurried  \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor)))\<^sup>\<sharp>"
  proof -
    have "(add_uncurried \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor)))\<^sup>\<sharp> \<circ>\<^sub>c successor
= (successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor)))\<^sup>\<sharp>"
      by (smt comp_type fact1 fact6b sharp_cancels_flat successor_type)
    also have "... = successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f  \<circ>\<^sub>c (add_uncurried  \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor)))\<^sup>\<sharp>"
      using add_uncurried_type comp_type fact0 successor_type transpose_of_comp by blast
    then show ?thesis using calculation by auto
  qed

  have fact6d: "(successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))
              = add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f successor)"
  proof - 
    have "(successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))
              = successor  \<circ>\<^sub>c eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add_curried)) \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)"
      by (simp add: add_uncurried_def comp_associative)
    also have "... =  eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add_curried)) \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)"
proof -
    have f1: "eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried\<^sup>\<sharp> = add_uncurried"
        using add_uncurried_type transpose_func_def by blast
      have f2: "domain successor = \<nat>\<^sub>c"
        using cfunc_type_def successor_type by blast
      have f3: "codomain (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried\<^sup>\<sharp>) = domain (eval_func \<nat>\<^sub>c \<nat>\<^sub>c)"
        using f1 by (metis (no_types) add_uncurried_type cfunc_type_def compatible_comp_ETCS_func)
      have f4: "successor \<circ>\<^sub>c add_uncurried \<in> ETCS_func"
        using add_uncurried_type cfunc_type_def compatible_comp_ETCS_func successor_type by fastforce
      have f5: "\<forall>c ca. codomain (eval_func ca c) = ca"
        by (meson cfunc_type_def eval_func_type)
      have f6: "\<forall>c ca. eval_func ca c \<in> ETCS_func"
        using cfunc_type_def eval_func_type by presburger
      have f7: "successor \<circ>\<^sub>c successor \<in> ETCS_func"
        using cfunc_type_def compatible_comp_ETCS_func successor_type by presburger
      then have f8: "domain (successor \<circ>\<^sub>c successor) = \<nat>\<^sub>c"
        using f6 f5 f2 by (metis comp_associative compatible_comp_ETCS_func)
      have "eval_func (codomain (successor \<circ>\<^sub>c eval_func \<nat>\<^sub>c \<nat>\<^sub>c)) \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (successor \<circ>\<^sub>c eval_func \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> = successor \<circ>\<^sub>c eval_func \<nat>\<^sub>c \<nat>\<^sub>c"
        using f4 f3 f1 by (metis cfunc_type_def comp_associative compatible_comp_ETCS_func eval_func_type transpose_func_def)
     then show ?thesis
      using f8 f7 f6 f5 by (metis (no_types) add_uncurried_def comp_associative compatible_comp_ETCS_func exp_func_def)
  qed
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  (successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c add_curried)) \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)"
    by (smt add_curried_property cfunc_cross_prod_comp_cfunc_cross_prod comp_associative id_domain id_right_unit id_type square_commutes_def)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  ( add_curried \<circ>\<^sub>c successor)) \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)"
    by (simp add: add_curried_comp_succ_eq)
  also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_curried) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)"
    using add_curried_type comp_associative identity_distributes_across_composition successor_type by auto
  also have "... = add_uncurried \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)"
    by (simp add: add_uncurried_def comp_associative)
  also have "... = add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f successor)"
  proof -
    have "successor \<times>\<^sub>f successor = (id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor) \<times>\<^sub>f (successor \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c)"
      by (metis (no_types) cfunc_type_def id_left_unit id_right_unit successor_type)
    then show ?thesis
      by (metis (no_types) cfunc_cross_prod_comp_cfunc_cross_prod id_type successor_type)
  qed
 then show ?thesis using calculation by auto
qed

  have fact6d: "(successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) = 
               ((add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c successor)\<^sup>\<flat>"
  proof - 
    have "(successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) =  
        add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f successor)"
      by (simp add: fact6d)
    also have "... = (add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor))"
      by (smt cfunc_cross_prod_comp_cfunc_cross_prod id_left_unit2 id_right_unit2 id_type successor_type)
    also have "... = ((add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c successor)\<^sup>\<flat>"
      by (smt add_uncurried_type comp_associative comp_type fact00 inv_transpose_func_def2 inv_transpose_of_composition successor_type transpose_func_def)
    then show ?thesis using calculation by auto
  qed


  have fact6e: "(add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c successor = 
                successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c (add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>" 
  proof - 
    have "(add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c successor = 
          (successor  \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>"
    proof -
      have "\<forall>c ca. ca \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> c \<or> \<not> ca : \<nat>\<^sub>c \<rightarrow> c"
        by (meson comp_type successor_type)
      then show ?thesis
        by (metis (no_types) fact01 fact6d sharp_cancels_flat)
    qed
    also have "... = successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c (add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>"
      by (meson add_uncurried_type comp_type fact00 successor_type transpose_of_comp)
then show ?thesis using calculation by auto
  qed
  

  
  have fact8: " (add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  (successor)))\<^sup>\<sharp> = 
                (add_uncurried \<circ>\<^sub>c ((successor) \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c ))\<^sup>\<sharp>" 
   proof (rule natural_number_object_func_unique[where f= "successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f",  where X= "\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"])
     show sg1: "(add_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
       by (simp add: fact1)
     show sg2: "(add_uncurried \<circ>\<^sub>c successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
       by (simp add: fact01)
     show sg3: "successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f : \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
       by (simp add: exp_func_type successor_type)
     show sg4: " (add_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor)\<^sup>\<sharp> \<circ>\<^sub>c zero =
              (add_uncurried \<circ>\<^sub>c successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero"
       using fact02 fact21 fact4 fact5 transpose_func_unique by auto
     show sg5: "(add_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor)\<^sup>\<sharp> \<circ>\<^sub>c successor =
                successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c (add_uncurried \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor)\<^sup>\<sharp>"
       using fact6c by auto
     show sg6: "(add_uncurried \<circ>\<^sub>c successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c successor =
                 successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c (add_uncurried \<circ>\<^sub>c successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>"
       by (simp add: fact6e)
   qed
    
   have fact9: "(add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  (successor))) = 
                (add_uncurried \<circ>\<^sub>c ((successor) \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c ))"
     by (smt add_uncurried_type comp_type fact0 fact00 fact8 transpose_func_def)
  show "add_uncurried \<circ>\<^sub>c \<langle>successor  \<circ>\<^sub>c m,  n\<rangle>  =  add_uncurried \<circ>\<^sub>c \<langle>m, successor  \<circ>\<^sub>c n\<rangle>"
   proof - 
     have "add_uncurried \<circ>\<^sub>c \<langle>successor  \<circ>\<^sub>c m,  n\<rangle>  = add_uncurried \<circ>\<^sub>c (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c ) \<circ>\<^sub>c  \<langle>m,n\<rangle>"
       by (smt assms(1) assms(2) cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_type successor_type)
     also have "... = add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f  (successor)) \<circ>\<^sub>c  \<langle>m,n\<rangle>"
       by (simp add: comp_associative fact9)
     also have "... = add_uncurried \<circ>\<^sub>c \<langle>m, successor  \<circ>\<^sub>c n\<rangle>"
       using assms(1) assms(2) cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_type successor_type by fastforce

      then show ?thesis using calculation by auto
 qed
qed



lemma add_respects_succ1:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c" 
  shows "m +\<^sub>\<nat> (successor  \<circ>\<^sub>c n)  =  successor\<circ>\<^sub>c (m +\<^sub>\<nat> n)"
  using add_def add_uncurried_respects_succ_right assms by auto


lemma add_respects_succ2:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c" 
  shows "m +\<^sub>\<nat> (successor  \<circ>\<^sub>c n)  =  (successor\<circ>\<^sub>c m) +\<^sub>\<nat> n"
  using add_def add_uncurried_commutes_succ assms(1) assms(2) by presburger

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
  shows "add_uncurried \<circ>\<^sub>c \<langle> right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c ,  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<rangle>
     \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor)\<circ>\<^sub>c \<langle>m,n\<rangle> = 
successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c  \<langle> right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c ,  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<rangle>\<circ>\<^sub>c \<langle>m,n\<rangle>"
proof - 
  have type1: "\<langle>m,successor \<circ>\<^sub>c n\<rangle>: one \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
    using assms(1) assms(2) cfunc_prod_type successor_type by auto
  have type2: "\<langle>m, n\<rangle>: one \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
    by (simp add: assms(1) assms(2) cfunc_prod_type)
  have "add_uncurried \<circ>\<^sub>c \<langle> right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c ,  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<rangle>
     \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor)\<circ>\<^sub>c \<langle>m,n\<rangle> = 
add_uncurried \<circ>\<^sub>c \<langle> right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c ,  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<rangle>
     \<circ>\<^sub>c \<langle>m,successor \<circ>\<^sub>c n\<rangle>"
    by (smt assms(1) assms(2) cfunc_cross_prod_comp_cfunc_prod cfunc_type_def id_left_unit id_type successor_type)
  also have "... = add_uncurried \<circ>\<^sub>c \<langle> right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m,successor \<circ>\<^sub>c n\<rangle> ,  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m,successor \<circ>\<^sub>c n\<rangle> \<rangle>"
    using cfunc_prod_comp left_cart_proj_type right_cart_proj_type type1 by fastforce
  also have "... = add_uncurried \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c n , m\<rangle>"
    by (metis assms(1) assms(2) comp_type left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod successor_type)
  also have "... = (successor \<circ>\<^sub>c n)  +\<^sub>\<nat> m"
    by (simp add: add_def)
  also have "... = successor  \<circ>\<^sub>c (n  +\<^sub>\<nat> m)"
    using add_respects_succ1 add_respects_succ2 assms(1) assms(2) by auto
  also have "... = successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c \<langle>n , m\<rangle>"
    by (simp add: add_def)
  also have "... = successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c
                 \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m , n\<rangle> , 
                  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>m , n\<rangle>\<rangle>"
    using assms(1) assms(2) left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod by auto
  also have "... = successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c  \<langle> right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c ,  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<rangle>\<circ>\<^sub>c \<langle>m,n\<rangle>"
    using cfunc_prod_comp  left_cart_proj_type right_cart_proj_type type2 by fastforce 
  then show ?thesis using calculation by auto
qed

lemma pointfree_add_pi1_pi0_1xsEqs_s_add_pi1_pi_0:
  shows "add_uncurried \<circ>\<^sub>c \<langle> right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c ,  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor)
    = successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c  \<langle> right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c ,  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<rangle>"
proof (rule one_separator[where X="\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c", where Y="\<nat>\<^sub>c"])
  have cross_type: "id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
    by (simp add: cfunc_cross_prod_type id_type successor_type)
  show "add_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor
          : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    using add_uncurried_type comp_type cross_type swap_type unfolding swap_def by blast
  show "successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>
          : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    using add_uncurried_type comp_type successor_type swap_type unfolding swap_def by blast
next
  fix x
  assume x_type: "x \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
  show "(add_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor) \<circ>\<^sub>c x
    = (successor \<circ>\<^sub>c add_uncurried \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c x"
    using add_pi1_pi0_1xsEqs_s_add_pi1_pi_0 cart_prod_decomp comp_associative x_type by fastforce
qed

lemma add_commutes:
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" "n \<in>\<^sub>c \<nat>\<^sub>c" 
  shows "m +\<^sub>\<nat> n  = n +\<^sub>\<nat> m"
proof - 
  have type1: " \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c),(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle>: 
        (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<rightarrow> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
      by (simp add: cfunc_prod_type left_cart_proj_type right_cart_proj_type)
    have type2: "(add_uncurried  \<circ>\<^sub>c 
    \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c),(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle>): (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<rightarrow>  \<nat>\<^sub>c"
      by (meson add_uncurried_type comp_type type1)
    have type3: "(add_uncurried  \<circ>\<^sub>c 
    \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c),(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
      by (simp add: transpose_func_def type2)
    have type4: "(add_uncurried  \<circ>\<^sub>c 
    \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c),(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>\<circ>\<^sub>c zero : one \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
      using type3 zero_type by auto
    have type5: " \<langle>(left_cart_proj \<nat>\<^sub>c one),zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c one)\<rangle>:
         (\<nat>\<^sub>c \<times>\<^sub>c one)   \<rightarrow> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
      by (meson cfunc_prod_type comp_type left_cart_proj_type right_cart_proj_type zero_type)
    have type6: "\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c(left_cart_proj \<nat>\<^sub>c one):  \<nat>\<^sub>c \<times>\<^sub>c one \<rightarrow> one"
      by (meson comp_type left_cart_proj_type terminal_func_type)
    then have type7: "zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c(left_cart_proj \<nat>\<^sub>c one):  \<nat>\<^sub>c \<times>\<^sub>c one \<rightarrow> \<nat>\<^sub>c"
      using comp_type zero_type by blast
    then have type8: "\<langle>m,n\<rangle>: one \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c\<nat>\<^sub>c"
      by (simp add: assms(1) assms(2) cfunc_prod_type)
  have "eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ((add_uncurried  \<circ>\<^sub>c 
    \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c),(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero)) = 
    left_cart_proj \<nat>\<^sub>c one"
  proof-
    have "eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f ((add_uncurried  \<circ>\<^sub>c
    \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c),(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero)) = 
    eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add_uncurried \<circ>\<^sub>c
    \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c),(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>)  \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero)"
      using identity_distributes_across_composition type3 zero_type by auto 
    also have "... = add_uncurried \<circ>\<^sub>c
   \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c),(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero)"
        using comp_associative transpose_func_def type2 by presburger
    also have "... = add_uncurried \<circ>\<^sub>c
   \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c),(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c
   \<langle>(left_cart_proj \<nat>\<^sub>c one),zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c one)\<rangle>"
      by (metis cfunc_cross_prod_def cfunc_type_def id_domain id_left_unit left_cart_proj_type zero_type)
    also have "... = add_uncurried \<circ>\<^sub>c
   \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c one),zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c one)\<rangle>,
    (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c one),zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c one)\<rangle>
   \<rangle>"
      using cfunc_prod_comp left_cart_proj_type right_cart_proj_type type5 by fastforce
    also have "... = add_uncurried \<circ>\<^sub>c
\<langle>zero \<circ>\<^sub>c (right_cart_proj \<nat>\<^sub>c one), (left_cart_proj \<nat>\<^sub>c one)\<rangle>"
      using cfunc_prod_comp
      by (smt comp_type left_cart_proj_cfunc_prod left_cart_proj_type right_cart_proj_cfunc_prod right_cart_proj_type zero_type)
    also have "... =  add_uncurried \<circ>\<^sub>c
\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c(left_cart_proj \<nat>\<^sub>c one), (left_cart_proj \<nat>\<^sub>c one)\<rangle>"
      by (metis right_cart_proj_type terminal_func_unique type6)
    also have "... =  add_uncurried \<circ>\<^sub>c
\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c(left_cart_proj \<nat>\<^sub>c one), id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one)\<rangle>"
      by (metis cfunc_type_def compatible_comp_ETCS_func domain_comp id_left_unit type6 zero_betaN_type)
    also have "... =  add_uncurried \<circ>\<^sub>c
\<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one) "
      using cfunc_prod_comp
      by (smt comp_associative id_type left_cart_proj_type zero_betaN_type)
    also have "... = id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c one) "
    by (simp add: comp_associative id_N_def2)
    also have "... = left_cart_proj \<nat>\<^sub>c one"
    by (metis cfunc_type_def id_left_unit left_cart_proj_type)
   then show ?thesis using calculation by auto
    qed
  
    then have fact0: "((add_uncurried  \<circ>\<^sub>c
    \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c),(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero)
   = (left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp>"
    using inv_transpose_func_def2 sharp_cancels_flat type4 by fastforce 

  have fact1: "((add_uncurried \<circ>\<^sub>c 
        \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c), (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
        successor)\<^sup>\<flat> = 
        successor \<circ>\<^sub>c 
        add_uncurried \<circ>\<^sub>c 
        \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c), (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle>"
  proof - 
     have "((add_uncurried \<circ>\<^sub>c 
        \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c), (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
        successor)\<^sup>\<flat> = 
    (add_uncurried \<circ>\<^sub>c \<langle> right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c ,  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<rangle>)\<^sup>\<sharp>\<^sup>\<flat>
     \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor)"
      by (meson inv_transpose_of_composition successor_type type3)
    also have "... =  (add_uncurried \<circ>\<^sub>c \<langle> right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c ,  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<rangle>)
     \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor)"
      using flat_cancels_sharp type2 by auto
    also have "... =  successor \<circ>\<^sub>c 
        add_uncurried \<circ>\<^sub>c 
        \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c), (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>"
      using comp_associative pointfree_add_pi1_pi0_1xsEqs_s_add_pi1_pi_0 by auto
    then show ?thesis using calculation by auto
 qed

  have fact2: "((add_uncurried \<circ>\<^sub>c 
        \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c), (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
        successor) = 
        successor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c 
        (add_uncurried \<circ>\<^sub>c 
        \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c), (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp>"
    by (metis comp_type fact1 sharp_cancels_flat successor_type transpose_of_comp type2 type3)

  have add_curried_def2: "(add_uncurried \<circ>\<^sub>c 
        \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c), (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp> = add_curried"
    using add_curried_0_eq add_curried_property fact0 fact2 natural_number_object_func_unique square_commutes_def type3 by auto

  show "m +\<^sub>\<nat> n  = n +\<^sub>\<nat> m"
  proof - 
    have "m +\<^sub>\<nat> n = add_uncurried \<circ>\<^sub>c \<langle>m,n\<rangle>"
      by (simp add: add_def)
    also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_curried)\<circ>\<^sub>c \<langle>m,n\<rangle>"
      by (simp add: add_uncurried_def comp_associative)
    also have "... = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (add_uncurried \<circ>\<^sub>c 
        \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c), (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>)\<^sup>\<sharp>)\<circ>\<^sub>c \<langle>m,n\<rangle>"
      by (simp add: add_curried_def2)
    also have "... =  (add_uncurried \<circ>\<^sub>c 
        \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c), (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<rangle>) \<circ>\<^sub>c \<langle>m,n\<rangle>"
      using \<open>m +\<^sub>\<nat> n = add_uncurried \<circ>\<^sub>c \<langle>m,n\<rangle>\<close> add_curried_def2 add_uncurried_def calculation transpose_func_def type2 by force
    also have "... = (add_uncurried \<circ>\<^sub>c 
        \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>m,n\<rangle>, (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)\<circ>\<^sub>c \<langle>m,n\<rangle> \<rangle>) "
      by (metis cfunc_prod_comp comp_associative left_cart_proj_type right_cart_proj_type type8)
    also have "... = add_uncurried \<circ>\<^sub>c \<langle>n,m\<rangle>"
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
  have typePair: "\<langle>a,b\<rangle> \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c"
    using assms(1) assms(2) cfunc_prod_type by blast
  have typePair1: " \<langle>\<langle>a,b\<rangle>,zero\<rangle> \<in>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c"
    by (simp add: cfunc_prod_type typePair zero_type)
  have projPairType: "(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c): 
    (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c"
    using comp_type left_cart_proj_type right_cart_proj_type by blast
  have type3: "(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
    using add_uncurried_type associate_right_type cfunc_cross_prod_type comp_type id_type by blast
  have type4:
    "add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    using add_uncurried_type comp_type type3 by blast
  have type5:
    "(add_uncurried \<circ>\<^sub>c(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
    using transpose_func_def type4 by blast
  have type6: "add_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) one : (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c one\<rightarrow>  \<nat>\<^sub>c"
    using add_uncurried_type comp_type left_cart_proj_type by blast

  have triangle1: "(add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero = 
    (add_uncurried \<circ>\<^sub>c add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero"
    (is "?lhs = ?rhs")
  proof (rule same_evals_equal[where X="\<nat>\<^sub>c", where A="\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c", where Z="one"]) 
    show lhs_type: "?lhs : one \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
      using type5 zero_type by auto
    show rhs_type: "?rhs : one \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
      by (meson add_uncurried_type cfunc_cross_prod_type comp_type id_type transpose_func_def zero_type)
    
    have lhs_eval: "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f ?lhs)
      = (add_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) one)"
    (is "?lhs1 = ?rhs1")
    proof (rule one_separator[where X="(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c one", where Y="\<nat>\<^sub>c"])
      show LHS_type: "?lhs1 : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one \<rightarrow> \<nat>\<^sub>c"
        by (meson cfunc_cross_prod_type comp_type eval_func_type id_type type5 zero_type)
      show RHS_type: "?rhs1 : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one \<rightarrow> \<nat>\<^sub>c"
        using transpose_func_def type6 by presburger
    next
      fix x
      assume "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one"
      then obtain a b where "x = \<langle>\<langle>a,b\<rangle>, id one\<rangle>" and a_type: "a \<in>\<^sub>c \<nat>\<^sub>c" and b_type: "b \<in>\<^sub>c \<nat>\<^sub>c"
        by (metis cart_prod_decomp id_type terminal_func_unique)
      then show "?lhs1 \<circ>\<^sub>c x = ?rhs1 \<circ>\<^sub>c x"
      proof auto
        have a_b_type: "\<langle>a,b\<rangle> \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
          by (simp add: a_type b_type cfunc_prod_type)
        have b_zero_type: "\<langle>b, zero\<rangle> \<in>\<^sub>c \<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c"
          by (simp add: b_type cfunc_prod_type zero_type)

        have "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c 
            (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
              (add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c
            \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>
          = eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c
            (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f
              (add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp>) \<circ>\<^sub>c
            (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>"
          using comp_associative identity_distributes_across_composition type5 zero_type by auto
        also have "... = (add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c
          ((id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f zero) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>)"
          using comp_associative flat_cancels_sharp inv_transpose_func_def2 type4 type5 by fastforce
        also have "... = (add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, zero\<rangle>"
          by (smt cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2 id_type a_b_type zero_type)
        also have "... = (add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried)) \<circ>\<^sub>c \<langle>a, \<langle>b, zero\<rangle>\<rangle>"
          by (metis a_type b_type associate_right_ap comp_associative zero_type)
        also have "... = add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) \<circ>\<^sub>c \<langle>a, \<langle>b, zero\<rangle>\<rangle>"
          by (simp add: comp_associative)
        also have "... = add_uncurried \<circ>\<^sub>c \<langle>a, add_uncurried \<circ>\<^sub>c \<langle>b, zero\<rangle>\<rangle>"
          using a_type b_zero_type id_type add_uncurried_type id_left_unit2 cfunc_cross_prod_comp_cfunc_prod
          by fastforce
        also have "... = (add_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) one) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>"
          by (metis a_b_type add_def add_respects_zero_on_right b_type comp_associative id_type left_cart_proj_cfunc_prod)
        then show "?lhs1 \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, id\<^sub>c one\<rangle> = ?rhs1 \<circ>\<^sub>c \<langle>\<langle>a, b\<rangle>, id\<^sub>c one\<rangle>"
          using calculation by (simp add: comp_associative) 
      qed
    qed

    term ?lhs
    term ?rhs

    have rhs_eval: "eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f ?rhs) 
      = (add_uncurried \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c\<times>\<^sub>c \<nat>\<^sub>c) one)"
    (is "?lhs1 = ?rhs1")
    proof (rule one_separator[where X="(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<times>\<^sub>c one", where Y="\<nat>\<^sub>c"])
      show LHS_type: "?lhs1 : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one \<rightarrow> \<nat>\<^sub>c"
        using flat_type inv_transpose_func_def2 rhs_type by auto
      show RHS_type: "?rhs1 : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one \<rightarrow> \<nat>\<^sub>c"
        using transpose_func_def type6 by presburger
    next
      fix x
      assume "x \<in>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>c one"
      then obtain a b where "x = \<langle>\<langle>a,b\<rangle>, id one\<rangle>" and a_type: "a \<in>\<^sub>c \<nat>\<^sub>c" and b_type: "b \<in>\<^sub>c \<nat>\<^sub>c"
        by (metis cart_prod_decomp id_type terminal_func_unique)
      then show "?lhs1 \<circ>\<^sub>c x = ?rhs1 \<circ>\<^sub>c x"
      proof auto
        have add_add_sharp_type: "(add_uncurried \<circ>\<^sub>c add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>"
          using cfunc_type_def codomain_comp compatible_comp_ETCS_func rhs_type zero_type by auto

        have "?lhs1  \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>  =  
          eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c
          (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f (add_uncurried \<circ>\<^sub>c add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)\<^sup>\<sharp> \<circ>\<^sub>c zero) \<circ>\<^sub>c
          \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>"
          by (simp add: comp_associative)
        also have "... =  
          eval_func  \<nat>\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<circ>\<^sub>c 
            (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f (add_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f  id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c
              (id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f zero)) \<circ>\<^sub>c
              \<langle>\<langle>a,b\<rangle>,id\<^sub>c one\<rangle>"
also have "... = (add_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f  id\<^sub>c \<nat>\<^sub>c))  \<circ>\<^sub>c
\<langle>\<langle>a,b\<rangle>,zero\<rangle>"
also have "... = add_uncurried \<circ>\<^sub>c \<langle> add_uncurried \<circ>\<^sub>c \<langle>a,b\<rangle>,zero\<rangle>"
also have "... = add_uncurried \<circ>\<^sub>c \<langle>a,b\<rangle>"

term ?rhs
    term ?lhs

(*Top of page 9*)
    have "add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) \<circ>\<^sub>c associate_right \<nat>\<^sub>c \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c 
      (id\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor)
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle> = 
  add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried)  \<circ>\<^sub>c
 \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)  \<circ>\<^sub>c  left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,
  \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,
right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c
\<langle>\<langle>a,b\<rangle>,successor \<circ>\<^sub>c c\<rangle>"
  also have "... = add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) 
 \<circ>\<^sub>c \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)  \<circ>\<^sub>c  left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c
\<circ>\<^sub>c
\<langle>\<langle>a,b\<rangle>,successor \<circ>\<^sub>c c\<rangle> , 
 \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,
right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,successor \<circ>\<^sub>c c\<rangle>"
  also have "... = add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) 
 \<circ>\<^sub>c \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c\<langle>a,b\<rangle>, 
 \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c 
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,successor \<circ>\<^sub>c c\<rangle>,
right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,successor \<circ>\<^sub>c c\<rangle> \<rangle>\<rangle>"
  also have "... = add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) 
 \<circ>\<^sub>c \<langle> a, \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>a,b\<rangle>, successor \<circ>\<^sub>c c\<rangle> \<rangle>"
  also have "... = add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) 
 \<circ>\<^sub>c \<langle>a,\<langle>b,successor \<circ>\<^sub>c c\<rangle> \<rangle>"
  also have "... = a +\<^sub>\<nat> (b +\<^sub>\<nat> successor \<circ>\<^sub>c c)"
  also have "... = a +\<^sub>\<nat> (successor \<circ>\<^sub>c (b +\<^sub>\<nat> c))"
  also have "... = successor \<circ>\<^sub>c (a +\<^sub>\<nat> (b +\<^sub>\<nat> c))"
  also have "... = successor \<circ>\<^sub>c (add_uncurried 
          \<circ>\<^sub>c \<langle>a,add_uncurried \<circ>\<^sub>c \<langle>b,c\<rangle>\<rangle>"
  also have "... = successor \<circ>\<^sub>c (add_uncurried \<circ>\<^sub>c
(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) \<circ>\<^sub>c
    \<langle>a,\<langle>b,c\<rangle>\<rangle>)"
  also have "... = successor \<circ>\<^sub>c (add_uncurried \<circ>\<^sub>c
(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) \<circ>\<^sub>c
    \<langle>a,\<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c
 \<langle>a,b\<rangle>,c\<rangle>\<rangle>)"
  also have "... = successor \<circ>\<^sub>c (add_uncurried \<circ>\<^sub>c
(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) \<circ>\<^sub>c
\<langle> (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c
 \<langle>a,b\<rangle>, \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c 
(left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>,
(right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c  \<langle>\<langle>a,b\<rangle>,c\<rangle>\<rangle>\<rangle>)"
  also have "... = successor \<circ>\<^sub>c (add_uncurried \<circ>\<^sub>c
(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) \<circ>\<^sub>c
\<langle> (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c
 \<langle>\<langle>a,b\<rangle>,c\<rangle>, \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c 
(left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c), 
(right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>\<rangle>\<rangle>)"
  also have "successor \<circ>\<^sub>c (add_uncurried \<circ>\<^sub>c
(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) \<circ>\<^sub>c \<langle>
(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)  \<circ>\<^sub>c 
(left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c
 (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<rangle>\<rangle>) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"

(*It follows that*)
    have "((add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried)  \<circ>\<^sub>c
 \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)  \<circ>\<^sub>c  left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,
  \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,
right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor)\<^sup>\<flat> = 
((add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried)  \<circ>\<^sub>c
 \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)  \<circ>\<^sub>c  left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,
  \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,
right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>)\<^sup>\<flat>  \<circ>\<^sub>c (id\<^sub>c(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor)"
      also have "... = successor \<circ>\<^sub>c (add_uncurried \<circ>\<^sub>c
(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) \<circ>\<^sub>c \<langle>
(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)  \<circ>\<^sub>c 
(left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c
 (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<rangle>\<rangle>)"

(*And by taking sharps of both sides we arrive at*)
        have "((add_uncurried \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried)  \<circ>\<^sub>c
 \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)  \<circ>\<^sub>c  left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,
  \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,
right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor)
 =  successor\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>\<^sub>f \<circ>\<^sub>c (add_uncurried \<circ>\<^sub>c
(id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) \<circ>\<^sub>c \<langle>
(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)  \<circ>\<^sub>c 
(left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c),
\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c
 (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<rangle>\<rangle>)\<^sup>\<sharp>"

(*That is, this function causes the square to commute.
Now we show that (add o (add x id))# does this as well.*)

(*Bottom of page 9*)
    have "add_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) 
 \<circ>\<^sub>c (id\<^sub>c(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle> = 
add_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,successor  \<circ>\<^sub>c c\<rangle>"
    also have "... = add_uncurried \<circ>\<^sub>c \<langle>
  add_uncurried \<circ>\<^sub>c \<langle>a,b\<rangle>, successor \<circ>\<^sub>c  c\<rangle>"
    also have "... = (a +\<^sub>\<nat> b) +\<^sub>\<nat> (successor \<circ>\<^sub>c  c)"
    also have "... = successor \<circ>\<^sub>c ((a +\<^sub>\<nat> b) +\<^sub>\<nat> c)"
    also have "... = successor \<circ>\<^sub>c (add_uncurried \<circ>\<^sub>c
\<langle>add_uncurried \<circ>\<^sub>c \<langle>a,b\<rangle>,c\<rangle>)"
    also have "... = successor \<circ>\<^sub>c (add_uncurried \<circ>\<^sub>c 
(add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>"

(*Top of page 9... "It follows that" *)

      have "((add_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> 
\<circ>\<^sub>c successor)\<^sup>\<flat> = (successor \<circ>\<^sub>c (add_uncurried \<circ>\<^sub>c 
(add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>)\<^sup>\<flat> \<circ>\<^sub>c (id\<^sub>c(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<times>\<^sub>f successor)"
        also have "... = 
successor \<circ>\<^sub>c (add_uncurried \<circ>\<^sub>c 
(add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))"

(*By taking sharps we arrive at *)
          have " successor\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)\<^esup>\<^sub>f \<circ>\<^sub>c
((add_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp>
 = (add_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c))\<^sup>\<sharp> 
\<circ>\<^sub>c successor"

(*Therefore ... causes the square to commmute as well...*)

            have "add_uncurried \<circ>\<^sub>c (add_uncurried \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)
 = "add_uncurried \<circ>\<^sub>c ( id\<^sub>c (\<nat>\<^sub>c\<times>\<^sub>c\<nat>\<^sub>c) \<times>\<^sub>f add_uncurried) \<circ>\<^sub>c
 \<langle>(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)  \<circ>\<^sub>c  left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,
  \<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c,
right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c\<rangle>\<rangle>"

(*Finally, we have that... *)

have "a +\<^sub>\<nat> (b +\<^sub>\<nat> c)  = add_uncurried \<circ>\<^sub>c \<langle>a, add_uncurried \<circ>\<^sub>c \<langle>b,c\<rangle>\<rangle>"
also have "... = add_uncurried \<circ>\<^sub>c ( id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) 
 \<circ>\<^sub>c \<langle>a,\<langle>b,c\<rangle>\<rangle>" 
also have "... = add_uncurried \<circ>\<^sub>c ( id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) 
\<circ>\<^sub>c \<langle>a,\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>a,b\<rangle>     ,c\<rangle>\<rangle>"
also have "... = 
add_uncurried \<circ>\<^sub>c ( id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) 
\<circ>\<^sub>c \<langle> (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>a,b\<rangle>
,\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)  \<circ>\<^sub>c
(left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)
 \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>    ,
(right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle> \<rangle>\<rangle>"
also have "... = 
add_uncurried \<circ>\<^sub>c ( id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) 
\<circ>\<^sub>c \<langle> (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c
 \<langle>\<langle>a,b\<rangle>,c\<rangle>
,\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)  \<circ>\<^sub>c
(left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)
 \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle>    ,
(right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)
\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle> \<rangle>\<rangle>"
also have "... = 
add_uncurried \<circ>\<^sub>c ( id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) 
\<circ>\<^sub>c \<langle> (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c
 \<langle>\<langle>a,b\<rangle>,c\<rangle>
,\<langle>(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c)  \<circ>\<^sub>c
(left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)
    ,
(right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c)
 \<rangle>\<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>,c\<rangle> \<rangle>"
also have "... = 
add_uncurried \<circ>\<^sub>c ( id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f add_uncurried) 
\<circ>\<^sub>c \<langle> (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<nat>\<^sub>c) \<circ>\<^sub>c

  oops

end