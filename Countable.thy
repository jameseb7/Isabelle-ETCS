theory Countable
  imports  Parity Inequality
begin


(* Definition 2.6.12 *)
definition fixed_point :: "cfunc \<Rightarrow> cfunc \<Rightarrow> bool" where
  "fixed_point a g \<longleftrightarrow> (\<exists> A. g : A \<rightarrow> A \<and> a \<in>\<^sub>c A \<and> g \<circ>\<^sub>c a = g)"
definition has_fixed_point :: "cfunc \<Rightarrow> bool" where
  "has_fixed_point g \<longleftrightarrow> (\<exists> a. fixed_point a g)"
definition fixed_point_property :: "cset \<Rightarrow> bool" where
  "fixed_point_property A \<longleftrightarrow> (\<forall> g. g : A \<rightarrow> A \<longrightarrow> has_fixed_point g)"

(* Definition 2.6.9 *)
definition epi_countable :: "cset \<Rightarrow> bool" where
  "epi_countable X \<longleftrightarrow> (\<exists> f. f : \<nat>\<^sub>c \<rightarrow> X \<and> epimorphism f)"

lemma emptyset_is_not_epi_countable:
  "\<not> (epi_countable \<emptyset>)"
  using comp_type emptyset_is_empty epi_countable_def zero_type by blast


(*Better  Definition 2.6.9 *)
definition countable :: "cset \<Rightarrow> bool" where
  "countable X \<longleftrightarrow> (\<exists> f. f : X \<rightarrow> \<nat>\<^sub>c \<and> monomorphism f)"

lemma epi_countable_is_countable: 
  assumes "epi_countable X"
  shows "countable X"
  using assms countable_def epi_countable_def epis_give_monos by blast



lemma emptyset_is_countable:
  "countable \<emptyset>"
  using countable_def empty_subset subobject_of_def2 by blast

lemma natural_numbers_are_countably_infinite:
  "(countable \<nat>\<^sub>c) \<and> (is_infinite \<nat>\<^sub>c)"
  by (meson CollectI Peano's_Axioms countable_def injective_imp_monomorphism is_infinite_def successor_type)


lemma iso_to_N_is_countably_infinite:
  assumes "X \<cong> \<nat>\<^sub>c"
  shows "(countable X) \<and> (is_infinite X)"
  by (meson assms countable_def is_isomorphic_def is_smaller_than_def iso_imp_epi_and_monic isomorphic_is_symmetric larger_than_infinite_is_infinite natural_numbers_are_countably_infinite)
  




lemma countably_infinite_iso_N:
  assumes "countable X"
  assumes "is_infinite X"
  shows "X \<cong> \<nat>\<^sub>c"
  sorry



lemma iterative_injective_peeling:
  assumes "g : X \<rightarrow> X"
  assumes "k \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "x \<in>\<^sub>c X"
  assumes "y \<in>\<^sub>c X"
  assumes "injective g"
  assumes "(g\<^bsup>\<circ>k\<^esup>) \<circ>\<^sub>c x =(g\<^bsup>\<circ>k\<^esup>) \<circ>\<^sub>c y"
  shows "x=y"
proof - 
  have "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>eval_func X X \<circ>\<^sub>c \<langle> x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, ITER X \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<rangle>,
                                  eval_func X X \<circ>\<^sub>c \<langle>y \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, ITER X \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>,
                   eq_pred X \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,y \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
  proof(rule natural_number_object_func_unique[where X = \<Omega>, where f = "id \<Omega>"])
    show "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>eval_func X X \<circ>\<^sub>c  \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER X \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>,eval_func X X \<circ>\<^sub>c \<langle>y \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER X \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>,eq_pred X \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,y \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
      using assms by typecheck_cfuncs
    show "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
      by typecheck_cfuncs
    show "id\<^sub>c \<Omega> : \<Omega> \<rightarrow> \<Omega>"
      by typecheck_cfuncs
  next
    have "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>eval_func X X \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER X \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>,
                                    eval_func X X \<circ>\<^sub>c \<langle>y \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER X \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>,
                      eq_pred X \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,y \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c  zero =
          IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>eval_func X X \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<circ>\<^sub>c  zero,ITER X \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<circ>\<^sub>c  zero,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  zero\<rangle>\<rangle>,
                                   eval_func X X \<circ>\<^sub>c \<langle>y \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c  zero,ITER X \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<circ>\<^sub>c  zero ,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  zero\<rangle>\<rangle>\<rangle>,
                      eq_pred X \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<circ>\<^sub>c  zero,y \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c  zero\<rangle>\<rangle>"
      using assms by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2)
    also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>eval_func X X \<circ>\<^sub>c \<langle>x ,ITER X \<circ>\<^sub>c \<langle>metafunc g ,  zero\<rangle>\<rangle>,
                                              eval_func X X \<circ>\<^sub>c \<langle>y ,ITER X \<circ>\<^sub>c \<langle>metafunc g , zero\<rangle>\<rangle>\<rangle>,
                                eq_pred X \<circ>\<^sub>c \<langle>x ,y \<rangle>\<rangle>"
      using assms by (typecheck_cfuncs, smt (z3) id_left_unit2 id_right_unit2 id_type terminal_func_unique)
    also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>x, y\<rangle>,eq_pred X \<circ>\<^sub>c \<langle>x ,y \<rangle>\<rangle>"
      using assms by (typecheck_cfuncs, smt (z3) eval_lemma_for_ITER id_left_unit2 zero_iters)
    also have "... = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero"
      using assms by (typecheck_cfuncs, smt (z3) comp_associative2 id_right_unit2 implies_implies_IMPLIES terminal_func_comp_elem)
    then show "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>eval_func X X \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER X \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>,eval_func X X \<circ>\<^sub>c \<langle>y \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER X \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>,eq_pred X \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,y \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c zero = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero"
      by (simp add: calculation)
  next
    show "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>eval_func X X \<circ>\<^sub>c  \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER X \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>,
                                    eval_func X X \<circ>\<^sub>c  \<langle>y \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER X \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>,
                      eq_pred X \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,y \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c successor = 
  id\<^sub>c \<Omega> \<circ>\<^sub>c IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>eval_func X X \<circ>\<^sub>c  \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER X \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>,
                                    eval_func X X \<circ>\<^sub>c  \<langle>y \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER X \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>,
                      eq_pred X \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,y \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>"
    proof(rule one_separator[where X = "\<nat>\<^sub>c", where Y = \<Omega>])
      show "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>eval_func X X \<circ>\<^sub>c  \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER X \<circ>\<^sub>c  \<langle>metafunc g \<circ>\<^sub>c  \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>,
                                      eval_func X X \<circ>\<^sub>c \<langle>y \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER X \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>,
                         eq_pred X \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,y \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<Omega>"
        using assms by typecheck_cfuncs
      show "id\<^sub>c \<Omega> \<circ>\<^sub>c IMPLIES \<circ>\<^sub>c  \<langle>eq_pred X \<circ>\<^sub>c \<langle>eval_func X X \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER X \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>,
                                               eval_func X X \<circ>\<^sub>c \<langle>y \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER X \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>,
                                 eq_pred X \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,y \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
        using assms by typecheck_cfuncs
    next
      fix n 
      assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
      
      have "((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>eval_func X X \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER X \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>,
                                       eval_func X X \<circ>\<^sub>c \<langle>y \<circ>\<^sub>c\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER X \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>,
                          eq_pred X \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,y \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c  successor) \<circ>\<^sub>c  n =
            IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>eval_func X X \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<circ>\<^sub>c (successor \<circ>\<^sub>c  n),ITER X \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<circ>\<^sub>c (successor \<circ>\<^sub>c  n),id\<^sub>c \<nat>\<^sub>c\<circ>\<^sub>c (successor \<circ>\<^sub>c  n)\<rangle>\<rangle>,
                                     eval_func X X \<circ>\<^sub>c \<langle>y \<circ>\<^sub>c\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<circ>\<^sub>c (successor \<circ>\<^sub>c  n),ITER X \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<circ>\<^sub>c (successor \<circ>\<^sub>c  n),id\<^sub>c \<nat>\<^sub>c\<circ>\<^sub>c (successor \<circ>\<^sub>c  n)\<rangle>\<rangle>\<rangle>,
                       eq_pred X \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<circ>\<^sub>c (successor \<circ>\<^sub>c  n),y \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c (successor \<circ>\<^sub>c  n)\<rangle>\<rangle>"
        using assms by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2)
      also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>eval_func X X \<circ>\<^sub>c \<langle>x ,ITER X \<circ>\<^sub>c \<langle>metafunc g ,successor \<circ>\<^sub>c  n\<rangle>\<rangle>,
                                                eval_func X X \<circ>\<^sub>c \<langle>y ,ITER X \<circ>\<^sub>c \<langle>metafunc g , successor \<circ>\<^sub>c  n\<rangle>\<rangle>\<rangle>,
                                   eq_pred X \<circ>\<^sub>c \<langle>x ,y \<rangle>\<rangle>"
        using assms by (typecheck_cfuncs, smt (z3) id_left_unit2 id_right_unit2 id_type terminal_func_unique)
      also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c  \<langle>(g\<^bsup>\<circ>successor \<circ>\<^sub>cn\<^esup>) \<circ>\<^sub>c x,
                                                 (g\<^bsup>\<circ>successor \<circ>\<^sub>cn\<^esup>) \<circ>\<^sub>c y\<rangle>,
                                   eq_pred X \<circ>\<^sub>c \<langle>x ,y \<rangle>\<rangle>"
        using assms eval_lemma_for_ITER by (typecheck_cfuncs, presburger)
      also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c  \<langle>g \<circ>\<^sub>c (g\<^bsup>\<circ>n\<^esup>) \<circ>\<^sub>c x,
                                                 g \<circ>\<^sub>c (g\<^bsup>\<circ>n\<^esup>) \<circ>\<^sub>c y\<rangle>,
                                   eq_pred X \<circ>\<^sub>c \<langle>x ,y \<rangle>\<rangle>"
        using assms comp_associative2 succ_iters by (typecheck_cfuncs, force)
      also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c  \<langle>(g\<^bsup>\<circ>n\<^esup>) \<circ>\<^sub>c x,
                                                 (g\<^bsup>\<circ>n\<^esup>) \<circ>\<^sub>c y\<rangle>,
                                   eq_pred X \<circ>\<^sub>c \<langle>x ,y \<rangle>\<rangle>"
        using assms by (typecheck_cfuncs, smt (verit, best) assms(5) eq_pred_iff_eq implies_implies_IMPLIES injective_imp_monomorphism mem_Collect_eq monomorphism_def3)
      also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c  \<langle>eval_func X X \<circ>\<^sub>c \<langle>x ,ITER X \<circ>\<^sub>c  \<langle>metafunc g ,n\<rangle>\<rangle>,
                                                 eval_func X X \<circ>\<^sub>c \<langle>y ,ITER X \<circ>\<^sub>c  \<langle>metafunc g ,n\<rangle>\<rangle>\<rangle>,
                                 eq_pred X \<circ>\<^sub>c \<langle>x ,y \<rangle>\<rangle>"
        using assms eval_lemma_for_ITER by (typecheck_cfuncs, presburger)
      also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c  \<langle>eval_func X X \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<circ>\<^sub>c n,ITER X \<circ>\<^sub>c  \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<circ>\<^sub>c n,id\<^sub>c \<nat>\<^sub>c\<circ>\<^sub>c n\<rangle>\<rangle>,
                                                eval_func X X \<circ>\<^sub>c \<langle>y \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<circ>\<^sub>c n,ITER X \<circ>\<^sub>c  \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<circ>\<^sub>c n,id\<^sub>c \<nat>\<^sub>c\<circ>\<^sub>c n\<rangle>\<rangle>\<rangle>,
                                 eq_pred X \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<circ>\<^sub>c n,y \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c n\<rangle>\<rangle>"
        using assms by (typecheck_cfuncs, smt (z3) id_left_unit2 id_right_unit2 id_type one_unique_element)
      also have "... = (id\<^sub>c \<Omega> \<circ>\<^sub>c IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c  \<langle>eval_func X X \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER X \<circ>\<^sub>c  \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>,
                                                eval_func X X \<circ>\<^sub>c \<langle>y \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER X \<circ>\<^sub>c  \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>,
                                 eq_pred X \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,y \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c n"
        using assms by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2 id_left_unit2)
      then show "((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>eval_func X X \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER X \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>,eval_func X X \<circ>\<^sub>c \<langle>y \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER X \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>,eq_pred X \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,y \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c successor) \<circ>\<^sub>c  n = 
         (id\<^sub>c \<Omega> \<circ>\<^sub>c IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>eval_func X X \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c  \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER X \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>,eval_func X X \<circ>\<^sub>c \<langle>y \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER X \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>,eq_pred X \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,y \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle>) \<circ>\<^sub>c n"
        using calculation by auto
    qed
    show "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor = id\<^sub>c \<Omega> \<circ>\<^sub>c \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
      by (typecheck_cfuncs, smt (z3) comp_associative2 id_left_unit2 terminal_func_comp)
  qed
  then have "\<t> = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>eval_func X X \<circ>\<^sub>c \<langle> x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, ITER X \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<rangle>,
                                          eval_func X X \<circ>\<^sub>c \<langle>y \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, ITER X \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>,
                            eq_pred X \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,y \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle> \<circ>\<^sub>c k"
    using assms by (typecheck_cfuncs, smt (z3) comp_associative2 id_right_unit2 terminal_func_comp_elem)
  also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>eval_func X X \<circ>\<^sub>c \<langle> x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<circ>\<^sub>c k, ITER X \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<circ>\<^sub>c k, id \<nat>\<^sub>c\<circ>\<^sub>c k\<rangle>\<rangle>,
                                            eval_func X X \<circ>\<^sub>c \<langle>y \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<circ>\<^sub>c k, ITER X \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<circ>\<^sub>c k, id \<nat>\<^sub>c\<circ>\<^sub>c k\<rangle>\<rangle>\<rangle>,
                               eq_pred X \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<circ>\<^sub>c k,y \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<circ>\<^sub>c k\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2)
  also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>eval_func X X \<circ>\<^sub>c \<langle> x, ITER X \<circ>\<^sub>c \<langle>metafunc g, k\<rangle>\<rangle>,
                                            eval_func X X \<circ>\<^sub>c \<langle>y, ITER X \<circ>\<^sub>c \<langle>metafunc g, k\<rangle>\<rangle>\<rangle>,
                               eq_pred X \<circ>\<^sub>c \<langle>x,y\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2 terminal_func_comp_elem)
  also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>(g\<^bsup>\<circ>k\<^esup>) \<circ>\<^sub>c x ,(g\<^bsup>\<circ>k\<^esup>) \<circ>\<^sub>c y\<rangle>,
                               eq_pred X \<circ>\<^sub>c \<langle>x,y\<rangle>\<rangle>"
    using assms eval_lemma_for_ITER by (typecheck_cfuncs, auto)
  also have "... = IMPLIES \<circ>\<^sub>c \<langle>\<t>, eq_pred X \<circ>\<^sub>c \<langle>x,y\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, metis assms(6) eq_pred_iff_eq)
  then have "eq_pred X \<circ>\<^sub>c \<langle>x,y\<rangle> = \<t>"
    using assms by (typecheck_cfuncs, metis (no_types) IMPLIES_elim' calculation)
  then show "x = y"
    using assms by (simp add:  eq_pred_iff_eq)
qed


lemma iterative_injective_peeling':
  assumes "g : X \<rightarrow> X"
  assumes "k \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "p \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "x \<in>\<^sub>c X"
  assumes "y \<in>\<^sub>c X"
  assumes "injective g"
  assumes "(g\<^bsup>\<circ>k +\<^sub>\<nat> p\<^esup>) \<circ>\<^sub>c x =(g\<^bsup>\<circ>k\<^esup>) \<circ>\<^sub>c y"
  shows "(g\<^bsup>\<circ>p\<^esup>) \<circ>\<^sub>c x=y"
  sorry


definition canonically_finite_set :: "cfunc \<Rightarrow> cset" ("[_]\<^sub>c")where 
  "canonically_finite_set n = (SOME E. \<exists> m. n \<in>\<^sub>c \<nat>\<^sub>c \<and> equalizer E m (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) (leq \<circ>\<^sub>c \<langle>successor, n  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>))"

lemma canonically_finite_set_def2:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "\<exists>m. equalizer (canonically_finite_set n) m (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) (leq \<circ>\<^sub>c \<langle>successor, n  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>)"
  unfolding canonically_finite_set_def using assms  
  by (typecheck_cfuncs, smt (z3) equalizer_exists someI_ex)


definition canonically_finite_morphism :: "cfunc \<Rightarrow> cfunc" where
 "canonically_finite_morphism n = (SOME m.  n \<in>\<^sub>c \<nat>\<^sub>c \<and> equalizer (canonically_finite_set n) m (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) (leq \<circ>\<^sub>c \<langle>successor, n  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>))"

lemma canonically_finite_morphism_def2: 
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows  "equalizer (canonically_finite_set n) (canonically_finite_morphism n) (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) (leq \<circ>\<^sub>c \<langle>successor, n  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>)"
  unfolding canonically_finite_morphism_def using assms  
  by (typecheck_cfuncs, meson canonically_finite_set_def2 someI_ex)

lemma canonically_finite_morphism_type[type_rule]:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "canonically_finite_morphism n : [n]\<^sub>c \<rightarrow> \<nat>\<^sub>c"
proof- 
  have "equalizer (canonically_finite_set n) (canonically_finite_morphism n) (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) (leq \<circ>\<^sub>c \<langle>successor, n  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>)"
    by (simp add: assms canonically_finite_morphism_def2)
  then show ?thesis
    unfolding equalizer_def by (-,typecheck_cfuncs, metis cfunc_type_def)
qed


lemma canonically_finite_morph_mono:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "monomorphism(canonically_finite_morphism n)"
  by (meson canonically_finite_morphism_def2 equalizer_is_monomorphism assms)

lemma member_canonically_finite_set:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "x  \<in>\<^sub>c [n]\<^sub>c"
  shows "leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c (canonically_finite_morphism n) \<circ>\<^sub>c x  , n\<rangle> = \<t>"
proof - 
  have "leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c (canonically_finite_morphism n) \<circ>\<^sub>c x  , n\<rangle> = (leq \<circ>\<^sub>c \<langle>successor  , n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c (canonically_finite_morphism n) \<circ>\<^sub>c x"
    using assms by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2 id_right_unit2 terminal_func_comp_elem)
  also have "... =  (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c (canonically_finite_morphism n) \<circ>\<^sub>c x"
    using assms canonically_finite_morphism_def2 unfolding equalizer_def by (-,typecheck_cfuncs, smt comp_associative2)
  also have "... = \<t>"
    using assms by (typecheck_cfuncs, smt comp_associative2 id_right_unit2 terminal_func_comp_elem)
  then show ?thesis
    using calculation by auto
qed


  

lemma member_canonically_finite_set2:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(successor \<circ>\<^sub>c m \<le>\<^sub>\<nat> n) = (m \<in>\<^bsub>\<nat>\<^sub>c\<^esub> ([n]\<^sub>c, (canonically_finite_morphism n)))"
proof(auto)
  assume "successor \<circ>\<^sub>c m \<le>\<^sub>\<nat> n"
  then have "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>)\<circ>\<^sub>c m = (leq \<circ>\<^sub>c \<langle>successor  , n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c m" 
    using assms by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2 id_right_unit2 leq_infix_def terminal_func_comp_elem)
  then have "m factorsthru (canonically_finite_morphism n)"
    using assms xfactorthru_equalizer_iff_fx_eq_gx canonically_finite_morphism_def2 by (-,typecheck_cfuncs, blast)
  then show "(m \<in>\<^bsub>\<nat>\<^sub>c\<^esub> ([n]\<^sub>c, (canonically_finite_morphism n)))"
    using assms by (typecheck_cfuncs, simp add: canonically_finite_morph_mono relative_member_def2)
next
  assume "m \<in>\<^bsub>\<nat>\<^sub>c\<^esub> ([n]\<^sub>c, canonically_finite_morphism n)"
  then have "m factorsthru (canonically_finite_morphism n)"
    by (simp add: relative_member_def2)
  then have fm_eq_gm: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>)\<circ>\<^sub>c m = (leq \<circ>\<^sub>c \<langle>successor  , n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c m"
    using assms by (typecheck_cfuncs, meson canonically_finite_morphism_def2 xfactorthru_equalizer_iff_fx_eq_gx)
  show "successor \<circ>\<^sub>c m \<le>\<^sub>\<nat> n"
  proof - 
    have "\<t> = (leq \<circ>\<^sub>c \<langle>successor  , n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c m"
      using assms by (typecheck_cfuncs, metis comp_associative2 fm_eq_gm id_right_unit2 terminal_func_comp_elem)
    also have "... = leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c m , n\<rangle>"
      using assms by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2 id_right_unit2 terminal_func_comp_elem)
    then show ?thesis
      by (simp add: calculation leq_infix_def)
  qed
qed


lemma member_canonically_finite_set3:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(n \<le>\<^sub>\<nat> m) = (\<not>(m \<in>\<^bsub>\<nat>\<^sub>c\<^esub> ([n]\<^sub>c, (canonically_finite_morphism n))))"
proof(auto)
  assume "n \<le>\<^sub>\<nat> m"
  then have "\<not>(successor \<circ>\<^sub>c m \<le>\<^sub>\<nat> n)"
    using assms by (simp add: nat_strict_total_order)
  then show "m \<in>\<^bsub>\<nat>\<^sub>c\<^esub> ([n]\<^sub>c, canonically_finite_morphism n) \<Longrightarrow> False"
    using assms member_canonically_finite_set2 by blast
next
  assume "\<not> m \<in>\<^bsub>\<nat>\<^sub>c\<^esub> ([n]\<^sub>c, canonically_finite_morphism n)"
  then have "\<not>(successor \<circ>\<^sub>c m \<le>\<^sub>\<nat> n)"
    using assms by (simp add: member_canonically_finite_set2)
  then show "n \<le>\<^sub>\<nat> m"
    using assms by (typecheck_cfuncs, simp add: nat_strict_total_order)
qed






definition elem_canon_finite_set :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" ("\<lbrakk>_:_\<rbrakk>\<^sub>c")where 
  "elem_canon_finite_set m n = (THE E. m \<in>\<^sub>c \<nat>\<^sub>c \<and> n \<in>\<^sub>c \<nat>\<^sub>c \<and> (successor \<circ>\<^sub>c m \<le>\<^sub>\<nat> n )
                                                         \<and> E \<in>\<^sub>c canonically_finite_set n
                                                         \<and> (canonically_finite_morphism n) \<circ>\<^sub>c E = m)"


lemma elem_canon_finite_set[type_rule]:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "(successor \<circ>\<^sub>c m \<le>\<^sub>\<nat> n)"
  shows "\<lbrakk>m:n\<rbrakk>\<^sub>c \<in>\<^sub>c [n]\<^sub>c"
proof - 
  obtain E where E_type[type_rule]: "E \<in>\<^sub>c [n]\<^sub>c" and E_def: "(canonically_finite_morphism n) \<circ>\<^sub>c E = m"
    using assms  
    by (metis assms(3) cfunc_type_def factors_through_def member_canonically_finite_set2 relative_member_def2)
  then show ?thesis
    using assms unfolding elem_canon_finite_set_def  
    by (typecheck_cfuncs, smt (verit, del_insts)  assms(3) canonically_finite_morph_mono monomorphism_def3 theI')
qed



lemma elem_canon_finite_def2:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "(successor \<circ>\<^sub>c m \<le>\<^sub>\<nat> n)"
  shows "(canonically_finite_morphism n) \<circ>\<^sub>c \<lbrakk>m:n\<rbrakk>\<^sub>c = m"
proof - 
  obtain E where E_type[type_rule]: "E \<in>\<^sub>c [n]\<^sub>c" and E_def: "(canonically_finite_morphism n) \<circ>\<^sub>c E = m"
    using assms  
    by (metis assms(3) cfunc_type_def factors_through_def member_canonically_finite_set2 relative_member_def2)
  then show ?thesis
    using assms unfolding elem_canon_finite_set_def   
    by (typecheck_cfuncs, smt (verit, del_insts)  assms(3) canonically_finite_morph_mono monomorphism_def3 theI')
qed




lemma elem_canon_finite_set_representation:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "x \<in>\<^sub>c [n]\<^sub>c"
  shows "\<exists>! m. (m \<in>\<^sub>c \<nat>\<^sub>c \<and> (successor \<circ>\<^sub>c m \<le>\<^sub>\<nat> n) \<and> \<lbrakk>m:n\<rbrakk>\<^sub>c = x)"
proof(auto)
  show "\<exists>m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> successor \<circ>\<^sub>c m \<le>\<^sub>\<nat> n \<and> \<lbrakk>m:n\<rbrakk>\<^sub>c = x"
      using assms by (meson canonically_finite_morph_mono canonically_finite_morphism_type comp_type
          elem_canon_finite_def2 elem_canon_finite_set leq_infix_def member_canonically_finite_set 
          monomorphism_def3)
  show "\<And>m y. m \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> y \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> successor \<circ>\<^sub>c m \<le>\<^sub>\<nat> n \<Longrightarrow> x = \<lbrakk>m:n\<rbrakk>\<^sub>c \<Longrightarrow> successor \<circ>\<^sub>c y \<le>\<^sub>\<nat> n \<Longrightarrow> \<lbrakk>y:n\<rbrakk>\<^sub>c = \<lbrakk>m:n\<rbrakk>\<^sub>c \<Longrightarrow> m = y"
      by (smt assms elem_canon_finite_def2)
qed











lemma zero_canonically_finite_set_empty:
  "[zero]\<^sub>c \<cong> \<emptyset>"
  by (typecheck_cfuncs, metis is_empty_def canonically_finite_morphism_type comp_type leq_infix_def
      member_canonically_finite_set nat_strict_total_order no_el_iff_iso_0 zero_is_smallest)





lemma canonically_finite_sets_grow:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "m \<le>\<^sub>\<nat> n"
  shows "[m]\<^sub>c \<le>\<^sub>c [n]\<^sub>c"
proof -   
  have "                   (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c (canonically_finite_morphism m) =
        (leq \<circ>\<^sub>c \<langle>successor, n  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c(canonically_finite_morphism m)"
  proof(rule one_separator[where X = "[m]\<^sub>c", where Y = \<Omega>])
    show "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c canonically_finite_morphism m : [m]\<^sub>c \<rightarrow> \<Omega>"
      using assms by typecheck_cfuncs
    show "(leq \<circ>\<^sub>c \<langle>successor,n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c canonically_finite_morphism m : [m]\<^sub>c \<rightarrow> \<Omega>"
      using assms by typecheck_cfuncs
  next
    fix x 
    assume[type_rule]: "x \<in>\<^sub>c [m]\<^sub>c"
    then obtain k where k_type[type_rule]: "k \<in>\<^sub>c \<nat>\<^sub>c" and k_def: "((successor \<circ>\<^sub>c k \<le>\<^sub>\<nat> m) \<and> \<lbrakk>k:m\<rbrakk>\<^sub>c = x)"
      using assms by (meson elem_canon_finite_set_representation)
    then have "(canonically_finite_morphism n) \<circ>\<^sub>c \<lbrakk>k:n\<rbrakk>\<^sub>c = k"
      using assms by (meson assms(2) assms(3) elem_canon_finite_def2 k_def leq_infix_def leq_transitivity nat_strict_total_order)
    then show "((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c canonically_finite_morphism m) \<circ>\<^sub>c x =
         ((leq \<circ>\<^sub>c \<langle>successor,n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c canonically_finite_morphism m) \<circ>\<^sub>c x "
      using assms 
      by (typecheck_cfuncs,smt (z3) assms(3) cfunc_prod_comp comp_associative2 elem_canon_finite_def2 id_right_unit2
          k_def k_type leq_infix_def leq_transitivity succ_n_type terminal_func_comp_elem)
  qed
  then obtain \<iota> where \<iota>_type[type_rule]: "\<iota> : [m]\<^sub>c \<rightarrow> [n]\<^sub>c" and  \<iota>_def: "(canonically_finite_morphism n) \<circ>\<^sub>c \<iota> = (canonically_finite_morphism m)"
    using assms by (metis canonically_finite_morphism_def2 cfunc_type_def equalizer_def)
   show ?thesis
    using assms 
    by (metis \<iota>_def \<iota>_type canonically_finite_morph_mono canonically_finite_morphism_type comp_monic_imp_monic' is_smaller_than_def)
qed



definition canonical_finite_inclusion :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc"  where 
  "canonical_finite_inclusion m n = (THE \<iota>. m \<in>\<^sub>c \<nat>\<^sub>c \<and> n \<in>\<^sub>c \<nat>\<^sub>c \<and> m \<le>\<^sub>\<nat> n  \<and> \<iota> : [m]\<^sub>c \<rightarrow> [n]\<^sub>c \<and> monomorphism \<iota> \<and> 
                                            canonically_finite_morphism n \<circ>\<^sub>c \<iota> = canonically_finite_morphism m)"



lemma canonical_finite_inclusion_def2: 
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "m \<le>\<^sub>\<nat> n"
  shows "m \<in>\<^sub>c \<nat>\<^sub>c \<and> n \<in>\<^sub>c \<nat>\<^sub>c \<and> m \<le>\<^sub>\<nat> n  \<and> canonical_finite_inclusion m n : [m]\<^sub>c \<rightarrow> [n]\<^sub>c \<and> monomorphism (canonical_finite_inclusion m n) \<and> 
                                            canonically_finite_morphism n \<circ>\<^sub>c canonical_finite_inclusion m n = canonically_finite_morphism m"
proof - 
  have "equalizer (canonically_finite_set n) (canonically_finite_morphism n) (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) (leq \<circ>\<^sub>c \<langle>successor, n  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>)"
    by (meson assms(1) canonically_finite_morphism_def2)
  then have "(\<forall> h F. ((h : F \<rightarrow> \<nat>\<^sub>c) \<and> ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c h = (leq \<circ>\<^sub>c \<langle>successor, n  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c h)) \<longrightarrow> (\<exists>! k. (k : F \<rightarrow> [n]\<^sub>c) \<and> canonically_finite_morphism n  \<circ>\<^sub>c k = h))"
    using assms by (typecheck_cfuncs, simp add: equalizer_def2)
  also have "(canonically_finite_morphism m : [m]\<^sub>c \<rightarrow> \<nat>\<^sub>c \<and> ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c (canonically_finite_morphism m) = (leq \<circ>\<^sub>c \<langle>successor, n  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c (canonically_finite_morphism m)))"
  proof(auto)
    show "canonically_finite_morphism m : [m]\<^sub>c \<rightarrow> \<nat>\<^sub>c"
      using assms by typecheck_cfuncs
  next
    show "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c canonically_finite_morphism m = (leq \<circ>\<^sub>c \<langle>successor,n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c canonically_finite_morphism m"
    proof(rule one_separator[where X ="[m]\<^sub>c", where Y = \<Omega>])
      show "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c canonically_finite_morphism m : [m]\<^sub>c \<rightarrow> \<Omega>"
        using assms by typecheck_cfuncs
      show "(leq \<circ>\<^sub>c \<langle>successor,n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c canonically_finite_morphism m : [m]\<^sub>c \<rightarrow> \<Omega>"
        using assms by typecheck_cfuncs
    next
      fix x
      assume x_type[type_rule]: "x \<in>\<^sub>c [m]\<^sub>c"
      have "successor \<circ>\<^sub>c canonically_finite_morphism m \<circ>\<^sub>c x \<le>\<^sub>\<nat>  m"
        using assms unfolding leq_infix_def by (typecheck_cfuncs, simp add: member_canonically_finite_set)
      then have f1: "successor \<circ>\<^sub>c canonically_finite_morphism m \<circ>\<^sub>c x \<le>\<^sub>\<nat> n"
        using assms by (typecheck_cfuncs, meson assms(3) leq_infix_def leq_transitivity)
      have  "((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c canonically_finite_morphism m) \<circ>\<^sub>c x = \<t>"
        using assms  
        by (typecheck_cfuncs, smt (z3) comp_associative2 id_right_unit2 id_type one_unique_element terminal_func_comp terminal_func_type)
      also have "... =  ((leq \<circ>\<^sub>c \<langle>successor,n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c canonically_finite_morphism m) \<circ>\<^sub>c x"
        using assms using f1 unfolding leq_infix_def 
        by (etcs_assocr, typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2 f1 id_right_unit2 leq_infix_def terminal_func_comp_elem)
      then show "((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c canonically_finite_morphism m) \<circ>\<^sub>c x = ((leq \<circ>\<^sub>c \<langle>successor,n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c canonically_finite_morphism m) \<circ>\<^sub>c x"
        using calculation by auto
    qed
  qed
  then have unique_map: "\<exists>! k. (k : [m]\<^sub>c \<rightarrow> [n]\<^sub>c) \<and> canonically_finite_morphism n  \<circ>\<^sub>c k = canonically_finite_morphism m"
    using calculation by auto
   show ?thesis
     unfolding canonical_finite_inclusion_def by(rule theI',
         metis unique_map  assms canonically_finite_morph_mono canonically_finite_morphism_type comp_monic_imp_monic')
qed





lemma canonical_finite_inclusion_type[type_rule]:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "m \<le>\<^sub>\<nat> n"
  shows "canonical_finite_inclusion m n : [m]\<^sub>c \<rightarrow> [n]\<^sub>c"
  by (simp add: assms canonical_finite_inclusion_def2)

lemma canonical_finite_inclusion_mono:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "m \<le>\<^sub>\<nat> n"
  shows "monomorphism (canonical_finite_inclusion m n)"
  by (simp add: assms canonical_finite_inclusion_def2)

lemma canonical_finite_morph_inclu_eq:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "m \<le>\<^sub>\<nat> n"
  shows "canonically_finite_morphism n \<circ>\<^sub>c canonical_finite_inclusion m n = canonically_finite_morphism m"
  by (simp add: assms canonical_finite_inclusion_def2)


lemma canonical_finite_inclusion_on_elements:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "k \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "successor \<circ>\<^sub>c k \<le>\<^sub>\<nat> m"
  assumes "m \<le>\<^sub>\<nat> n"
  shows "(canonical_finite_inclusion m n) \<circ>\<^sub>c \<lbrakk>k: m\<rbrakk>\<^sub>c = \<lbrakk>k: n\<rbrakk>\<^sub>c"
  using assms  
  by (typecheck_cfuncs, smt (verit, ccfv_SIG) canonical_finite_morph_inclu_eq canonically_finite_morphism_type comp_associative2 elem_canon_finite_def2 elem_canon_finite_set_representation)






lemma inclusion_characteristic_on_els: 
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "m \<le>\<^sub>\<nat> n"
  assumes "k \<in>\<^sub>c [n]\<^sub>c"
  shows "(k \<in>\<^bsub>[n]\<^sub>c\<^esub> ([m]\<^sub>c, canonical_finite_inclusion m n)) = (characteristic_func (canonical_finite_inclusion m n) \<circ>\<^sub>c k = \<t>)"
  using assms by (typecheck_cfuncs, meson canonical_finite_inclusion_def2 characteristic_func_false_not_relative_member characteristic_func_true_relative_member true_false_only_truth_values)


lemma inclusion_characteristic_on_els2:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "m \<le>\<^sub>\<nat> n"
  assumes "k \<in>\<^sub>c [n]\<^sub>c"
  shows "(k \<in>\<^bsub>[n]\<^sub>c\<^esub> ([m]\<^sub>c, canonical_finite_inclusion m n)) = (successor  \<circ>\<^sub>c  canonically_finite_morphism n \<circ>\<^sub>c k \<le>\<^sub>\<nat>  m)" 
proof(auto)
  show "k \<in>\<^bsub>[n]\<^sub>c\<^esub> ([m]\<^sub>c, canonical_finite_inclusion m n) \<Longrightarrow> successor \<circ>\<^sub>c canonically_finite_morphism n \<circ>\<^sub>c k \<le>\<^sub>\<nat> m"
    by (typecheck_cfuncs, smt (z3) assms canonical_finite_morph_inclu_eq comp_associative2 factors_through_def2 leq_infix_def member_canonically_finite_set relative_member_def2)
  show "successor \<circ>\<^sub>c canonically_finite_morphism n \<circ>\<^sub>c k \<le>\<^sub>\<nat> m \<Longrightarrow> k \<in>\<^bsub>[n]\<^sub>c\<^esub> ([m]\<^sub>c, canonical_finite_inclusion m n)"
    by (typecheck_cfuncs, metis assms canonical_finite_inclusion_mono canonical_finite_inclusion_on_elements elem_canon_finite_def2 elem_canon_finite_set elem_canon_finite_set_representation factors_through_def2 relative_member_def2)
qed




lemma inclusion_characteristic_def:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "m \<le>\<^sub>\<nat> n"
  assumes "k \<in>\<^sub>c [n]\<^sub>c"
  shows "(characteristic_func (canonical_finite_inclusion m n) \<circ>\<^sub>c k = \<t>)  = (successor  \<circ>\<^sub>c  canonically_finite_morphism n \<circ>\<^sub>c k \<le>\<^sub>\<nat>  m)"
  using assms inclusion_characteristic_on_els inclusion_characteristic_on_els2 by force



lemma inclusion_characteristic_def2:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "k \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "successor \<circ>\<^sub>c k \<le>\<^sub>\<nat> n"
  assumes "m \<le>\<^sub>\<nat> n"
  shows "(characteristic_func (canonical_finite_inclusion m n) \<circ>\<^sub>c \<lbrakk>k: n\<rbrakk>\<^sub>c = \<t>)  = (successor \<circ>\<^sub>c k \<le>\<^sub>\<nat> m)"
  using assms elem_canon_finite_def2 inclusion_characteristic_def by (typecheck_cfuncs, presburger)



lemma inclusion_characteristic_def3:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "k \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "successor \<circ>\<^sub>c k \<le>\<^sub>\<nat> n"
  assumes "m \<le>\<^sub>\<nat> n"
  shows "(characteristic_func (canonical_finite_inclusion m n) \<circ>\<^sub>c \<lbrakk>k: n\<rbrakk>\<^sub>c = \<f>)  = (m \<le>\<^sub>\<nat> k)"
  using assms by (typecheck_cfuncs, metis canonical_finite_inclusion_mono inclusion_characteristic_def2 nat_strict_total_order true_false_distinct true_false_only_truth_values)








  

(*We probably want these still, but need to relocate them!*)






lemma size_2_sets:
"(X \<cong> \<Omega>) = (\<exists> x1. (\<exists> x2. ((x1 \<in>\<^sub>c X) \<and> (x2 \<in>\<^sub>c X) \<and> (x1\<noteq>x2) \<and> (\<forall>x. x \<in>\<^sub>c X \<longrightarrow> (x=x1) \<or> (x=x2))  )))"
proof 
  assume "X \<cong> \<Omega>"
  then obtain \<phi> where \<phi>_type[type_rule]: "\<phi> : X \<rightarrow> \<Omega>" and \<phi>_iso: "isomorphism \<phi>"
    using is_isomorphic_def by blast
  obtain x1 x2 where x1_type[type_rule]: "x1 \<in>\<^sub>c X" and x1_def: "\<phi> \<circ>\<^sub>c x1 = \<t>" and
                     x2_type[type_rule]: "x2 \<in>\<^sub>c X" and x2_def: "\<phi> \<circ>\<^sub>c x2 = \<f>" and
                     distinct: "x1 \<noteq> x2"
    by (typecheck_cfuncs, smt (z3) \<phi>_iso cfunc_type_def comp_associative comp_type id_left_unit2 isomorphism_def true_false_distinct)
  then show  "\<exists>x1 x2. x1 \<in>\<^sub>c X \<and> x2 \<in>\<^sub>c X \<and> x1 \<noteq> x2 \<and> (\<forall>x. x \<in>\<^sub>c X \<longrightarrow> x = x1 \<or> x = x2)"
    by (smt (verit, best)  \<phi>_iso \<phi>_type cfunc_type_def comp_associative2 comp_type id_left_unit2 isomorphism_def true_false_only_truth_values)
next
  assume exactly_two: "\<exists>x1 x2. x1 \<in>\<^sub>c X \<and> x2 \<in>\<^sub>c X \<and> x1 \<noteq> x2 \<and> (\<forall>x. x \<in>\<^sub>c X \<longrightarrow> x = x1 \<or> x = x2)"
  then obtain x1 x2  where x1_type[type_rule]: "x1 \<in>\<^sub>c X" and x2_type[type_rule]: "x2 \<in>\<^sub>c X" and distinct: "x1 \<noteq> x2"
    by force
  have iso_type: "((x1 \<amalg> x2) \<circ>\<^sub>c case_bool) : \<Omega> \<rightarrow> X"
    by typecheck_cfuncs
  have surj: "surjective ((x1 \<amalg> x2) \<circ>\<^sub>c case_bool)"
    by (typecheck_cfuncs, smt (verit, best) exactly_two cfunc_type_def coprod_case_bool_false
                coprod_case_bool_true distinct false_func_type surjective_def true_func_type)
  have inj: "injective ((x1 \<amalg> x2) \<circ>\<^sub>c case_bool)"
    by (typecheck_cfuncs, smt (verit, ccfv_SIG) distinct case_bool_true_and_false comp_associative2 
        coprod_case_bool_false injective_def2 left_coproj_cfunc_coprod true_false_only_truth_values)
  then have "isomorphism ((x1 \<amalg> x2) \<circ>\<^sub>c case_bool)"
    by (meson epi_mon_is_iso injective_imp_monomorphism singletonI surj surjective_is_epimorphism)
  then show "X \<cong> \<Omega>"
    using is_isomorphic_def iso_type isomorphic_is_symmetric by blast
qed





lemma size_2plus_sets:
  "(\<Omega>  \<le>\<^sub>c  X ) = (\<exists> x1. (\<exists> x2. ((x1 \<in>\<^sub>c X) \<and> (x2 \<in>\<^sub>c X) \<and> (x1\<noteq>x2)  )))"
proof(auto)
  show "\<Omega> \<le>\<^sub>c X \<Longrightarrow> \<exists>x1. x1 \<in>\<^sub>c X \<and> (\<exists>x2. x2 \<in>\<^sub>c X \<and> x1 \<noteq> x2)"
    by (meson comp_type false_func_type is_smaller_than_def monomorphism_def3 true_false_distinct true_func_type)
next
  fix x1 x2 
  assume x1_type[type_rule]: "x1 \<in>\<^sub>c X"
  assume x2_type[type_rule]: "x2 \<in>\<^sub>c X"
  assume distinct: "x1 \<noteq> x2"  
  have mono_type: "((x1 \<amalg> x2) \<circ>\<^sub>c case_bool) : \<Omega> \<rightarrow> X"
    by typecheck_cfuncs
  have inj: "injective ((x1 \<amalg> x2) \<circ>\<^sub>c case_bool)"
    by (typecheck_cfuncs, smt (verit, ccfv_SIG) distinct case_bool_true_and_false comp_associative2 
        coprod_case_bool_false injective_def2 left_coproj_cfunc_coprod true_false_only_truth_values)    
  then show "\<Omega> \<le>\<^sub>c X"
    using injective_imp_monomorphism is_smaller_than_def mono_type by blast
qed


    (*See "non_init_non_ter_sets" in the Cardinality.thy file.*)


lemma not_init_not_term:
  "(\<not>(initial_object X) \<and> \<not>(terminal_object X)) = (\<exists> x1. (\<exists> x2. ((x1 \<in>\<^sub>c X) \<and> (x2 \<in>\<^sub>c X) \<and> (x1\<noteq>x2)  )))"
by (metis is_empty_def initial_iso_empty iso_empty_initial iso_to1_is_term no_el_iff_iso_0 single_elem_iso_one terminal_object_def)

lemma sets_size_3_plus:
  "(\<not>(initial_object X) \<and> \<not>(terminal_object X) \<and> \<not>(X \<cong> \<Omega>)) = (\<exists> x1. (\<exists> x2.  \<exists> x3. ((x1 \<in>\<^sub>c X) \<and> (x2 \<in>\<^sub>c X) \<and>  (x3 \<in>\<^sub>c X) \<and> (x1\<noteq>x2) \<and>  (x2\<noteq>x3) \<and> (x1\<noteq>x3) )             ))"
by (metis not_init_not_term size_2_sets)



(*

lemma strange_elems_of_can_finite_sets:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "k \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "n \<le>\<^sub>\<nat> k"
  assumes  "\<lbrakk>k:n\<rbrakk>\<^sub>c \<in>\<^sub>c [n]\<^sub>c"
  shows "\<exists>! m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> successor \<circ>\<^sub>c m \<le>\<^sub>\<nat> n \<and> \<lbrakk>k:n\<rbrakk>\<^sub>c = \<lbrakk>m:n\<rbrakk>\<^sub>c"
  using assms by (metis elem_canon_finite_set_representation)
*)

thm image_self

lemma
  assumes n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes \<iota>_type[type_rule]: "\<iota> : [n]\<^sub>c \<rightarrow> [successor \<circ>\<^sub>c n]\<^sub>c" and \<iota>_mono: "monomorphism \<iota>"
  shows "[successor \<circ>\<^sub>c n]\<^sub>c \<setminus> ([n]\<^sub>c, \<iota>) \<cong> one"
proof -
  (* have \<iota>\<restriction>\<^bsub>([n]\<^sub>c, id)\<^esub> : [n]\<^sub>c \<rightarrow> \<iota>[[n]\<^sub>c]\<^bsub>id\<^esub> iso *)
  (* obtain its inverse, g : \<iota>[[n]\<^sub>c]\<^bsub>id\<^esub> \<rightarrow> [n]\<^sub>c *)
  obtain m where m_type[type_rule]: "m : ([successor \<circ>\<^sub>c n]\<^sub>c \<setminus> ([n]\<^sub>c, \<iota>)) \<rightarrow> [successor \<circ>\<^sub>c n]\<^sub>c" and
                      m_def: "equalizer ([successor \<circ>\<^sub>c n]\<^sub>c \<setminus> ([n]\<^sub>c, \<iota>)) m (characteristic_func \<iota>) (\<f> \<circ>\<^sub>c \<beta>\<^bsub>[successor \<circ>\<^sub>c n]\<^sub>c\<^esub>)"
    using \<iota>_mono \<iota>_type complement_morphism_equalizer complement_morphism_type by blast
  have chi_i: "(characteristic_func \<iota>) \<circ>\<^sub>c \<lbrakk>n:successor \<circ>\<^sub>c n\<rbrakk>\<^sub>c = \<f>"

(*Should we delete this now that we have the summation version which is more general?*)
lemma canonically_finite_succ:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "[successor \<circ>\<^sub>c n]\<^sub>c \<cong> [n]\<^sub>c \<Coprod> one"
proof -
  obtain \<iota> where \<iota>_def: "\<iota> = (canonical_finite_inclusion n (successor \<circ>\<^sub>c n))" and
                \<iota>_type[type_rule]: "\<iota> : [n]\<^sub>c \<rightarrow> [successor \<circ>\<^sub>c n]\<^sub>c" and 
                \<iota>_inj: "monomorphism \<iota>"
     by (typecheck_cfuncs, metis assms canonical_finite_inclusion_mono leq_infix_def lqe_connexity nat_strict_total_order)
  then obtain m where m_type[type_rule]: "m : ([successor \<circ>\<^sub>c n]\<^sub>c \<setminus> ([n]\<^sub>c, \<iota>)) \<rightarrow> [successor \<circ>\<^sub>c n]\<^sub>c" and
                      m_def: "equalizer ([successor \<circ>\<^sub>c n]\<^sub>c \<setminus> ([n]\<^sub>c, \<iota>)) m (characteristic_func \<iota>) (\<f> \<circ>\<^sub>c \<beta>\<^bsub>[successor \<circ>\<^sub>c n]\<^sub>c\<^esub>)"
     by (meson complement_morphism_equalizer complement_morphism_type)
  have chi_i: "(characteristic_func \<iota>) \<circ>\<^sub>c \<lbrakk>n:successor \<circ>\<^sub>c n\<rbrakk>\<^sub>c = \<f>"
    unfolding \<iota>_def by (typecheck_cfuncs, metis assms inclusion_characteristic_def3 leq_infix_def lqe_connexity nat_strict_total_order)
  have f_beta: "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>[successor \<circ>\<^sub>c n]\<^sub>c\<^esub>) \<circ>\<^sub>c \<lbrakk>n:successor \<circ>\<^sub>c n\<rbrakk>\<^sub>c = \<f>"
    by (typecheck_cfuncs, metis assms cfunc_type_def comp_associative id_right_unit2 leq_infix_def lqe_connexity terminal_func_comp_elem)
  obtain \<psi> where \<psi>_type[type_rule]: "\<psi> \<in>\<^sub>c [successor \<circ>\<^sub>c n]\<^sub>c \<setminus> ([n]\<^sub>c, \<iota>)" and \<psi>_def: "m \<circ>\<^sub>c \<psi> = \<lbrakk>n:successor \<circ>\<^sub>c n\<rbrakk>\<^sub>c"
    by (typecheck_cfuncs, metis assms cfunc_type_def chi_i equalizer_def f_beta leq_infix_def lqe_connexity m_def)
  have rep_fact: "\<And> k. k \<in>\<^sub>c [successor \<circ>\<^sub>c n]\<^sub>c \<and> (characteristic_func \<iota>) \<circ>\<^sub>c k = \<f> \<and> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>[successor \<circ>\<^sub>c n]\<^sub>c\<^esub>) \<circ>\<^sub>c k = \<f> \<Longrightarrow> k = \<lbrakk>n:successor \<circ>\<^sub>c n\<rbrakk>\<^sub>c" 
  proof(auto)
    fix k 
    assume k_type[type_rule]: "k \<in>\<^sub>c [successor \<circ>\<^sub>c n]\<^sub>c"
    assume chi_ik:"(characteristic_func \<iota>) \<circ>\<^sub>c k = \<f>"
    assume f_k: "(\<f> \<circ>\<^sub>c \<beta>\<^bsub>[successor \<circ>\<^sub>c n]\<^sub>c\<^esub>) \<circ>\<^sub>c k = \<f>"
    then obtain p where p_type:"p \<in>\<^sub>c \<nat>\<^sub>c" and p_def: "k = \<lbrakk>p:successor \<circ>\<^sub>c n\<rbrakk>\<^sub>c" and "successor \<circ>\<^sub>c p \<le>\<^sub>\<nat> successor \<circ>\<^sub>c n"
      using assms elem_canon_finite_set_representation by (typecheck_cfuncs, blast)
    then have "n \<le>\<^sub>\<nat> p"
      using assms inclusion_characteristic_def3 by (-,typecheck_cfuncs,
      metis \<iota>_def chi_ik leq_infix_def lqe_connexity nat_strict_total_order p_def p_type)
    then show "k = \<lbrakk>n:successor \<circ>\<^sub>c n\<rbrakk>\<^sub>c"
      using assms by (typecheck_cfuncs, metis \<open>successor \<circ>\<^sub>c p \<le>\<^sub>\<nat> successor \<circ>\<^sub>c n\<close> leq_infix_def lqe_antisymmetry nat_strict_total_order p_def p_type)
  qed
  have surj_phi: "surjective \<psi>"
  proof(typecheck_cfuncs, unfold surjective_def2, auto)
    fix y 
    assume y_type[type_rule]: "y \<in>\<^sub>c [successor \<circ>\<^sub>c n]\<^sub>c \<setminus> ([n]\<^sub>c, \<iota>)"  
    have f1: "successor \<circ>\<^sub>c (canonically_finite_morphism (successor \<circ>\<^sub>c n))  \<circ>\<^sub>c  \<iota>\<^sup>c  \<circ>\<^sub>c y \<le>\<^sub>\<nat> successor \<circ>\<^sub>c n"
      using assms \<iota>_inj leq_infix_def member_canonically_finite_set  by (typecheck_cfuncs, blast)
    have f2: "successor \<circ>\<^sub>c (canonically_finite_morphism (successor \<circ>\<^sub>c n))  \<circ>\<^sub>c  \<iota>\<^sup>c  \<circ>\<^sub>c \<psi> \<le>\<^sub>\<nat> successor \<circ>\<^sub>c n"
      using assms  \<iota>_inj leq_infix_def member_canonically_finite_set by (typecheck_cfuncs, blast)
    have char_iicy: "characteristic_func \<iota> \<circ>\<^sub>c \<iota>\<^sup>c \<circ>\<^sub>c y = \<f>"
      by (typecheck_cfuncs, smt (z3) \<iota>_inj comp_associative2 complement_morphism_eq id_right_unit2 terminal_func_comp terminal_func_comp_elem terminal_func_type)
    then have "\<not>(successor \<circ>\<^sub>c (canonically_finite_morphism (successor \<circ>\<^sub>c n))  \<circ>\<^sub>c  \<iota>\<^sup>c  \<circ>\<^sub>c y \<le>\<^sub>\<nat> n)"    
      by (typecheck_cfuncs,  metis assms \<iota>_def \<iota>_inj  add_respects_succ3 add_respects_zero_on_left exists_implies_leq_true inclusion_characteristic_def leq_infix_def succ_n_type true_false_distinct zero_type)
    then have "( successor \<circ>\<^sub>c n \<le>\<^sub>\<nat> successor \<circ>\<^sub>c (canonically_finite_morphism (successor \<circ>\<^sub>c n))  \<circ>\<^sub>c  \<iota>\<^sup>c  \<circ>\<^sub>c y)"    
      using assms \<iota>_inj nat_strict_total_order by (typecheck_cfuncs, blast)
    then have f3: "(successor \<circ>\<^sub>c n = successor \<circ>\<^sub>c (canonically_finite_morphism (successor \<circ>\<^sub>c n))  \<circ>\<^sub>c  \<iota>\<^sup>c  \<circ>\<^sub>c y)"
      using assms by (typecheck_cfuncs, meson \<iota>_inj  f1 leq_infix_def lqe_antisymmetry)
    have char_iicphi: "characteristic_func \<iota> \<circ>\<^sub>c \<iota>\<^sup>c \<circ>\<^sub>c \<psi> = \<f>"
      by (typecheck_cfuncs, smt (z3) \<iota>_inj comp_associative2 complement_morphism_eq id_right_unit2 terminal_func_comp terminal_func_comp_elem terminal_func_type)
    then have  "\<not>(successor \<circ>\<^sub>c (canonically_finite_morphism (successor \<circ>\<^sub>c n))  \<circ>\<^sub>c  \<iota>\<^sup>c  \<circ>\<^sub>c \<psi> \<le>\<^sub>\<nat> n)"
      by (typecheck_cfuncs,  metis assms \<iota>_def \<iota>_inj  add_respects_succ3 add_respects_zero_on_left exists_implies_leq_true inclusion_characteristic_def leq_infix_def succ_n_type true_false_distinct zero_type)
    then have "( successor \<circ>\<^sub>c n \<le>\<^sub>\<nat> successor \<circ>\<^sub>c (canonically_finite_morphism (successor \<circ>\<^sub>c n))  \<circ>\<^sub>c  \<iota>\<^sup>c  \<circ>\<^sub>c \<psi>)"    
      using assms \<iota>_inj nat_strict_total_order by (typecheck_cfuncs, blast)
    then have f4: "( successor \<circ>\<^sub>c n = successor \<circ>\<^sub>c (canonically_finite_morphism (successor \<circ>\<^sub>c n))  \<circ>\<^sub>c  \<iota>\<^sup>c  \<circ>\<^sub>c \<psi>)"    
      using assms by (typecheck_cfuncs, meson \<iota>_inj  f2 leq_infix_def lqe_antisymmetry)
    have "(canonically_finite_morphism (successor \<circ>\<^sub>c n))  \<circ>\<^sub>c  \<iota>\<^sup>c  \<circ>\<^sub>c \<psi> = (canonically_finite_morphism (successor \<circ>\<^sub>c n))  \<circ>\<^sub>c  \<iota>\<^sup>c  \<circ>\<^sub>c y"
      using assms \<iota>_inj f3 f4  succ_inject by (typecheck_cfuncs, presburger)
    then have "\<psi> = y"
      by (typecheck_cfuncs_prems, smt (verit, best) \<iota>_inj char_iicy char_iicphi rep_fact cfunc_type_def characteristic_func_type comp_associative complement_morphism_eq complement_morphism_mono domain_comp monomorphism_def3 terminal_func_type)
    then show "\<exists>x. x \<in>\<^sub>c one \<and> \<psi> \<circ>\<^sub>c x = y"
      by (metis \<psi>_type cfunc_type_def id_right_unit id_type)
  qed
  have  "injective \<psi>"
    using \<psi>_type element_monomorphism monomorphism_imp_injective by blast 
  then have "isomorphism \<psi>"
    using \<psi>_type element_monomorphism epi_mon_is_iso surj_phi surjective_is_epimorphism by blast
  then have "[successor \<circ>\<^sub>c n]\<^sub>c \<setminus> ([n]\<^sub>c, \<iota>) \<cong> one"
    using \<psi>_type is_isomorphic_def isomorphic_is_symmetric by blast
  then obtain \<psi>_inv where \<psi>_inv_type[type_rule]: "\<psi>_inv :  [successor \<circ>\<^sub>c n]\<^sub>c \<setminus> ([n]\<^sub>c, \<iota>) \<rightarrow> one" and 
              \<psi>_inv_iso: "isomorphism \<psi>_inv"
    using is_isomorphic_def by blast
  obtain f where f_type[type_rule]: "f : [successor \<circ>\<^sub>c n]\<^sub>c \<rightarrow> [n]\<^sub>c \<Coprod> one" and 
                 f_def: "f = (id[n]\<^sub>c \<bowtie>\<^sub>f \<psi>_inv) \<circ>\<^sub>c try_cast \<iota>"
     by (typecheck_cfuncs_prems, smt \<iota>_inj assms)
   then have "isomorphism f"  
     unfolding f_def by (typecheck_cfuncs, metis \<iota>_inj \<psi>_inv_iso cfunc_bowtieprod_iso id_isomorphism id_type into_super_iso into_super_type isomorphism_comp' isomorphism_sandwich try_cast_into_super)
   then show ?thesis
     using f_type is_isomorphic_def by blast
qed



lemma one_canonically_finite_set_one:
  "[successor \<circ>\<^sub>c zero]\<^sub>c \<cong> one"
  by (meson canonically_finite_succ coprod_with_init_obj2 zero_canonically_finite_set_empty iso_empty_initial iso_to_term_is_term one_terminal_object terminal_objects_isomorphic zero_type)

lemma two_canonically_finite_set_Omega:
  "[successor \<circ>\<^sub>c successor \<circ>\<^sub>c zero]\<^sub>c \<cong> \<Omega>"
  by (meson canonically_finite_succ coprod_pres_iso isomorphic_is_reflexive isomorphic_is_transitive oneUone_iso_\<Omega> one_canonically_finite_set_one succ_n_type zero_type)
  






(*We cannot yet show they are finite*)
lemma canonicall_finite_sets_are_countable: 
  assumes n_type[type_rule]:  "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "countable [n]\<^sub>c"
  by (meson canonically_finite_morph_mono canonically_finite_morphism_type countable_def n_type)


lemma sum_of_canonically_finite_sets:
  assumes n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c" and m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c"
  shows "[n +\<^sub>\<nat> m]\<^sub>c \<cong> [n]\<^sub>c \<Coprod> [m]\<^sub>c"
proof -
  obtain \<phi> where \<phi>_type[type_rule]: "\<phi> : [n]\<^sub>c \<Coprod> [m]\<^sub>c \<rightarrow> \<nat>\<^sub>c" and
    \<phi>_def: "\<phi> = canonically_finite_morphism n \<amalg> (add2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>[m]\<^sub>c\<^esub>, canonically_finite_morphism m\<rangle>)"
    by typecheck_cfuncs

  have "injective \<phi>"
  proof (etcs_subst injective_def2, auto)
    fix x y
    assume x_type[type_rule]: "x \<in>\<^sub>c [n]\<^sub>c \<Coprod> [m]\<^sub>c"
    assume y_type[type_rule]: "y \<in>\<^sub>c [n]\<^sub>c \<Coprod> [m]\<^sub>c"
    assume \<phi>_eq: "\<phi> \<circ>\<^sub>c x = \<phi> \<circ>\<^sub>c y"

    show "x = y"
    proof (cases "\<exists> x'. x = right_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c x' \<and> x' \<in>\<^sub>c [m]\<^sub>c", auto)
      fix x'
      assume x'type[type_rule]: "x' \<in>\<^sub>c [m]\<^sub>c"
      assume x_right: "x = right_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c x'"

      show "right_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c x' = y"
      proof (cases "\<exists> y'. y = right_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c y' \<and> y' \<in>\<^sub>c [m]\<^sub>c", auto)
        fix y'
        assume y'_type[type_rule]: "y' \<in>\<^sub>c [m]\<^sub>c"
        assume y_right: "y = right_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c y'"

        have "(add2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>[m]\<^sub>c\<^esub>, canonically_finite_morphism m\<rangle>) \<circ>\<^sub>c x' = (add2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>[m]\<^sub>c\<^esub>, canonically_finite_morphism m\<rangle>) \<circ>\<^sub>c y'"
          using \<phi>_eq unfolding \<phi>_def x_right y_right by (typecheck_cfuncs_prems, auto simp add: comp_associative2 right_coproj_cfunc_coprod)
        then have "add2 \<circ>\<^sub>c \<langle>n, canonically_finite_morphism m \<circ>\<^sub>c x'\<rangle> = add2 \<circ>\<^sub>c \<langle>n, canonically_finite_morphism m \<circ>\<^sub>c y'\<rangle>"
          by (typecheck_cfuncs_prems, smt (z3) cfunc_prod_comp comp_associative2 id_right_unit2 terminal_func_comp_elem)
        then have "canonically_finite_morphism m \<circ>\<^sub>c x' = canonically_finite_morphism m \<circ>\<^sub>c y'"
          by (fold add_def, typecheck_cfuncs_prems, smt add_commutes add_cancellative)
        then have "x' = y'"
          using canonically_finite_morph_mono monomorphism_def3 by (typecheck_cfuncs_prems, blast)
        then show "right_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c x' = right_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c y'"
          by auto
      next
        assume "\<forall>y'. y = right_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c y' \<longrightarrow> \<not> y' \<in>\<^sub>c [m]\<^sub>c"
        then obtain y' where y'_type[type_rule]: "y' \<in>\<^sub>c [n]\<^sub>c" and
          y_left: "y = left_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c y'"
          using coprojs_jointly_surj y_type by blast

        have bnd: "successor \<circ>\<^sub>c canonically_finite_morphism n \<circ>\<^sub>c y' \<le>\<^sub>\<nat> n"
          by (simp add: leq_infix_def member_canonically_finite_set n_type y'_type)


        have "n +\<^sub>\<nat> (canonically_finite_morphism m \<circ>\<^sub>c x') = canonically_finite_morphism n \<circ>\<^sub>c y'"
        proof - 
          have "n +\<^sub>\<nat> (canonically_finite_morphism m \<circ>\<^sub>c x') = add2 \<circ>\<^sub>c \<langle>n, canonically_finite_morphism m \<circ>\<^sub>c x'\<rangle>"
            using add_def by auto
          also have "... = add2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>[m]\<^sub>c\<^esub> \<circ>\<^sub>c x', canonically_finite_morphism m \<circ>\<^sub>c x'\<rangle>"
            by (typecheck_cfuncs, simp add: id_right_unit2 terminal_func_comp_elem)
          also have "... = add2 \<circ>\<^sub>c \<langle>(n \<circ>\<^sub>c \<beta>\<^bsub>[m]\<^sub>c\<^esub>) \<circ>\<^sub>c x', canonically_finite_morphism m \<circ>\<^sub>c x'\<rangle>"
            by (typecheck_cfuncs, simp add: comp_associative2)
          also have "... = add2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>[m]\<^sub>c\<^esub>, canonically_finite_morphism m\<rangle>  \<circ>\<^sub>c x'"
            by (typecheck_cfuncs, simp add: cfunc_prod_comp)
          also have "... = canonically_finite_morphism n \<amalg> (add2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>[m]\<^sub>c\<^esub>, canonically_finite_morphism m\<rangle>)  \<circ>\<^sub>c right_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c x'"
            unfolding \<phi>_def by (typecheck_cfuncs, simp add: comp_associative2 right_coproj_cfunc_coprod)
          also have "... = canonically_finite_morphism n \<amalg> (add2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>[m]\<^sub>c\<^esub>, canonically_finite_morphism m\<rangle>)  \<circ>\<^sub>c left_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c y'" 
             using \<phi>_eq unfolding \<phi>_def  x_right y_left by fastforce
          also have "... = canonically_finite_morphism n \<circ>\<^sub>c y'"
            by (typecheck_cfuncs, simp add: comp_associative2 left_coproj_cfunc_coprod)
          then show ?thesis 
            by (simp add: calculation)
        qed
        then have "(successor \<circ>\<^sub>c n) +\<^sub>\<nat> (canonically_finite_morphism m \<circ>\<^sub>c x') \<le>\<^sub>\<nat> n "
          using  add_respects_succ3 bnd by (typecheck_cfuncs, presburger)
        then have "successor \<circ>\<^sub>c n \<le>\<^sub>\<nat> n "
          by (typecheck_cfuncs, metis canonically_finite_morphism_type comp_type fewer_is_less m_type x'type)
        then have False
          using leq_infix_def lqe_connexity n_type nat_strict_total_order by blast
        then show "right_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c x' = y"
          by simp
      qed
    next
      assume "\<forall>x'. x = right_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c x' \<longrightarrow> \<not> x' \<in>\<^sub>c [m]\<^sub>c"
      then obtain x' where x'_type[type_rule]: "x' \<in>\<^sub>c [n]\<^sub>c" and
          x_left: "x = left_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c x'"
          using coprojs_jointly_surj x_type by blast

      have x'_bnd: "successor \<circ>\<^sub>c canonically_finite_morphism n \<circ>\<^sub>c x' \<le>\<^sub>\<nat> n"
        by (simp add: leq_infix_def member_canonically_finite_set n_type x'_type)
    
      show "x = y"    
      proof(cases "\<exists> y'. y = right_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c y' \<and> y' \<in>\<^sub>c [m]\<^sub>c", auto)
        fix y'
        assume y'_type[type_rule]: "y' \<in>\<^sub>c [m]\<^sub>c"
        assume y_right: "y = right_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c y'"
        
        have " n +\<^sub>\<nat> (canonically_finite_morphism m \<circ>\<^sub>c y') = canonically_finite_morphism n \<circ>\<^sub>c x' "
        proof - 
          have "n +\<^sub>\<nat> (canonically_finite_morphism m \<circ>\<^sub>c y') = add2 \<circ>\<^sub>c \<langle>n, canonically_finite_morphism m \<circ>\<^sub>c y'\<rangle>"
            using add_def by auto
          also have "... = add2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>[m]\<^sub>c\<^esub> \<circ>\<^sub>c y', canonically_finite_morphism m \<circ>\<^sub>c y'\<rangle>"
            by (typecheck_cfuncs, simp add: id_right_unit2 terminal_func_comp_elem)
          also have "... = add2 \<circ>\<^sub>c \<langle>(n \<circ>\<^sub>c \<beta>\<^bsub>[m]\<^sub>c\<^esub>) \<circ>\<^sub>c y', canonically_finite_morphism m \<circ>\<^sub>c y'\<rangle>"
            by (typecheck_cfuncs, simp add: comp_associative2)
          also have "... = add2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>[m]\<^sub>c\<^esub>, canonically_finite_morphism m\<rangle>  \<circ>\<^sub>c y'"
            by (typecheck_cfuncs, simp add: cfunc_prod_comp)
          also have "... = canonically_finite_morphism n \<amalg> (add2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>[m]\<^sub>c\<^esub>, canonically_finite_morphism m\<rangle>)  \<circ>\<^sub>c right_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c y'"
            unfolding \<phi>_def by (typecheck_cfuncs, simp add: comp_associative2 right_coproj_cfunc_coprod)
          also have "... = canonically_finite_morphism n \<amalg> (add2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>[m]\<^sub>c\<^esub>, canonically_finite_morphism m\<rangle>)  \<circ>\<^sub>c left_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c x'" 
             using \<phi>_eq unfolding \<phi>_def  y_right x_left by fastforce
          also have "... = canonically_finite_morphism n \<circ>\<^sub>c x'"
            by (typecheck_cfuncs, simp add: comp_associative2 left_coproj_cfunc_coprod)
          then show ?thesis
            by (simp add: calculation)
        qed
        then have "(successor \<circ>\<^sub>c n) +\<^sub>\<nat> (canonically_finite_morphism m \<circ>\<^sub>c y') \<le>\<^sub>\<nat> n "
          using  add_respects_succ3 x'_bnd by (typecheck_cfuncs, presburger)
        then have "successor \<circ>\<^sub>c n \<le>\<^sub>\<nat> n "
          by (typecheck_cfuncs, metis canonically_finite_morphism_type comp_type fewer_is_less m_type y'_type)
        then have False
          using leq_infix_def lqe_connexity n_type nat_strict_total_order by blast
        then show " x = right_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c y'"
          by simp 
      next
        assume "\<forall>y'. y = right_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c y' \<longrightarrow> \<not> y' \<in>\<^sub>c [m]\<^sub>c"
        then obtain y' where y'_type[type_rule]: "y' \<in>\<^sub>c [n]\<^sub>c" and
          y_left: "y = left_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c y'"
          using coprojs_jointly_surj y_type by blast
        have "canonically_finite_morphism n \<circ>\<^sub>c x' = canonically_finite_morphism n \<circ>\<^sub>c  y'"
        proof - 
          have "canonically_finite_morphism n \<circ>\<^sub>c x' = (canonically_finite_morphism n \<amalg> (add2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>[m]\<^sub>c\<^esub>, canonically_finite_morphism m\<rangle>) \<circ>\<^sub>c left_coproj [n]\<^sub>c [m]\<^sub>c) \<circ>\<^sub>c x'"
            by (typecheck_cfuncs, simp add: left_coproj_cfunc_coprod)
          also have "... = (canonically_finite_morphism n \<amalg> (add2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>[m]\<^sub>c\<^esub>, canonically_finite_morphism m\<rangle>) \<circ>\<^sub>c left_coproj [n]\<^sub>c [m]\<^sub>c) \<circ>\<^sub>c y'"
            using \<phi>_def \<phi>_eq comp_associative2 x_left y_left by (typecheck_cfuncs, force)
          also have "... =canonically_finite_morphism n \<circ>\<^sub>c y'"
            by (typecheck_cfuncs, simp add: left_coproj_cfunc_coprod)
          then show ?thesis
            by (simp add: calculation)
        qed
        then have "x' = y'"
          by (typecheck_cfuncs_prems, metis elem_canon_finite_def2 elem_canon_finite_set_representation)
        then show "x=y"
          using x_left y_left by blast
        qed
   qed
 qed

  have "(leq \<circ>\<^sub>c \<langle>successor, (n +\<^sub>\<nat> m)  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c  \<phi> = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c  \<phi>"
  proof(rule one_separator[where X = "[n]\<^sub>c \<Coprod> [m]\<^sub>c", where Y = \<Omega>])
    show "(leq \<circ>\<^sub>c \<langle>successor,n +\<^sub>\<nat> m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c \<phi> : [n]\<^sub>c \<Coprod> [m]\<^sub>c \<rightarrow> \<Omega>"
      by typecheck_cfuncs
    show "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c \<phi> : [n]\<^sub>c \<Coprod> [m]\<^sub>c \<rightarrow> \<Omega>"
      by typecheck_cfuncs
  next
    fix nm
    assume nm_type: "nm  \<in>\<^sub>c [n]\<^sub>c \<Coprod> [m]\<^sub>c"
    show "((leq \<circ>\<^sub>c \<langle>successor,n +\<^sub>\<nat> m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c nm = ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c nm"
    proof(cases "\<exists> y. nm= right_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c y \<and> y \<in>\<^sub>c [m]\<^sub>c", auto)
      fix y
      assume y_type[type_rule]: "y \<in>\<^sub>c [m]\<^sub>c"
      assume "nm = right_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c y" 

      obtain k where k_type[type_rule]: "k \<in>\<^sub>c \<nat>\<^sub>c" and k_bnd: "successor \<circ>\<^sub>c k \<le>\<^sub>\<nat> m" and k_def: "y = \<lbrakk>k:m\<rbrakk>\<^sub>c"
        using elem_canon_finite_set_representation m_type y_type by blast

      have "((leq \<circ>\<^sub>c \<langle>successor,n +\<^sub>\<nat> m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c right_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c y = 
             (leq \<circ>\<^sub>c \<langle>successor,n +\<^sub>\<nat> m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c (\<phi> \<circ>\<^sub>c right_coproj [n]\<^sub>c [m]\<^sub>c) \<circ>\<^sub>c y"
        by (typecheck_cfuncs, simp add:  comp_associative2)
      also have "... = (leq \<circ>\<^sub>c \<langle>successor,n +\<^sub>\<nat> m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c (add2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>[m]\<^sub>c\<^esub>, canonically_finite_morphism m\<rangle>) \<circ>\<^sub>c y"
        by (typecheck_cfuncs, metis \<phi>_def canonically_finite_morphism_type right_coproj_cfunc_coprod)
      also have "... = (leq \<circ>\<^sub>c \<langle>successor,n +\<^sub>\<nat> m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c (add2 \<circ>\<^sub>c \<langle>n, canonically_finite_morphism m \<circ>\<^sub>c y\<rangle> )"
        by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2 id_right_unit2 terminal_func_comp_elem)
      also have "... = (leq \<circ>\<^sub>c \<langle>successor,n +\<^sub>\<nat> m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c (n +\<^sub>\<nat> k )"
        using add_def elem_canon_finite_def2 k_bnd k_def by (typecheck_cfuncs, presburger)
      also have "... = leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c (n +\<^sub>\<nat> k ),n +\<^sub>\<nat> m\<rangle>"
        by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2 id_right_unit2 terminal_func_comp_elem)
      also have "... = \<t>"
        by (typecheck_cfuncs, metis add_monotonic add_respects_succ1 k_bnd leq_infix_def lqe_connexity succ_n_type)
      also have "... = ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c right_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c y"
        by (typecheck_cfuncs, smt (verit, ccfv_SIG)  comp_associative2 comp_type id_right_unit2 terminal_func_comp_elem)
      then show "((leq \<circ>\<^sub>c \<langle>successor,n +\<^sub>\<nat> m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c right_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c y = ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c right_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c y"
        by (simp add: calculation)
    next
      assume "\<forall>y. nm = right_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c y \<longrightarrow> \<not> y \<in>\<^sub>c [m]\<^sub>c"
      then obtain y where y_type[type_rule]: "y \<in>\<^sub>c [n]\<^sub>c" and
          y_left: "nm = left_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c y"
        by (metis coprojs_jointly_surj nm_type)
     

      have "((leq \<circ>\<^sub>c \<langle>successor,n +\<^sub>\<nat> m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c nm =  (leq \<circ>\<^sub>c \<langle>successor,n +\<^sub>\<nat> m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c ((\<phi> \<circ>\<^sub>c left_coproj [n]\<^sub>c [m]\<^sub>c) \<circ>\<^sub>c y)"
        using cfunc_type_def comp_associative y_left by (typecheck_cfuncs, force)
      also have "... = (leq \<circ>\<^sub>c \<langle>successor,n +\<^sub>\<nat> m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c (canonically_finite_morphism n \<circ>\<^sub>c y)"
        unfolding \<phi>_def by (typecheck_cfuncs, simp add: left_coproj_cfunc_coprod)
      also have "... = leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c (canonically_finite_morphism n \<circ>\<^sub>c y),n +\<^sub>\<nat> m \<rangle>"
        by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2 id_right_unit2 terminal_func_comp_elem)
      also have "... = \<t>"
        by (typecheck_cfuncs, metis fewer_is_less leq_infix_def member_canonically_finite_set nat_strict_total_order)
      also have "... = ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c nm"
        by (typecheck_cfuncs, smt (z3) comp_associative2 id_right_unit2 id_type nm_type terminal_func_comp terminal_func_type terminal_func_unique)
      then show "((leq \<circ>\<^sub>c \<langle>successor,n +\<^sub>\<nat> m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c nm = ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c nm"
        by (simp add: calculation)
    qed
  qed
  then obtain \<psi> where \<psi>_type[type_rule]: "\<psi> : [n]\<^sub>c \<Coprod> [m]\<^sub>c \<rightarrow> [n +\<^sub>\<nat> m]\<^sub>c" and \<psi>_def: "(canonically_finite_morphism (n +\<^sub>\<nat> m)) \<circ>\<^sub>c \<psi> = \<phi>"
    by (typecheck_cfuncs, metis canonically_finite_morphism_def2 cfunc_type_def equalizer_def)
  then have \<psi>_mono: "monomorphism \<psi>"
    by (metis \<open>injective \<phi>\<close> add_type canonically_finite_morphism_type comp_monic_imp_monic' injective_imp_monomorphism m_type mem_Collect_eq n_type)
  have "surjective \<psi>"
  proof(etcs_subst surjective_def2, auto)
    fix y 
    assume y_type[type_rule]: "y \<in>\<^sub>c [n +\<^sub>\<nat> m]\<^sub>c"
    then obtain k where k_type[type_rule]: "k \<in>\<^sub>c \<nat>\<^sub>c" and k_def: "y = \<lbrakk>k:n +\<^sub>\<nat> m\<rbrakk>\<^sub>c" and k_bnd: "successor \<circ>\<^sub>c k \<le>\<^sub>\<nat> n +\<^sub>\<nat> m"
      by (metis add_type assms elem_canon_finite_set_representation)
    show "\<exists>x. x \<in>\<^sub>c [n]\<^sub>c \<Coprod> [m]\<^sub>c \<and> \<psi> \<circ>\<^sub>c x = y"
    proof(cases "successor \<circ>\<^sub>c k \<le>\<^sub>\<nat> n")
      assume case1: "successor \<circ>\<^sub>c k \<le>\<^sub>\<nat> n"
      have "(canonically_finite_morphism (n +\<^sub>\<nat> m)) \<circ>\<^sub>c (\<psi> \<circ>\<^sub>c (left_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c \<lbrakk>k:n\<rbrakk>\<^sub>c)) = (canonically_finite_morphism (n +\<^sub>\<nat> m)) \<circ>\<^sub>c \<lbrakk>k:n +\<^sub>\<nat> m\<rbrakk>\<^sub>c"
      proof - 
        have "(canonically_finite_morphism (n +\<^sub>\<nat> m)) \<circ>\<^sub>c (\<psi> \<circ>\<^sub>c (left_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c \<lbrakk>k:n\<rbrakk>\<^sub>c)) = \<phi> \<circ>\<^sub>c (left_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c \<lbrakk>k:n\<rbrakk>\<^sub>c)"
          by (typecheck_cfuncs, smt \<psi>_def case1 comp_associative2)
        also have "... = canonically_finite_morphism n\<circ>\<^sub>c \<lbrakk>k:n\<rbrakk>\<^sub>c"
          unfolding \<phi>_def by (typecheck_cfuncs, simp add: case1 comp_associative2 left_coproj_cfunc_coprod)
        also have "... = canonically_finite_morphism (n +\<^sub>\<nat> m) \<circ>\<^sub>c \<lbrakk>k:n +\<^sub>\<nat> m\<rbrakk>\<^sub>c"
          using case1 elem_canon_finite_def2 k_bnd by (typecheck_cfuncs, presburger)
        then show ?thesis 
          by (simp add: calculation)
      qed     
      then have "\<psi> \<circ>\<^sub>c (left_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c \<lbrakk>k:n\<rbrakk>\<^sub>c) = y"
        unfolding k_def by (typecheck_cfuncs_prems, meson canonically_finite_morph_mono case1 k_bnd monomorphism_def3)
      then show ?thesis
        by (metis case1 comp_type elem_canon_finite_set k_type left_proj_type n_type)
    next
      assume "\<not> successor \<circ>\<^sub>c k \<le>\<^sub>\<nat> n"
      then have case2: "n \<le>\<^sub>\<nat> k"
        by (typecheck_cfuncs, simp add: nat_strict_total_order)
      then obtain j where j_type[type_rule]: "j \<in>\<^sub>c \<nat>\<^sub>c" and j_def: "j +\<^sub>\<nat> n = k"  
        using assms by (typecheck_cfuncs, meson case2 leq_infix_def leq_true_implies_exists)
      then have j_bnd: "successor \<circ>\<^sub>c j \<le>\<^sub>\<nat> m"
        using k_bnd by (typecheck_cfuncs_prems, metis add_commutes add_monotonic leq_infix_def lqe_connexity nat_strict_total_order)


      have "(canonically_finite_morphism (n +\<^sub>\<nat> m)) \<circ>\<^sub>c (\<psi> \<circ>\<^sub>c (right_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c \<lbrakk>j:m\<rbrakk>\<^sub>c)) = (canonically_finite_morphism (n +\<^sub>\<nat> m)) \<circ>\<^sub>c \<lbrakk>k:n +\<^sub>\<nat> m\<rbrakk>\<^sub>c"
      proof - 
        have "(canonically_finite_morphism (n +\<^sub>\<nat> m)) \<circ>\<^sub>c (\<psi> \<circ>\<^sub>c (right_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c \<lbrakk>j:m\<rbrakk>\<^sub>c)) = \<phi> \<circ>\<^sub>c (right_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c \<lbrakk>j:m\<rbrakk>\<^sub>c)"
          by (typecheck_cfuncs, metis \<psi>_def cfunc_type_def comp_associative j_bnd)
        also have "... = (add2 \<circ>\<^sub>c \<langle>n \<circ>\<^sub>c \<beta>\<^bsub>[m]\<^sub>c\<^esub>, canonically_finite_morphism m\<rangle>) \<circ>\<^sub>c \<lbrakk>j:m\<rbrakk>\<^sub>c"
          by (typecheck_cfuncs, metis (full_types) \<phi>_def canonically_finite_morphism_type comp_associative2 j_bnd right_coproj_cfunc_coprod)
        also have "... = add2 \<circ>\<^sub>c \<langle>n, canonically_finite_morphism m \<circ>\<^sub>c \<lbrakk>j:m\<rbrakk>\<^sub>c\<rangle>"
          by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2 id_right_unit2 j_bnd terminal_func_comp_elem)
        also have "... = (canonically_finite_morphism (n +\<^sub>\<nat> m)) \<circ>\<^sub>c \<lbrakk>k:n +\<^sub>\<nat> m\<rbrakk>\<^sub>c"
          by (typecheck_cfuncs, metis j_def add_commutes add_def elem_canon_finite_def2 j_bnd k_bnd)
        then show ?thesis
          by (simp add: calculation)
      qed
      then have "\<psi> \<circ>\<^sub>c (right_coproj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c \<lbrakk>j:m\<rbrakk>\<^sub>c) = y"
        unfolding k_def by (typecheck_cfuncs_prems, meson canonically_finite_morph_mono j_bnd k_bnd monomorphism_def3)
      then show ?thesis
        by (metis comp_type elem_canon_finite_set j_bnd j_type m_type right_proj_type)
    qed
  qed
  then show ?thesis
    using \<psi>_type surjective_is_epimorphism \<psi>_mono epi_mon_is_iso is_isomorphic_def isomorphic_is_symmetric by blast
qed


(*Maybe we need to use canonical_finite_inclusion n succ n   ?*)
lemma canonically_finite_sets_are_finite_aux:
  assumes n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "\<not>([n]\<^sub>c \<cong> [successor  \<circ>\<^sub>c  n]\<^sub>c)"
proof(rule ccontr, auto)
  assume "[n]\<^sub>c \<cong> [successor \<circ>\<^sub>c n]\<^sub>c"
  then obtain \<psi> where \<phi>_type[type_rule]: "\<psi> : [n]\<^sub>c \<rightarrow> [successor \<circ>\<^sub>c n]\<^sub>c" and \<psi>_iso: "isomorphism \<psi>"
    using is_isomorphic_def by blast
  then have new_equalizer: "equalizer [n]\<^sub>c (canonically_finite_morphism (successor \<circ>\<^sub>c n) \<circ>\<^sub>c \<psi>) (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) (leq \<circ>\<^sub>c \<langle>successor, successor \<circ>\<^sub>c n  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>)"
    by (typecheck_cfuncs, simp add: \<psi>_iso canonically_finite_morphism_def2 comp_associative2 isomorphic_to_equalizer_is_equalizer)
  
  have "(leq \<circ>\<^sub>c \<langle>successor, successor \<circ>\<^sub>c n  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>)  \<circ>\<^sub>c n = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c n"
    by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2 id_right_unit2 lqe_connexity succ_n_type terminal_func_comp_elem)
  then have "n factorsthru (canonically_finite_morphism (successor \<circ>\<^sub>c n) \<circ>\<^sub>c \<psi>)"
    using  xfactorthru_equalizer_iff_fx_eq_gx by (-, typecheck_cfuncs, smt new_equalizer)
  then obtain u where u_type[type_rule]: "u \<in>\<^sub>c [n]\<^sub>c" and u_def: "(canonically_finite_morphism (successor \<circ>\<^sub>c n) \<circ>\<^sub>c \<psi>) \<circ>\<^sub>c u = n"
    by (typecheck_cfuncs, meson factors_through_def2)
  then obtain k where k_type[type_rule]: "k \<in>\<^sub>c \<nat>\<^sub>c" and k_bnd: "successor \<circ>\<^sub>c k \<le>\<^sub>\<nat> n" and k_def: "u = \<lbrakk>k:n\<rbrakk>\<^sub>c"
    by (metis elem_canon_finite_set_representation n_type)
  have "n= canonically_finite_morphism (successor \<circ>\<^sub>c n) \<circ>\<^sub>c (\<psi> \<circ>\<^sub>c u)"
    by (typecheck_cfuncs, simp add: comp_associative2 u_def)
  then have "\<psi> \<circ>\<^sub>c u = \<lbrakk>n:successor \<circ>\<^sub>c n\<rbrakk>\<^sub>c"
    by (typecheck_cfuncs, metis canonically_finite_morph_mono canonically_finite_morphism_type elem_canon_finite_def2 leq_infix_def lqe_connexity monomorphism_def2)
  
  oops







theorem Euclid's_division_lemma:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c" and "m \<noteq> zero"
  shows "\<exists> q r. ((q \<in>\<^sub>c \<nat>\<^sub>c) \<and> (r \<in>\<^sub>c \<nat>\<^sub>c) \<and> (n = (m \<cdot>\<^sub>\<nat> q) +\<^sub>\<nat> r) \<and> (successor  \<circ>\<^sub>c r \<le>\<^sub>\<nat> m)) \<and> 
         (\<forall> s t. (s \<in>\<^sub>c \<nat>\<^sub>c) \<and> (t \<in>\<^sub>c \<nat>\<^sub>c) \<and> (n = (m \<cdot>\<^sub>\<nat> s) +\<^sub>\<nat> t) \<and> (successor  \<circ>\<^sub>c t \<le>\<^sub>\<nat> m) \<longrightarrow> (s=q) \<and> (t=r))"
proof(cases "n=zero")
  show "n = zero \<Longrightarrow> ?thesis"
    by(rule_tac x=zero in exI, rule_tac x=zero in exI, typecheck_cfuncs, metis add_respects_zero_on_right add_type
       assms(2,3) exists_implies_leq_true leq_infix_def mult_cancellative mult_commutative mult_respects_zero_right
       mult_type nat_strict_total_order nonzero_is_succ zero_is_smallest zero_type)
  next
    assume "n \<noteq> zero"
    obtain f where f_type[type_rule]: "f : \<nat>\<^sub>c \<rightarrow> \<Omega>" and f_def: "f = leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, mult2 \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<rangle>"
      using assms by typecheck_cfuncs
    obtain g where g_type[type_rule]: "g : \<nat>\<^sub>c \<rightarrow> \<Omega>" and g_def: "g = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
      using assms by typecheck_cfuncs
  
    then obtain E e where  e_type[type_rule]: "e : E \<rightarrow> \<nat>\<^sub>c" and  E_def: "f \<circ>\<^sub>c e = g \<circ>\<^sub>c e \<and> (\<forall> h F. ((h : F \<rightarrow> \<nat>\<^sub>c) \<and> (f \<circ>\<^sub>c h = g \<circ>\<^sub>c h)) \<longrightarrow> (\<exists>! k. (k : F \<rightarrow> E) \<and> e \<circ>\<^sub>c k = h))"
      using equalizer_exists2 by (typecheck_cfuncs, blast)
    then have equalizer: "equalizer E e f g"   
      unfolding equalizer_def by (typecheck_cfuncs, blast)
    then have mono_e: "monomorphism e"
      using equalizer equalizer_is_monomorphism by blast
  
    have satisfying_set:  "\<And>j. (j \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (j  \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (E,e)) = (successor \<circ>\<^sub>c n \<le>\<^sub>\<nat> m \<cdot>\<^sub>\<nat> j))"
    proof - 
      have f1: "\<And>j. (j \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (j  \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (E,e)) = (f \<circ>\<^sub>c j = \<t>))"
      proof(auto)
        fix j 
        assume j_type[type_rule]: "j \<in>\<^sub>c \<nat>\<^sub>c"
        assume j_relmem: "j \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (E, e)"
        then have "j factorsthru e"
          using j_relmem by (meson relative_member_def2)          
        then obtain h where h_type[type_rule]: "h \<in>\<^sub>c E" and h_def: "e \<circ>\<^sub>c h = j"
          using factors_through_def2 by (typecheck_cfuncs, auto)
        have "f \<circ>\<^sub>c j = (f \<circ>\<^sub>c e) \<circ>\<^sub>c h"
          using comp_associative2 e_type f_type h_def h_type by blast
        also have "... = g \<circ>\<^sub>c (e \<circ>\<^sub>c h)"
          using E_def comp_associative2 e_type g_type h_type by auto
        also have "... = \<t>"
          using comp_associative2 g_def h_def id_right_unit2 j_type terminal_func_comp_elem terminal_func_type true_func_type by fastforce
        then show "f \<circ>\<^sub>c j = \<t>"
          by (simp add: calculation)
      next
        fix j 
        assume j_type[type_rule]: "j \<in>\<^sub>c \<nat>\<^sub>c"
        assume fj_true: "f \<circ>\<^sub>c j = \<t>"
        have "g \<circ>\<^sub>c j = \<t>"
          by (typecheck_cfuncs, smt (z3) comp_associative2 g_def id_right_unit2 terminal_func_comp_elem terminal_func_type)
        then obtain k where k_type[type_rule]: "k \<in>\<^sub>c E" and k_def: "e \<circ>\<^sub>c k = j"
          by (typecheck_cfuncs, metis E_def fj_true)
        then have "j factorsthru e"
          using e_type factors_through_def2 j_type by auto
        then show "j \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (E, e)"
          by (simp add:  e_type j_type mono_e relative_member_def2)
      qed
  
      have "\<And>j. (j \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (f \<circ>\<^sub>c j = \<t>) = (successor \<circ>\<^sub>c n \<le>\<^sub>\<nat> m \<cdot>\<^sub>\<nat> j))"
      proof(auto) 
        fix j
        assume j_type[type_rule]: "j \<in>\<^sub>c \<nat>\<^sub>c"
        assume "f \<circ>\<^sub>c j = \<t>"
        then show "successor \<circ>\<^sub>c n \<le>\<^sub>\<nat> m \<cdot>\<^sub>\<nat> j"
          using assms unfolding f_def  by (-,typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2 id_right_unit2 leq_infix_def mult_apply1right terminal_func_comp_elem)
      next
        fix j 
        assume j_type[type_rule]: "j \<in>\<^sub>c \<nat>\<^sub>c"
        assume "successor \<circ>\<^sub>c n \<le>\<^sub>\<nat> m \<cdot>\<^sub>\<nat> j"
        then show "f \<circ>\<^sub>c j = \<t>"
          using assms unfolding f_def by (-, typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2 id_right_unit2 leq_infix_def mult_apply1right terminal_func_comp_elem)
      qed
      then show "\<And>j. (j \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (j  \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (E,e)) = (successor \<circ>\<^sub>c n \<le>\<^sub>\<nat> m \<cdot>\<^sub>\<nat> j))"
        by (simp add: f1)
    qed
  
    have "successor \<circ>\<^sub>c n \<le>\<^sub>\<nat> m \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c n)" 
      by (typecheck_cfuncs, smt (z3) add_monotonic add_respects_succ2 add_respects_zero_on_left assms(3) leq_infix_def lqe_connexity mult_monotonic nonzero_is_succ s0_is_left_id succ_n_type zero_is_smallest zero_type assms)  
    then have "(successor \<circ>\<^sub>c n) \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (E,e)"
      by (simp add: assms(1) satisfying_set succ_n_type)  
    then have "nonempty E"
      by (meson  factors_through_def2 nonempty_def relative_member_def2) 
    have  "(E,e) \<subseteq>\<^sub>c \<nat>\<^sub>c"
       using \<open>successor \<circ>\<^sub>c n \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (E, e)\<close> relative_member_def2 subobject_of_def2 by blast
    then obtain min where min_type[type_rule]: "min \<in>\<^sub>c \<nat>\<^sub>c" and min_rel_type: "min \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (E, e)" and m_def: "\<forall> s. s \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (E, e) \<longrightarrow> min  \<le>\<^sub>\<nat> s"
      by (metis  \<open>nonempty E\<close> relative_member_def2 well_ordering_principle)  
    then have "min \<noteq> zero"
      using assms(1) assms(2) leq_infix_def mult_respects_zero_right nat_strict_total_order satisfying_set zero_is_smallest by force
    then obtain q where q_type[type_rule]: "q \<in>\<^sub>c \<nat>\<^sub>c" and q_def: "successor \<circ>\<^sub>c q = min"
      using min_type nonzero_is_succ by blast
    then have "q \<cdot>\<^sub>\<nat> m \<le>\<^sub>\<nat> n"  
      by (typecheck_cfuncs, metis satisfying_set m_def min_rel_type min_type mult_commutative nat_strict_total_order q_def assms(1,2))
    then obtain r where r_type[type_rule]: "r \<in>\<^sub>c \<nat>\<^sub>c" and r_def: "r +\<^sub>\<nat> (q \<cdot>\<^sub>\<nat> m) = n"
      using assms by (typecheck_cfuncs, metis leq_infix_def leq_true_implies_exists)
    have r_bnd: "successor \<circ>\<^sub>c r \<le>\<^sub>\<nat> m"
    proof(rule ccontr)
      assume "\<not> successor \<circ>\<^sub>c r \<le>\<^sub>\<nat> m"
      then have "m \<le>\<^sub>\<nat> r"
        by (simp add: assms(2) nat_strict_total_order r_type)
      then obtain k where k_type[type_rule]: "k \<in>\<^sub>c \<nat>\<^sub>c" and k_def: "r = m +\<^sub>\<nat> k"
        by (metis add_commutes assms(2) leq_infix_def leq_true_implies_exists r_type)    
      then have "(m +\<^sub>\<nat> k) +\<^sub>\<nat> (m \<cdot>\<^sub>\<nat> q) = n"
        using assms k_def mult_commutative r_def by (typecheck_cfuncs, presburger)
      then have "((successor \<circ>\<^sub>c q) \<cdot>\<^sub>\<nat> m) +\<^sub>\<nat> k = n"
        using assms add_associates add_commutes k_def mult_closure mult_commutative mult_respects_succ_right r_def by (typecheck_cfuncs, force)
      then have "min \<cdot>\<^sub>\<nat> m \<le>\<^sub>\<nat> n"
        by (typecheck_cfuncs, metis add_respects_zero_on_left exists_implies_leq_true fewer_is_less k_type leq_infix_def q_def zero_type assms(1,2))
      then show False
        using assms(1,2) min_rel_type min_type mult_closure mult_commutative nat_strict_total_order satisfying_set by force
    qed
    have uniqueness: "\<forall>s t. s \<in>\<^sub>c \<nat>\<^sub>c \<and> t \<in>\<^sub>c \<nat>\<^sub>c \<and> n = m \<cdot>\<^sub>\<nat> s +\<^sub>\<nat> t \<and> successor \<circ>\<^sub>c t \<le>\<^sub>\<nat> m \<longrightarrow> s = q \<and> t = r"
    proof(auto)
      fix q' r'
      assume q'_type[type_rule]: "q' \<in>\<^sub>c \<nat>\<^sub>c"
      assume r'_type[type_rule]: "r' \<in>\<^sub>c \<nat>\<^sub>c"
      assume alt_sol: "n = m \<cdot>\<^sub>\<nat> q' +\<^sub>\<nat> r'"
      assume "successor \<circ>\<^sub>c r' \<le>\<^sub>\<nat> m"
      show "q' = q"
      proof(cases "q \<le>\<^sub>\<nat> q'")
        assume "q \<le>\<^sub>\<nat> q'"
        then obtain j where j_type[type_rule]: "j \<in>\<^sub>c \<nat>\<^sub>c" and j_def: "q +\<^sub>\<nat> j = q'"
          by (metis add_commutes leq_infix_def leq_true_implies_exists q'_type q_type)        
        show "q' = q"
        proof(cases "r' \<le>\<^sub>\<nat> r")
          assume "r' \<le>\<^sub>\<nat> r"
          then obtain k where k_type[type_rule]: "k \<in>\<^sub>c \<nat>\<^sub>c" and k_def: "r' +\<^sub>\<nat> k = r"
            by (metis add_commutes leq_infix_def leq_true_implies_exists r'_type r_type)
  
          have "r = (j\<cdot>\<^sub>\<nat> m) +\<^sub>\<nat> r'"
          proof - 
            have "((j \<cdot>\<^sub>\<nat> m) +\<^sub>\<nat> r') +\<^sub>\<nat> (q'\<cdot>\<^sub>\<nat> m) = (j \<cdot>\<^sub>\<nat> m) +\<^sub>\<nat> (r' +\<^sub>\<nat> (q'\<cdot>\<^sub>\<nat> m))"
              using assms(2) add_associates by (typecheck_cfuncs, presburger)
            also have "... = (j \<cdot>\<^sub>\<nat> m) +\<^sub>\<nat> ((q\<cdot>\<^sub>\<nat> m)  +\<^sub>\<nat> r)"
              using assms(2) add_commutes alt_sol mult_commutative r_def by (typecheck_cfuncs, force)
            also have "... = ((j \<cdot>\<^sub>\<nat> m) +\<^sub>\<nat> (q\<cdot>\<^sub>\<nat> m))  +\<^sub>\<nat> r"
              by (typecheck_cfuncs, simp add: add_associates assms(2))
            also have "... = ((j +\<^sub>\<nat> q) \<cdot>\<^sub>\<nat> m)  +\<^sub>\<nat> r"
              by (typecheck_cfuncs, simp add: mult_Left_Distributivity assms(2))
            also have "... = (q' \<cdot>\<^sub>\<nat> m)  +\<^sub>\<nat> r"
              using assms(2) add_commutes j_def by (typecheck_cfuncs, presburger)
            then show ?thesis
              by (typecheck_cfuncs, smt (z3) add_cancellative add_commutes add_type calculation j_def mult_closure q_type assms(2))
          qed
          then have k_eq_mj: "k = m  \<cdot>\<^sub>\<nat> j"
            using assms(2)  by (typecheck_cfuncs, metis add_cancellative add_commutes  k_def mult_commutative r'_type)
          have "j = zero"
          proof(rule ccontr)
            assume BWOC: "j \<noteq> zero"
            then have "m \<le>\<^sub>\<nat> k"
              by (metis BWOC k_eq_mj add_respects_zero_on_left exists_implies_leq_true fewer_is_less j_type leq_infix_def mult_respects_succ_right mult_type nonzero_is_succ assms(2))
            have "k \<le>\<^sub>\<nat> r"
              using exists_implies_leq_true k_def k_type leq_infix_def r'_type r_type by blast
            then have "k \<noteq> k"
              by (typecheck_cfuncs, metis  \<open>m \<le>\<^sub>\<nat> k\<close> r_bnd add_commutes assms(2) fewer_is_less leq_infix_def leq_true_implies_exists nat_strict_total_order r_type)
            then show False
              by simp
          qed
          show "q'=q"
            using \<open>j = zero\<close> add_respects_zero_on_right j_def q_type by blast
        next
          assume "\<not> r' \<le>\<^sub>\<nat> r"
          then have "r \<le>\<^sub>\<nat> r'"
            by (typecheck_cfuncs, meson leq_infix_def lqe_connexity)
          then obtain k where k_type[type_rule]: "k \<in>\<^sub>c \<nat>\<^sub>c" and k_def: "r +\<^sub>\<nat> k = r'"
            by (metis add_commutes leq_infix_def leq_true_implies_exists r'_type r_type)
          
          have f1: "(m \<cdot>\<^sub>\<nat> q) +\<^sub>\<nat> r =  m \<cdot>\<^sub>\<nat> (q +\<^sub>\<nat> j) +\<^sub>\<nat> r'"
            using add_commutes alt_sol j_def mult_commutative r_def assms(2) by (typecheck_cfuncs, presburger)
          also have "... = ((m \<cdot>\<^sub>\<nat> q) +\<^sub>\<nat> (m \<cdot>\<^sub>\<nat> j)) +\<^sub>\<nat> r'"
            by (typecheck_cfuncs, simp add: mult_right_distributivity assms(2))
          also have "... = (m \<cdot>\<^sub>\<nat> q) +\<^sub>\<nat> ((m \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> (r +\<^sub>\<nat> k))"
            using assms(2) add_associates k_def by (typecheck_cfuncs, presburger)
          also have "... = (m \<cdot>\<^sub>\<nat> q) +\<^sub>\<nat> ((r +\<^sub>\<nat> k) +\<^sub>\<nat> (m \<cdot>\<^sub>\<nat> j))"
            by (typecheck_cfuncs, simp add: add_commutes assms(2))
          also have "... = (m \<cdot>\<^sub>\<nat> q) +\<^sub>\<nat> (r +\<^sub>\<nat> (k +\<^sub>\<nat> (m \<cdot>\<^sub>\<nat> j)))"
            using assms(2) add_associates by (typecheck_cfuncs, presburger)
          also have "... = ((m \<cdot>\<^sub>\<nat> q) +\<^sub>\<nat> r) +\<^sub>\<nat> (k +\<^sub>\<nat> (m \<cdot>\<^sub>\<nat> j))"
            using assms(2) by (typecheck_cfuncs, meson add_associates)
          then have "k +\<^sub>\<nat> (m \<cdot>\<^sub>\<nat> j) = zero"
            by (metis  add_cancellative add_commutes add_respects_zero_on_right add_type alt_sol assms(1,2) f1 calculation j_def j_type k_type mult_type zero_type)
          then have "k = zero"
            by (typecheck_cfuncs, metis add_respects_zero_on_left assms(2) exists_implies_leq_true fewer_is_less j_type leq_infix_def mult_type nat_strict_total_order nonzero_is_succ)
          then show ?thesis
            using \<open>\<not> r' \<le>\<^sub>\<nat> r\<close> \<open>r \<le>\<^sub>\<nat> r'\<close> add_respects_zero_on_right k_def r_type by force
        qed
      next
        assume "\<not> q \<le>\<^sub>\<nat> q'"
        then have "q' \<le>\<^sub>\<nat> q"
          by (typecheck_cfuncs, meson leq_infix_def lqe_connexity)
        then obtain j where j_type[type_rule]: "j \<in>\<^sub>c \<nat>\<^sub>c" and j_def: "q' +\<^sub>\<nat> j = q"
          by (metis add_commutes leq_infix_def leq_true_implies_exists q'_type q_type)        
         show "q' = q"
        proof(cases "r' \<le>\<^sub>\<nat> r")
          assume "r' \<le>\<^sub>\<nat> r"
          then obtain k where k_type[type_rule]: "k \<in>\<^sub>c \<nat>\<^sub>c" and k_def: "r' +\<^sub>\<nat> k = r"
            by (metis add_commutes leq_infix_def leq_true_implies_exists r'_type r_type)
          have "(m \<cdot>\<^sub>\<nat> q) +\<^sub>\<nat> r = m \<cdot>\<^sub>\<nat> (q' +\<^sub>\<nat> j) +\<^sub>\<nat> r"
            using assms(2) j_def k_def by blast
          also have "... = ((m \<cdot>\<^sub>\<nat> q') +\<^sub>\<nat> (m \<cdot>\<^sub>\<nat>j )) +\<^sub>\<nat> r" 
             by (typecheck_cfuncs, smt assms(2) mult_right_distributivity)
          also have "... = ((m \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> (m \<cdot>\<^sub>\<nat> q')) +\<^sub>\<nat> r" 
             by (typecheck_cfuncs, simp add: add_commutes assms(2))
          also have "... = (m \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> ((m \<cdot>\<^sub>\<nat> q') +\<^sub>\<nat> r)" 
             by (typecheck_cfuncs, simp add: add_associates assms(2))
          also have "... = (m \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> (((m \<cdot>\<^sub>\<nat> q') +\<^sub>\<nat> r') +\<^sub>\<nat> k)" 
             by (typecheck_cfuncs, metis add_associates k_def assms(2))     
          also have "... = (m \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> (((m \<cdot>\<^sub>\<nat> q) +\<^sub>\<nat> r)  +\<^sub>\<nat> k)" 
            using assms(2)  add_commutes alt_sol mult_commutative r_def by (typecheck_cfuncs, presburger)
          also have "... = ((m \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> ((m \<cdot>\<^sub>\<nat> q) +\<^sub>\<nat> r))  +\<^sub>\<nat> k" 
            by (typecheck_cfuncs, meson add_associates assms(2))
          also have "... = ((m \<cdot>\<^sub>\<nat> q) +\<^sub>\<nat> r) +\<^sub>\<nat>  ((m \<cdot>\<^sub>\<nat> j)  +\<^sub>\<nat> k)" 
            by (typecheck_cfuncs, metis add_associates4 add_commutes assms(2))
          then have "((m \<cdot>\<^sub>\<nat> j)  +\<^sub>\<nat> k) = zero"
            by (typecheck_cfuncs, metis  add_cancellative add_commutes add_respects_zero_on_left assms(1,2) calculation mult_commutative mult_type q_type r_def r_type)
          then have "j = zero"  
            by (typecheck_cfuncs, metis assms(2,3) fewer_is_less k_type l_mult_cancellative leq_infix_def lqe_antisymmetry mult_respects_zero_right mult_type zero_is_smallest)
          then show ?thesis
            using add_respects_zero_on_right j_def q'_type by auto
        next
          assume "\<not> r' \<le>\<^sub>\<nat> r"
          then have "r \<le>\<^sub>\<nat> r'"
            by (typecheck_cfuncs, meson leq_infix_def lqe_connexity)
          then obtain k where k_type[type_rule]: "k \<in>\<^sub>c \<nat>\<^sub>c" and k_def: "r +\<^sub>\<nat> k = r'"
            by (metis add_commutes leq_infix_def leq_true_implies_exists r'_type r_type)
          have "r' = (j\<cdot>\<^sub>\<nat> m) +\<^sub>\<nat> r"
          proof - 
            have "((j \<cdot>\<^sub>\<nat> m) +\<^sub>\<nat> (q\<cdot>\<^sub>\<nat> m))  +\<^sub>\<nat> r' = ((j \<cdot>\<^sub>\<nat> m) +\<^sub>\<nat> r') +\<^sub>\<nat> (q\<cdot>\<^sub>\<nat> m)"
              using assms(2) add_associates add_commutes by (typecheck_cfuncs, presburger)
            also have "... = (j \<cdot>\<^sub>\<nat> m) +\<^sub>\<nat> (r' +\<^sub>\<nat> (q\<cdot>\<^sub>\<nat> m))"
              using assms(2) add_associates by (typecheck_cfuncs, presburger)
            also have "... = (j \<cdot>\<^sub>\<nat> m) +\<^sub>\<nat> ((q\<cdot>\<^sub>\<nat> m)  +\<^sub>\<nat> r')"
              using assms(2) add_commutes alt_sol mult_commutative r_def by (typecheck_cfuncs, force)
            also have "... = (j \<cdot>\<^sub>\<nat> m) +\<^sub>\<nat> (((q'\<cdot>\<^sub>\<nat> m)  +\<^sub>\<nat> (j \<cdot>\<^sub>\<nat>m))  +\<^sub>\<nat> r')"
              using assms(2) j_def mult_Left_Distributivity by (typecheck_cfuncs, force)
            also have "... = (j \<cdot>\<^sub>\<nat> m) +\<^sub>\<nat> (((j \<cdot>\<^sub>\<nat>m)  +\<^sub>\<nat> (q'\<cdot>\<^sub>\<nat> m))  +\<^sub>\<nat> r')"
              using assms(2)  add_commutes by (typecheck_cfuncs, presburger)          
            also have "... = (j \<cdot>\<^sub>\<nat> m) +\<^sub>\<nat> ((j \<cdot>\<^sub>\<nat> m)  +\<^sub>\<nat> ((q\<cdot>\<^sub>\<nat> m)  +\<^sub>\<nat> r))"
              using assms(2) add_associates add_commutes alt_sol mult_commutative r_def by (typecheck_cfuncs, force)
            also have "... = (j \<cdot>\<^sub>\<nat> m) +\<^sub>\<nat> (((q\<cdot>\<^sub>\<nat> m)  +\<^sub>\<nat> r)  +\<^sub>\<nat>(j \<cdot>\<^sub>\<nat> m) )"
              using assms(2)  by (typecheck_cfuncs, simp add: add_commutes)
            also have "... = ((j \<cdot>\<^sub>\<nat> m) +\<^sub>\<nat> (q\<cdot>\<^sub>\<nat> m)) +\<^sub>\<nat> (r  +\<^sub>\<nat>(j \<cdot>\<^sub>\<nat> m) )"
              using assms(2) add_associates by (typecheck_cfuncs, presburger)
            also have "... = ((j \<cdot>\<^sub>\<nat> m) +\<^sub>\<nat> (q\<cdot>\<^sub>\<nat> m)) +\<^sub>\<nat> ((j \<cdot>\<^sub>\<nat> m)  +\<^sub>\<nat> r )"
              using assms(2) add_commutes by (typecheck_cfuncs, presburger)
            then show ?thesis
              by (typecheck_cfuncs, smt (z3) add_cancellative add_commutes add_type calculation j_def mult_closure q_type assms(2))
          qed
          then have k_eq_mj: "k = m  \<cdot>\<^sub>\<nat> j"
            by (typecheck_cfuncs, metis add_cancellative add_commutes assms(2) k_def mult_commutative r_type)
          have "j = zero"
          proof(rule ccontr)
            assume BWOC: "j \<noteq> zero"
            then have "m \<le>\<^sub>\<nat> k"
              by (metis BWOC k_eq_mj add_respects_zero_on_left exists_implies_leq_true fewer_is_less j_type leq_infix_def mult_respects_succ_right mult_type nonzero_is_succ assms(2))
            have "k \<le>\<^sub>\<nat> r'"
              using exists_implies_leq_true k_def k_type leq_infix_def r'_type r_type by blast
            then have "k \<noteq> k"
              by (typecheck_cfuncs, metis \<open>m \<le>\<^sub>\<nat> k\<close> \<open>r' = j \<cdot>\<^sub>\<nat> m +\<^sub>\<nat> r\<close> \<open>successor \<circ>\<^sub>c r' \<le>\<^sub>\<nat> m\<close> assms(2,3) k_eq_mj fewer_is_less j_type mult_commutative nat_strict_total_order nonzero_is_succ r'_type r_type)
            then show False
              by simp
          qed
          show "q'=q"
            using \<open>j = zero\<close> add_respects_zero_on_right j_def q'_type by auto 
        qed
      qed
      then show "r' = r"
        by (metis add_cancellative add_commutes alt_sol assms(2) mult_commutative mult_type q'_type r'_type r_def r_type)
    qed
  then show ?thesis     
    by (rule_tac x=q in exI, rule_tac x=r in exI, typecheck_cfuncs, smt add_commutes assms(2) mult_commutative r_bnd r_def )
qed




lemma product_of_canonically_finite_sets:
  assumes n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c" and m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c"
  shows "[n \<cdot>\<^sub>\<nat> m]\<^sub>c \<cong> [n]\<^sub>c \<times>\<^sub>c [m]\<^sub>c"
proof(cases "m = zero")
  show "m = zero \<Longrightarrow> [n \<cdot>\<^sub>\<nat> m]\<^sub>c \<cong> [n]\<^sub>c \<times>\<^sub>c [m]\<^sub>c"
    by (typecheck_cfuncs, metis is_empty_def cart_prod_decomp isomorphic_is_symmetric isomorphic_is_transitive mult_respects_zero_right no_el_iff_iso_0 zero_canonically_finite_set_empty)
next
  assume "m \<noteq> zero"
  obtain \<phi> where \<phi>_type[type_rule]: "\<phi> : [n]\<^sub>c \<times>\<^sub>c [m]\<^sub>c \<rightarrow> \<nat>\<^sub>c" and
    \<phi>_def: "\<phi> = add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c \<beta>\<^bsub>[n]\<^sub>c \<times>\<^sub>c [m]\<^sub>c\<^esub>, (canonically_finite_morphism n) \<circ>\<^sub>c (left_cart_proj [n]\<^sub>c [m]\<^sub>c)\<rangle>, (canonically_finite_morphism m) \<circ>\<^sub>c (right_cart_proj [n]\<^sub>c [m]\<^sub>c)\<rangle>"
    by typecheck_cfuncs
  have phi_action: "\<And> j k. j \<in>\<^sub>c \<nat>\<^sub>c \<and> k \<in>\<^sub>c \<nat>\<^sub>c \<and> successor \<circ>\<^sub>c j \<le>\<^sub>\<nat> n \<and> successor \<circ>\<^sub>c k  \<le>\<^sub>\<nat> m \<longrightarrow> \<phi> \<circ>\<^sub>c \<langle>\<lbrakk>j:n\<rbrakk>\<^sub>c, \<lbrakk>k:m\<rbrakk>\<^sub>c\<rangle> = (m \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> k"
  proof(unfold \<phi>_def, auto)
    fix j k 
    assume j_type[type_rule]: "j \<in>\<^sub>c \<nat>\<^sub>c"
    assume k_type[type_rule]: "k \<in>\<^sub>c \<nat>\<^sub>c"
    assume j_bnd: "successor \<circ>\<^sub>c j \<le>\<^sub>\<nat> n"
    assume k_bnd: "successor \<circ>\<^sub>c k \<le>\<^sub>\<nat> m"   

    (*James.... we, in fact, need all three of these.... an opportunity for improvement!*)
    have type1[type_rule]: "\<lbrakk>j:n\<rbrakk>\<^sub>c  \<in>\<^sub>c [n]\<^sub>c"
      by (simp add: elem_canon_finite_set j_bnd j_type n_type)
    have type2[type_rule]: "\<lbrakk>k:m\<rbrakk>\<^sub>c \<in>\<^sub>c [m]\<^sub>c"
      by (simp add: elem_canon_finite_set k_bnd k_type m_type)
    have type_info[type_rule]: "\<langle>\<lbrakk>j:n\<rbrakk>\<^sub>c, \<lbrakk>k:m\<rbrakk>\<^sub>c\<rangle> \<in>\<^sub>c [n]\<^sub>c \<times>\<^sub>c [m]\<^sub>c"
      by (simp add: cfunc_prod_type type1 type2)


    have "(add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c  \<langle>m \<circ>\<^sub>c \<beta>\<^bsub>([n]\<^sub>c \<times>\<^sub>c [m]\<^sub>c)\<^esub>,canonically_finite_morphism n \<circ>\<^sub>c left_cart_proj [n]\<^sub>c [m]\<^sub>c\<rangle>,canonically_finite_morphism m \<circ>\<^sub>c right_cart_proj [n]\<^sub>c [m]\<^sub>c\<rangle>) \<circ>\<^sub>c \<langle>\<lbrakk>j:n\<rbrakk>\<^sub>c,\<lbrakk>k:m\<rbrakk>\<^sub>c\<rangle> =
           add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c \<beta>\<^bsub>([n]\<^sub>c \<times>\<^sub>c [m]\<^sub>c)\<^esub> \<circ>\<^sub>c \<langle>\<lbrakk>j:n\<rbrakk>\<^sub>c,\<lbrakk>k:m\<rbrakk>\<^sub>c\<rangle>,canonically_finite_morphism n \<circ>\<^sub>c left_cart_proj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c \<langle>\<lbrakk>j:n\<rbrakk>\<^sub>c,\<lbrakk>k:m\<rbrakk>\<^sub>c\<rangle>\<rangle> ,canonically_finite_morphism m \<circ>\<^sub>c right_cart_proj [n]\<^sub>c [m]\<^sub>c \<circ>\<^sub>c \<langle>\<lbrakk>j:n\<rbrakk>\<^sub>c,\<lbrakk>k:m\<rbrakk>\<^sub>c\<rangle>\<rangle> "
      by (typecheck_cfuncs, smt (verit, best) cfunc_prod_comp comp_associative2)
    also have "... = (m \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> k"
      by (typecheck_cfuncs, simp add: add_def elem_canon_finite_def2 id_right_unit2 j_bnd k_bnd left_cart_proj_cfunc_prod mult_def right_cart_proj_cfunc_prod terminal_func_comp_elem)
    then show "(add2 \<circ>\<^sub>c \<langle>mult2 \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c \<beta>\<^bsub>[n]\<^sub>c \<times>\<^sub>c [m]\<^sub>c\<^esub>,canonically_finite_morphism n \<circ>\<^sub>c left_cart_proj [n]\<^sub>c [m]\<^sub>c\<rangle>,canonically_finite_morphism m \<circ>\<^sub>c right_cart_proj [n]\<^sub>c [m]\<^sub>c\<rangle>) \<circ>\<^sub>c  \<langle>\<lbrakk>j:n\<rbrakk>\<^sub>c,\<lbrakk>k:m\<rbrakk>\<^sub>c\<rangle> =  m \<cdot>\<^sub>\<nat> j +\<^sub>\<nat> k"
      by (simp add: calculation)
  qed

  have "injective \<phi>"
  proof (etcs_subst injective_def2, auto)
    fix x y 
    assume x_type[type_rule]: "x \<in>\<^sub>c [n]\<^sub>c \<times>\<^sub>c [m]\<^sub>c"
    assume y_type[type_rule]: "y \<in>\<^sub>c [n]\<^sub>c \<times>\<^sub>c [m]\<^sub>c"
    assume \<phi>_eq: "\<phi> \<circ>\<^sub>c x = \<phi> \<circ>\<^sub>c y"
    obtain x1 x2  where x1_type[type_rule]: "x1 \<in>\<^sub>c [n]\<^sub>c" and x2_type[type_rule]:"x2 \<in>\<^sub>c [m]\<^sub>c"    and                
                        x_def: "x = \<langle>x1, x2\<rangle>"
      using cart_prod_decomp by (typecheck_cfuncs, blast)
    obtain x1'  where x1'_type[type_rule]: "x1' \<in>\<^sub>c \<nat>\<^sub>c" and x1'_bnd: "successor \<circ>\<^sub>c x1' \<le>\<^sub>\<nat> n" and  x1_def: "x1 = \<lbrakk>x1':n\<rbrakk>\<^sub>c"            
      using elem_canon_finite_set_representation by (typecheck_cfuncs, blast)
    obtain x2'  where x2'_type[type_rule]: "x2' \<in>\<^sub>c \<nat>\<^sub>c" and x2'_bnd: "successor \<circ>\<^sub>c x2' \<le>\<^sub>\<nat> m" and  x2_def: "x2 = \<lbrakk>x2':m\<rbrakk>\<^sub>c"
      using elem_canon_finite_set_representation by (typecheck_cfuncs, blast)
    obtain y1 y2  where y1_type[type_rule]: "y1 \<in>\<^sub>c [n]\<^sub>c" and y2_type[type_rule]:"y2 \<in>\<^sub>c [m]\<^sub>c"    and                
                        y_def: "y = \<langle>y1, y2\<rangle>"
      using cart_prod_decomp by (typecheck_cfuncs, blast)
    obtain y1'  where y1'_type[type_rule]: "y1' \<in>\<^sub>c \<nat>\<^sub>c" and y1'_bnd: "successor \<circ>\<^sub>c y1' \<le>\<^sub>\<nat> n" and  y1_def: "y1 = \<lbrakk>y1':n\<rbrakk>\<^sub>c"            
      using elem_canon_finite_set_representation by (typecheck_cfuncs, blast)
    obtain y2'  where y2'_type[type_rule]: "y2' \<in>\<^sub>c \<nat>\<^sub>c" and y2'_bnd: "successor \<circ>\<^sub>c y2' \<le>\<^sub>\<nat> m" and  y2_def: "y2 = \<lbrakk>y2':m\<rbrakk>\<^sub>c"
      using elem_canon_finite_set_representation by (typecheck_cfuncs, blast)

    

    have lhs_eq: "\<phi> \<circ>\<^sub>c x = (m \<cdot>\<^sub>\<nat> x1') +\<^sub>\<nat> x2'"
      by (typecheck_cfuncs, simp add: x1'_bnd x2'_bnd phi_action x1_def x2_def x_def)

    have rhs_eq: "\<phi> \<circ>\<^sub>c y = (m \<cdot>\<^sub>\<nat> y1') +\<^sub>\<nat> y2'"
      by (typecheck_cfuncs, simp add: y1'_bnd y2'_bnd phi_action y1_def y2_def y_def)
    
    have "(m \<cdot>\<^sub>\<nat> x1') +\<^sub>\<nat> x2' = (m \<cdot>\<^sub>\<nat> y1') +\<^sub>\<nat> y2'"
      using \<phi>_eq lhs_eq rhs_eq by force
    then have "(x1' = y1') \<and> (x2' = y2')"
      using assms by (typecheck_cfuncs, metis Euclid's_division_lemma \<open>m \<noteq> zero\<close> \<phi>_eq add_type lhs_eq m_type mult_type rhs_eq x2'_bnd y2'_bnd)
    then show "x = y"
      using  x1_def x2_def x_def y1_def y2_def y_def by force
  qed

  have \<phi>_equalizes: "(leq \<circ>\<^sub>c \<langle>successor, (n \<cdot>\<^sub>\<nat> m)  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c  \<phi> = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c  \<phi>"
  proof(rule one_separator[where X = "[n]\<^sub>c \<times>\<^sub>c [m]\<^sub>c", where Y = \<Omega>])
    show "(leq \<circ>\<^sub>c \<langle>successor,n \<cdot>\<^sub>\<nat> m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c \<phi> : [n]\<^sub>c \<times>\<^sub>c [m]\<^sub>c \<rightarrow> \<Omega>"
      by typecheck_cfuncs
    show "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c \<phi> : [n]\<^sub>c \<times>\<^sub>c [m]\<^sub>c \<rightarrow> \<Omega>"
      by typecheck_cfuncs
  next
    fix x 
    assume x_type[type_rule]: "x \<in>\<^sub>c [n]\<^sub>c \<times>\<^sub>c [m]\<^sub>c"
    then obtain x1 x2 where x1_type[type_rule]: "x1 \<in>\<^sub>c [n]\<^sub>c" and x2_type[type_rule]: "x2 \<in>\<^sub>c [m]\<^sub>c" and x_def: "x = \<langle>x1,x2\<rangle>"
      using cart_prod_decomp by blast        
    then obtain j k where j_type[type_rule]: "j \<in>\<^sub>c \<nat>\<^sub>c" and  x1_def: "x1 = \<lbrakk>j:n\<rbrakk>\<^sub>c" and j_bnd: "successor \<circ>\<^sub>c j \<le>\<^sub>\<nat> n" and
                          k_type[type_rule]: "k \<in>\<^sub>c \<nat>\<^sub>c" and  x2_def: "x2 = \<lbrakk>k:m\<rbrakk>\<^sub>c" and k_bnd: "successor \<circ>\<^sub>c k \<le>\<^sub>\<nat> m"
      by (metis assms elem_canon_finite_set_representation)


    
    have \<phi>_x: "\<phi> \<circ>\<^sub>c x = (m \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> k"
      by (typecheck_cfuncs, simp add: j_bnd k_bnd phi_action x1_def x2_def x_def)

    have "((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c x = \<t>"
      by (typecheck_cfuncs, smt (z3) comp_associative2 id_right_unit2 terminal_func_comp terminal_func_comp_elem terminal_func_type)
    also have "... = leq \<circ>\<^sub>c \<langle> m \<cdot>\<^sub>\<nat>  (successor \<circ>\<^sub>c j) ,n \<cdot>\<^sub>\<nat> m\<rangle>"
      by (typecheck_cfuncs, metis j_bnd leq_infix_def lqe_connexity mult_commutative mult_monotonic)
    also have "... = leq \<circ>\<^sub>c \<langle> (m \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> m ,n \<cdot>\<^sub>\<nat> m\<rangle>"
      using add_commutes mult_respects_succ_right by (typecheck_cfuncs, presburger)
    also have "... = leq \<circ>\<^sub>c \<langle> (m \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> (successor \<circ>\<^sub>c k) ,n \<cdot>\<^sub>\<nat> m\<rangle>"
      by (typecheck_cfuncs, metis \<open>\<t> = leq \<circ>\<^sub>c \<langle>m \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c j),n \<cdot>\<^sub>\<nat> m\<rangle>\<close> \<open>leq \<circ>\<^sub>c \<langle>m \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c j),n \<cdot>\<^sub>\<nat> m\<rangle> = leq \<circ>\<^sub>c \<langle>m \<cdot>\<^sub>\<nat> j +\<^sub>\<nat> m,n \<cdot>\<^sub>\<nat> m\<rangle>\<close> add_monotonic k_bnd leq_infix_def leq_transitivity lqe_connexity)
    also have "... = leq \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c ((m \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> k) ,n \<cdot>\<^sub>\<nat> m\<rangle>"
      using add_respects_succ1 by (typecheck_cfuncs, presburger)
    also have "... = leq \<circ>\<^sub>c \<langle>successor,n \<cdot>\<^sub>\<nat> m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c ((m \<cdot>\<^sub>\<nat> j) +\<^sub>\<nat> k)"
      by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2 id_right_unit2 terminal_func_comp_elem)
    also have "... = (leq \<circ>\<^sub>c \<langle>successor,n \<cdot>\<^sub>\<nat> m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c (\<phi> \<circ>\<^sub>c x)"
      by (typecheck_cfuncs, simp add: \<phi>_x comp_associative2)
    also have "... = ((leq \<circ>\<^sub>c \<langle>successor,n \<cdot>\<^sub>\<nat> m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c x"
      by (typecheck_cfuncs, meson comp_associative2)
    then show "((leq \<circ>\<^sub>c \<langle>successor,n \<cdot>\<^sub>\<nat> m \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c x = ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c x"
      by (simp add: calculation)
  qed



  then obtain \<psi> where \<psi>_type[type_rule]: "\<psi> : [n]\<^sub>c \<times>\<^sub>c [m]\<^sub>c \<rightarrow> [n \<cdot>\<^sub>\<nat> m]\<^sub>c" and \<psi>_def: "(canonically_finite_morphism (n \<cdot>\<^sub>\<nat> m)) \<circ>\<^sub>c \<psi> = \<phi>"
    using equalizer_def2 by (-,typecheck_cfuncs, metis canonically_finite_morphism_def2)

  then have \<psi>_mono: "monomorphism \<psi>"
    by (metis \<open>injective \<phi>\<close> canonically_finite_morphism_type comp_monic_imp_monic' injective_imp_monomorphism m_type mem_Collect_eq mult_type n_type)

  have "surjective \<psi>"
  proof(etcs_subst surjective_def2, auto)
    fix y 
    assume y_type[type_rule]: "y \<in>\<^sub>c [n \<cdot>\<^sub>\<nat> m]\<^sub>c"
    then obtain k where k_type[type_rule]: "k \<in>\<^sub>c \<nat>\<^sub>c" and y_rep: "y = \<lbrakk>k:n \<cdot>\<^sub>\<nat> m\<rbrakk>\<^sub>c" and k_bnd: "successor \<circ>\<^sub>c k \<le>\<^sub>\<nat> n \<cdot>\<^sub>\<nat> m"
      by (metis elem_canon_finite_set_representation m_type mult_closure n_type)
    
    then obtain q r where q_type[type_rule]: "q \<in>\<^sub>c \<nat>\<^sub>c" and r_type[type_rule]: "r \<in>\<^sub>c \<nat>\<^sub>c"
        and k_def: "(k = (m \<cdot>\<^sub>\<nat> q) +\<^sub>\<nat> r) \<and> (successor  \<circ>\<^sub>c r \<le>\<^sub>\<nat> m)" 
        and uniqueness_of_qr:  "\<forall> s t. (s \<in>\<^sub>c \<nat>\<^sub>c) \<and> (t \<in>\<^sub>c \<nat>\<^sub>c) \<and> (k = (m \<cdot>\<^sub>\<nat> s) +\<^sub>\<nat> t) \<and> (successor  \<circ>\<^sub>c t \<le>\<^sub>\<nat> m) \<longrightarrow> (s=q) \<and> (t=r)"
      by (metis Euclid's_division_lemma \<open>m \<noteq> zero\<close> m_type)

    have q_bnd: "successor  \<circ>\<^sub>c q \<le>\<^sub>\<nat> n"   
    proof(rule ccontr)
      assume "\<not> successor \<circ>\<^sub>c q \<le>\<^sub>\<nat> n"
      then have n_leq_q: "n \<le>\<^sub>\<nat> q"
        by (simp add: n_type nat_strict_total_order q_type)
      then have "successor \<circ>\<^sub>c k \<le>\<^sub>\<nat> m \<cdot>\<^sub>\<nat> n"
        using k_bnd m_type mult_commutative n_type by auto
      then have "m \<cdot>\<^sub>\<nat> n \<le>\<^sub>\<nat> m \<cdot>\<^sub>\<nat> q"
        by (typecheck_cfuncs, meson leq_infix_def lqe_connexity mult_monotonic n_leq_q)
      have "m \<cdot>\<^sub>\<nat> q \<le>\<^sub>\<nat> k" 
        by (typecheck_cfuncs, metis add_respects_zero_on_left exists_implies_leq_true fewer_is_less k_def leq_infix_def r_type zero_type) 
      then have "successor \<circ>\<^sub>c k \<le>\<^sub>\<nat> k"
        by (typecheck_cfuncs, smt (z3) \<open>m \<cdot>\<^sub>\<nat> n \<le>\<^sub>\<nat> m \<cdot>\<^sub>\<nat> q\<close>  k_bnd leq_infix_def leq_transitivity m_type mult_closure mult_commutative n_type q_type)
      then show False
        using k_type leq_infix_def lqe_connexity nat_strict_total_order by blast
    qed




   
  
    have \<phi>_x: "\<phi> \<circ>\<^sub>c   \<langle>\<lbrakk>q:n\<rbrakk>\<^sub>c, \<lbrakk>r:m\<rbrakk>\<^sub>c\<rangle> = (m \<cdot>\<^sub>\<nat> q) +\<^sub>\<nat> r"
      by (typecheck_cfuncs, simp add: k_def phi_action q_bnd)
    

    then have "canonically_finite_morphism (n \<cdot>\<^sub>\<nat> m) \<circ>\<^sub>c (\<psi> \<circ>\<^sub>c \<langle>\<lbrakk>q:n\<rbrakk>\<^sub>c, \<lbrakk>r:m\<rbrakk>\<^sub>c\<rangle>) = canonically_finite_morphism (n \<cdot>\<^sub>\<nat> m) \<circ>\<^sub>c \<lbrakk>k:n \<cdot>\<^sub>\<nat> m\<rbrakk>\<^sub>c"
      by (typecheck_cfuncs, metis \<phi>_x \<psi>_def cfunc_type_def comp_associative elem_canon_finite_def2 k_bnd k_def q_bnd)

    then show "\<exists>x. x \<in>\<^sub>c [n]\<^sub>c \<times>\<^sub>c [m]\<^sub>c \<and> \<psi> \<circ>\<^sub>c x = y"
      by (rule_tac x="\<langle>\<lbrakk>q:n\<rbrakk>\<^sub>c, \<lbrakk>r:m\<rbrakk>\<^sub>c\<rangle>" in exI, typecheck_cfuncs, metis canonically_finite_morph_mono k_def monomorphism_def2 q_bnd y_rep)    
  qed
  then show ?thesis
    using \<psi>_mono \<psi>_type epi_mon_is_iso is_isomorphic_def isomorphic_is_symmetric surjective_is_epimorphism by blast
qed











(*I think we also have the following:   "A \<cong> A \<setminus> (\<nat>\<^sub>c,f)" .... or maybe we want A \<cong> h(A)  *)


theorem Herrlichs_finiteness_criterion: 
  "is_finite A = (\<nexists> f. f: \<nat>\<^sub>c \<rightarrow> A \<and> injective f)"
proof(auto)
  fix f 
  assume A_finite: "is_finite A"
  assume f_type[type_rule]: "f : \<nat>\<^sub>c \<rightarrow> A"
  assume f_inj: "injective f"

  obtain h where h_def: "h = (f \<circ>\<^sub>c successor ) \<amalg> (f\<^sup>c ) \<circ>\<^sub>c try_cast f" and h_type[type_rule]: "h: A \<rightarrow> A"
    using f_inj injective_imp_monomorphism by (typecheck_cfuncs, blast)

  have a_eq_fn: "\<And>q. q \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>  h \<circ>\<^sub>c f \<circ>\<^sub>c q = f \<circ>\<^sub>c successor \<circ>\<^sub>c q"
  proof - 
    fix q 
    assume q_type[type_rule]: "q \<in>\<^sub>c \<nat>\<^sub>c"
    have fq_in: "f \<circ>\<^sub>c q \<in>\<^bsub>A\<^esub> (\<nat>\<^sub>c, f)"
      by (typecheck_cfuncs, metis f_inj factors_through_def2 injective_imp_monomorphism mem_Collect_eq relative_member_def2)
    have try_fq: "try_cast f \<circ>\<^sub>c f \<circ>\<^sub>c q = left_coproj \<nat>\<^sub>c (A \<setminus> (\<nat>\<^sub>c, f)) \<circ>\<^sub>c q"
        by (typecheck_cfuncs, metis comp_associative2 f_inj injective_imp_monomorphism mem_Collect_eq try_cast_m_m) 
    have "h \<circ>\<^sub>c f \<circ>\<^sub>c q = (f \<circ>\<^sub>c successor ) \<amalg> (f\<^sup>c ) \<circ>\<^sub>c  try_cast f \<circ>\<^sub>c f \<circ>\<^sub>c q "
      using comp_associative2 f_inj h_def injective_imp_monomorphism by (typecheck_cfuncs, fastforce)
    also have "... = (f \<circ>\<^sub>c successor ) \<amalg> (f\<^sup>c ) \<circ>\<^sub>c left_coproj \<nat>\<^sub>c (A \<setminus> (\<nat>\<^sub>c, f)) \<circ>\<^sub>c q"
      using try_fq by (typecheck_cfuncs, presburger)
    also have "... = ((f \<circ>\<^sub>c successor ) \<amalg> (f\<^sup>c ) \<circ>\<^sub>c left_coproj \<nat>\<^sub>c (A \<setminus> (\<nat>\<^sub>c, f))) \<circ>\<^sub>c q"
      by (typecheck_cfuncs, meson fq_in comp_associative2 relative_member_def2)
    also have "... = f \<circ>\<^sub>c successor \<circ>\<^sub>c q"
      by (typecheck_cfuncs, metis comp_associative2 fq_in left_coproj_cfunc_coprod relative_member_def2)
    then show  "h \<circ>\<^sub>c (f \<circ>\<^sub>c q) = f \<circ>\<^sub>c successor \<circ>\<^sub>c q"
      by (simp add: calculation)
  qed
  have a_neq_fn: "\<And>a. a \<in>\<^sub>c A \<Longrightarrow> (\<nexists>n. n \<in>\<^sub>c \<nat>\<^sub>c \<and> a = f  \<circ>\<^sub>c n) \<Longrightarrow> 
                                  (\<exists> b. b \<in>\<^sub>c A \<setminus> (\<nat>\<^sub>c,f) \<and> h \<circ>\<^sub>c a =  f\<^sup>c  \<circ>\<^sub>c b \<and> try_cast f \<circ>\<^sub>c a = right_coproj \<nat>\<^sub>c (A \<setminus> (\<nat>\<^sub>c,f)) \<circ>\<^sub>c b)"
  proof - 
    fix a 
    assume a_type[type_rule]: "a \<in>\<^sub>c A"
    assume a_not_in_fN: " \<nexists>n. n \<in>\<^sub>c \<nat>\<^sub>c \<and> a = f \<circ>\<^sub>c n"
    then have a_nin: "\<not> a  \<in>\<^bsub>A\<^esub> (\<nat>\<^sub>c, f)"
      using a_not_in_fN factors_through_def2 relative_member_def by auto
    then obtain b where b_type[type_rule]: "b \<in>\<^sub>c A \<setminus> (\<nat>\<^sub>c,f)" and b_def: "try_cast f \<circ>\<^sub>c a = right_coproj \<nat>\<^sub>c (A \<setminus> (\<nat>\<^sub>c,f)) \<circ>\<^sub>c b"
      by (typecheck_cfuncs, metis f_inj injective_imp_monomorphism mem_Collect_eq try_cast_not_in_X)

    have "h \<circ>\<^sub>c a =f\<^sup>c  \<circ>\<^sub>c b"
    proof - 
      have "h \<circ>\<^sub>c a = ((f \<circ>\<^sub>c successor ) \<amalg> f\<^sup>c ) \<circ>\<^sub>c try_cast f \<circ>\<^sub>c a"
        using comp_associative2 f_inj h_def injective_imp_monomorphism by (typecheck_cfuncs, fastforce)
      also have "... = ((f \<circ>\<^sub>c successor ) \<amalg> f\<^sup>c ) \<circ>\<^sub>c right_coproj \<nat>\<^sub>c (A \<setminus> (\<nat>\<^sub>c, f)) \<circ>\<^sub>c b"
        using b_def by presburger
      also have "... = (((f \<circ>\<^sub>c successor ) \<amalg> f\<^sup>c ) \<circ>\<^sub>c right_coproj \<nat>\<^sub>c (A \<setminus> (\<nat>\<^sub>c, f))) \<circ>\<^sub>c b"
        using comp_associative2 f_inj injective_imp_monomorphism by (typecheck_cfuncs, blast)
      also have "... = f\<^sup>c  \<circ>\<^sub>c b"
        by (typecheck_cfuncs, metis f_inj injective_imp_monomorphism right_coproj_cfunc_coprod singletonI)
      then show ?thesis
        by (simp add: calculation)
    qed

    then show "(\<exists> b. b \<in>\<^sub>c A \<setminus> (\<nat>\<^sub>c,f) \<and> h \<circ>\<^sub>c a =  f\<^sup>c  \<circ>\<^sub>c b \<and> try_cast f \<circ>\<^sub>c a = right_coproj \<nat>\<^sub>c (A \<setminus> (\<nat>\<^sub>c,f)) \<circ>\<^sub>c b)"
      using b_def b_type by blast
  qed

  have "(injective h)"
  proof(unfold injective_def, auto)
    fix x y
    assume x_type[type_rule]: "x \<in>\<^sub>c domain h" 
    assume y_type[type_rule]: "y \<in>\<^sub>c domain h"
    assume hx_eq_hy: "h \<circ>\<^sub>c x = h \<circ>\<^sub>c y"
    have x_type2[type_rule]: "x \<in>\<^sub>c A"
      using cfunc_type_def h_type by (typecheck_cfuncs, auto)
    have y_type2[type_rule]: "y \<in>\<^sub>c A"
       using cfunc_type_def h_type by (typecheck_cfuncs, auto)

      
    show "x=y"
    proof(cases "\<exists> n. n \<in>\<^sub>c \<nat>\<^sub>c \<and> f \<circ>\<^sub>c n = x")
      assume "\<exists> n. n \<in>\<^sub>c \<nat>\<^sub>c \<and> f \<circ>\<^sub>c n = x"
      then obtain n where n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c" and  x_def: "f \<circ>\<^sub>c n = x"
        by blast 
      have hfn_fsn: "h \<circ>\<^sub>c f \<circ>\<^sub>c n =f \<circ>\<^sub>c successor \<circ>\<^sub>c n"
        by (simp add: a_eq_fn n_type)
      
      show "x=y"
      proof(cases "\<exists> m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> f \<circ>\<^sub>c m = y")
        assume "\<exists> m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> f \<circ>\<^sub>c m = y"
        then obtain m where m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c" and  y_def: "f \<circ>\<^sub>c m = y"
          by blast
        have hfm_fsm: "h \<circ>\<^sub>c f \<circ>\<^sub>c m =f \<circ>\<^sub>c successor \<circ>\<^sub>c m"
          by (simp add: a_eq_fn m_type)
        have "f \<circ>\<^sub>c successor \<circ>\<^sub>c n = f \<circ>\<^sub>c successor \<circ>\<^sub>c m"
          using hfm_fsm hfn_fsn hx_eq_hy x_def y_def by auto
        then have "successor \<circ>\<^sub>c n = successor \<circ>\<^sub>c m"
          by (typecheck_cfuncs, metis f_inj f_type injective_imp_monomorphism mem_Collect_eq monomorphism_def3)
        then have "n = m"
          by (typecheck_cfuncs, simp add: succ_inject)
        then show "x = y"
          using \<open>n = m\<close> x_def y_def by blast
      next 
        assume "\<nexists>m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> f \<circ>\<^sub>c m = y"
        then obtain b where b_type[type_rule]: "b \<in>\<^sub>c A \<setminus> (\<nat>\<^sub>c,f)" and b_def: "h \<circ>\<^sub>c y =  f\<^sup>c  \<circ>\<^sub>c b"
          by (metis a_neq_fn y_type2)
        then have contradiction: "f \<circ>\<^sub>c successor \<circ>\<^sub>c n =  f\<^sup>c  \<circ>\<^sub>c b"
          by (metis b_def hfn_fsn hx_eq_hy x_def)
        have "f \<circ>\<^sub>c successor \<circ>\<^sub>c n \<noteq>  f\<^sup>c  \<circ>\<^sub>c b"
          by (typecheck_cfuncs, meson complement_disjoint f_inj injective_imp_monomorphism singletonI)
        then have False
          by (simp add: contradiction)
        then show "x = y"
          by simp
      qed
    next
      assume "\<nexists>n. n \<in>\<^sub>c \<nat>\<^sub>c \<and> f \<circ>\<^sub>c n = x"
      then obtain c where c_type[type_rule]:  "c \<in>\<^sub>c A \<setminus> (\<nat>\<^sub>c,f)" and c_def: "h \<circ>\<^sub>c x =  f\<^sup>c  \<circ>\<^sub>c c" and 
                                   try_x: "try_cast f \<circ>\<^sub>c x = right_coproj \<nat>\<^sub>c (A \<setminus> (\<nat>\<^sub>c,f)) \<circ>\<^sub>c c"
        using a_neq_fn x_type2 by blast      
      show "x = y"
      proof(cases "\<exists> m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> f \<circ>\<^sub>c m = y")
        assume "\<exists>m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> f \<circ>\<^sub>c m = y"
        then obtain m where m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c" and  y_def: "f \<circ>\<^sub>c m = y"
          by blast
        have hfm_fsm: "h \<circ>\<^sub>c f \<circ>\<^sub>c m =f \<circ>\<^sub>c successor \<circ>\<^sub>c m"
          by (simp add: a_eq_fn m_type)
        then have contradiction: "f \<circ>\<^sub>c successor \<circ>\<^sub>c m =  f\<^sup>c  \<circ>\<^sub>c c"
          using c_def hx_eq_hy y_def by force
        have "f \<circ>\<^sub>c successor \<circ>\<^sub>c m \<noteq>  f\<^sup>c  \<circ>\<^sub>c c"
          by (typecheck_cfuncs, meson complement_disjoint f_inj injective_imp_monomorphism singletonI)
        then have False
          by (simp add: contradiction)
        then show "x = y"
          by simp
      next
        assume "\<nexists>m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> f \<circ>\<^sub>c m = y"
        then obtain b where b_type[type_rule]: "b \<in>\<^sub>c A \<setminus> (\<nat>\<^sub>c,f)" and b_def: "h \<circ>\<^sub>c y =  f\<^sup>c  \<circ>\<^sub>c b" and
                                    try_y: "try_cast f \<circ>\<^sub>c y = right_coproj \<nat>\<^sub>c (A \<setminus> (\<nat>\<^sub>c,f)) \<circ>\<^sub>c b"
          by (metis a_neq_fn y_type2)
        then have "f\<^sup>c  \<circ>\<^sub>c b = f\<^sup>c  \<circ>\<^sub>c c"
          using c_def hx_eq_hy by presburger
        then have "b = c"
          by (typecheck_cfuncs, metis b_def c_def cfunc_type_def complement_morphism_mono 
              complement_morphism_type f_inj f_type hx_eq_hy injective_imp_monomorphism monomorphism_def singletonI)     
        then have "into_super f \<circ>\<^sub>c try_cast f \<circ>\<^sub>c y = into_super f \<circ>\<^sub>c try_cast f \<circ>\<^sub>c x"
           using  try_x try_y by force
         then show "x = y"
           by (typecheck_cfuncs, metis \<open>b = c\<close> cfunc_type_def comp_associative f_inj f_type 
               id_left_unit2 injective_imp_monomorphism into_super_type mem_Collect_eq try_cast_def2 try_x try_y x_type2)
      qed
    qed
  qed









  have "\<not>(surjective h)"
  proof(rule ccontr, auto)
    assume h_surj: "surjective h"
    then obtain a where a_type[type_rule]: "a \<in>\<^sub>c A" and a_def: "h  \<circ>\<^sub>c a =  f  \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, meson surjective_def2)
    show False
    proof(cases "\<exists> n. n \<in>\<^sub>c \<nat>\<^sub>c \<and> f \<circ>\<^sub>c n = a")  
      assume "\<exists>n. n \<in>\<^sub>c \<nat>\<^sub>c \<and> f \<circ>\<^sub>c n = a"
      then obtain n where n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c" and n_def: "f \<circ>\<^sub>c n = a"
        by blast 
      have "f  \<circ>\<^sub>c zero = f \<circ>\<^sub>c successor \<circ>\<^sub>c n"
        by (typecheck_cfuncs, metis a_def a_eq_fn n_def)
      then have "zero = successor \<circ>\<^sub>c n"
        by ( typecheck_cfuncs, metis f_inj f_type injective_imp_monomorphism mem_Collect_eq monomorphism_def3)
      then show False
        using n_type zero_is_not_successor by blast
    next
      assume "\<nexists>n. n \<in>\<^sub>c \<nat>\<^sub>c \<and> f \<circ>\<^sub>c n = a"
      then obtain c where c_type[type_rule]:  "c \<in>\<^sub>c A \<setminus> (\<nat>\<^sub>c,f)" and c_def: "h \<circ>\<^sub>c a =  f\<^sup>c  \<circ>\<^sub>c c"
        by (typecheck_cfuncs, metis a_neq_fn)
      then have "f  \<circ>\<^sub>c zero =  f\<^sup>c  \<circ>\<^sub>c c"
        using a_def by fastforce
      then show False
        using c_type complement_disjoint f_inj f_type injective_imp_monomorphism zero_type by blast 
    qed
  qed



  then show False
    using A_finite \<open>injective h\<close> epi_is_surj h_type injective_imp_monomorphism is_finite_def iso_imp_epi_and_monic by blast
next
  assume "\<forall>f. f : \<nat>\<^sub>c \<rightarrow> A \<longrightarrow> \<not> injective f"
  show "is_finite A"
  proof(rule ccontr)
    assume not_finite: "\<not> is_finite A"
    then obtain g where g_type[type_rule]: "g: A \<rightarrow> A" and g_not_surj: "\<not> surjective g" and g_injective: "injective g"
      using either_finite_or_infinite is_infinite_def monomorphism_imp_injective by blast
    
    obtain x where x_type[type_rule]: "x \<in>\<^sub>c A" and not_under_g: "\<nexists> a. a \<in>\<^sub>c A \<and> g \<circ>\<^sub>c a = x"
      using g_not_surj surjective_def2 by (typecheck_cfuncs, auto)

    obtain f where f_type[type_rule]: "f: \<nat>\<^sub>c \<rightarrow> A" and f_zero: "f \<circ>\<^sub>c zero = x" and f_succ: "f \<circ>\<^sub>c successor = g \<circ>\<^sub>c f"
      by (typecheck_cfuncs, metis natural_number_object_property2)


    have main_fact_aux: "eq_pred A \<circ>\<^sub>c \<langle>f , eval_func A A \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER A \<circ>\<^sub>c \<langle>(metafunc g) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id \<nat>\<^sub>c\<rangle>\<rangle>\<rangle> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
    proof(rule natural_number_object_func_unique[where X = \<Omega>, where f=  "id \<Omega>"])
      show "eq_pred A \<circ>\<^sub>c \<langle>f ,eval_func A A \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER A \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
        by typecheck_cfuncs
      show "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
        by typecheck_cfuncs
      show "id\<^sub>c \<Omega> : \<Omega> \<rightarrow> \<Omega>"
        by typecheck_cfuncs
      show "(eq_pred A \<circ>\<^sub>c \<langle>f,eval_func A A \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER A \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>) \<circ>\<^sub>c zero = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero"
        by (typecheck_cfuncs,smt (z3) ITER_zero' \<open>f \<circ>\<^sub>c zero = x\<close> cart_prod_extract_right cfunc_prod_comp char_of_singleton1 comp_associative2 eval_lemma id_left_unit2 id_right_unit2 id_type terminal_func_comp_elem)      
      show "(eq_pred A \<circ>\<^sub>c \<langle>f,eval_func A A \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER A \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>) \<circ>\<^sub>c successor =
    id\<^sub>c \<Omega> \<circ>\<^sub>c eq_pred A \<circ>\<^sub>c \<langle>f,eval_func A A \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER A \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>"
      proof(rule one_separator[where X = "\<nat>\<^sub>c", where Y = \<Omega>])
        show "(eq_pred A \<circ>\<^sub>c \<langle>f,eval_func A A \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER A \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>) \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<Omega>"
          by typecheck_cfuncs
        show "id\<^sub>c \<Omega> \<circ>\<^sub>c eq_pred A \<circ>\<^sub>c \<langle>f,eval_func A A \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER A \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
          by typecheck_cfuncs
      next
        fix n 
        assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
          

        have "((eq_pred A \<circ>\<^sub>c \<langle>f,eval_func A A \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER A \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>) \<circ>\<^sub>c successor) \<circ>\<^sub>c n =
                eq_pred A \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c (successor \<circ>\<^sub>c n),eval_func A A \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<circ>\<^sub>c (successor \<circ>\<^sub>c n),ITER A \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<circ>\<^sub>c (successor \<circ>\<^sub>c n),id\<^sub>c \<nat>\<^sub>c\<circ>\<^sub>c (successor \<circ>\<^sub>c n)\<rangle>\<rangle>\<rangle>"
          by (typecheck_cfuncs,smt (z3) cfunc_prod_comp comp_associative2)
        also have "... = eq_pred A \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c (successor \<circ>\<^sub>c n),eval_func A A \<circ>\<^sub>c \<langle>x, ITER A \<circ>\<^sub>c \<langle>metafunc g,  successor \<circ>\<^sub>c n\<rangle>\<rangle>\<rangle>"
          by (typecheck_cfuncs, metis id_left_unit2 id_right_unit2 id_type terminal_func_unique)
        also have "... = eq_pred A \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c (successor \<circ>\<^sub>c n),(g\<^bsup>\<circ>successor \<circ>\<^sub>c n\<^esup>) \<circ>\<^sub>c x\<rangle>"
          using eval_lemma_for_ITER by (typecheck_cfuncs, force)
        also have "... = eq_pred A \<circ>\<^sub>c \<langle>g \<circ>\<^sub>c f \<circ>\<^sub>c n, g \<circ>\<^sub>c(g\<^bsup>\<circ>n\<^esup>) \<circ>\<^sub>c x\<rangle>"
          using comp_associative2 f_succ succ_iters by (typecheck_cfuncs, force)
        also have "... = eq_pred A \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c n,(g\<^bsup>\<circ>n\<^esup>) \<circ>\<^sub>c x\<rangle>"
          by (typecheck_cfuncs, metis eq_pred_iff_eq eq_pred_iff_eq_conv g_injective injective_imp_monomorphism monomorphism_def3 singletonI)
        also have "... =eq_pred A \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c n, eval_func A A \<circ>\<^sub>c \<langle>x, ITER A \<circ>\<^sub>c \<langle>metafunc g, n\<rangle>\<rangle>\<rangle>"
          by (typecheck_cfuncs, simp add: eval_lemma_for_ITER)
        also have "... = eq_pred A \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c n, eval_func A A \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<circ>\<^sub>c n,ITER A \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c n,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>\<rangle>\<rangle>"
          by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2 terminal_func_comp_elem)
        also have "... = (id\<^sub>c \<Omega> \<circ>\<^sub>c eq_pred A \<circ>\<^sub>c \<langle>f,eval_func A A \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER A \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>) \<circ>\<^sub>c n"
          by (typecheck_cfuncs,smt (z3) cfunc_prod_comp comp_associative2 id_left_unit2)
        then show "((eq_pred A \<circ>\<^sub>c \<langle>f,eval_func A A \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER A \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>) \<circ>\<^sub>c successor) \<circ>\<^sub>c n =
          (id\<^sub>c \<Omega> \<circ>\<^sub>c eq_pred A \<circ>\<^sub>c \<langle>f,eval_func A A \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER A \<circ>\<^sub>c \<langle>metafunc g \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>) \<circ>\<^sub>c n"
          by (simp add: calculation)
      qed
      show "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor = id\<^sub>c \<Omega> \<circ>\<^sub>c \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
        by (typecheck_cfuncs, smt (z3) comp_associative2 id_left_unit2 terminal_func_comp)
    qed
    have f_is_g_itered: "\<And> n. n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> f \<circ>\<^sub>c n = (g\<^bsup>\<circ>n\<^esup>)\<circ>\<^sub>c x"
    proof -
      fix n 
      assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
      have "\<t> = eq_pred A \<circ>\<^sub>c \<langle>f , eval_func A A \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,ITER A \<circ>\<^sub>c \<langle>(metafunc g) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id \<nat>\<^sub>c\<rangle>\<rangle>\<rangle> \<circ>\<^sub>c n"
        by (typecheck_cfuncs, smt (z3) main_fact_aux comp_associative2 id_right_unit2 terminal_func_comp_elem)
      also have "... = eq_pred A \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c n, eval_func A A \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c n, ITER A \<circ>\<^sub>c \<langle>(metafunc g) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c n,id \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>\<rangle>\<rangle> "
        by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2)
      also have "... = eq_pred A \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c n, eval_func A A \<circ>\<^sub>c \<langle>x, ITER A \<circ>\<^sub>c \<langle>(metafunc g), n\<rangle>\<rangle>\<rangle>"
        by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2 terminal_func_comp_elem)
      also have "... = eq_pred A \<circ>\<^sub>c \<langle>f \<circ>\<^sub>c n, (g\<^bsup>\<circ>n\<^esup>) \<circ>\<^sub>c x\<rangle>"
        using eval_lemma_for_ITER by (typecheck_cfuncs, presburger)
      then show "f \<circ>\<^sub>c n = (g\<^bsup>\<circ>n\<^esup>)\<circ>\<^sub>c x"
        by (typecheck_cfuncs, simp add: calculation eq_pred_iff_eq)
    qed

    have "injective f"
    proof(rule ccontr)
      assume "\<not> injective f"
      then obtain n k where n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c" and k_type[type_rule]: "k  \<in>\<^sub>c \<nat>\<^sub>c" and distinct: "n \<noteq> k" and eq_im: "f \<circ>\<^sub>c n = f \<circ>\<^sub>c k"
        using cfunc_type_def f_type injective_def by auto

      then have gnx_eq_gkx: "(g\<^bsup>\<circ>n\<^esup>)\<circ>\<^sub>c x = (g\<^bsup>\<circ>k\<^esup>)\<circ>\<^sub>c x"
        using eq_im f_is_g_itered by auto
      
      have "n = k"
      proof(cases "n \<le>\<^sub>\<nat> k")
        assume n_leq_k: "n \<le>\<^sub>\<nat> k"
        then obtain m where m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c" and m_def: "n +\<^sub>\<nat> m = k"
          by (metis add_commutes k_type leq_infix_def leq_true_implies_exists n_type)
       then have "(g\<^bsup>\<circ>n\<^esup>)\<circ>\<^sub>c x = (g\<^bsup>\<circ>n\<^esup>)\<circ>\<^sub>c (g\<^bsup>\<circ>m\<^esup>)\<circ>\<^sub>c x"
         using add_iters comp_associative2 gnx_eq_gkx m_def by (typecheck_cfuncs, force)
       then have "x = (g\<^bsup>\<circ>m\<^esup>)\<circ>\<^sub>c x"
         using  g_injective iterative_injective_peeling n_type by (typecheck_cfuncs, blast)
       show "n = k"
       proof(cases "m = zero")
        show "m = zero \<Longrightarrow> n = k"
            using add_respects_zero_on_right m_def n_type by force
        next
          assume "m \<noteq> zero"
          then obtain j where j_type[type_rule]: "j \<in>\<^sub>c \<nat>\<^sub>c" and m_def: "successor \<circ>\<^sub>c j = m"
            using m_type nonzero_is_succ by auto
          then have "x = g \<circ>\<^sub>c (g\<^bsup>\<circ>j\<^esup>)\<circ>\<^sub>c x"
            using \<open>x = (g\<^bsup>\<circ>m\<^esup>) \<circ>\<^sub>c x\<close> comp_associative2 m_def succ_iters by (typecheck_cfuncs, force)
          then have False
            by (metis comp_type f_is_g_itered f_type j_type not_under_g)
          then show "n = k"
            by simp
        qed
      next
        assume "\<not> n \<le>\<^sub>\<nat> k"
        then obtain m where m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c" and m_def: "k +\<^sub>\<nat> m = n"
          by (typecheck_cfuncs, metis \<open>\<not> n \<le>\<^sub>\<nat> k\<close> add_commutes leq_infix_def leq_true_implies_exists lqe_connexity)
         then have "(g\<^bsup>\<circ>k\<^esup>)\<circ>\<^sub>c x = (g\<^bsup>\<circ>k\<^esup>)\<circ>\<^sub>c (g\<^bsup>\<circ>m\<^esup>)\<circ>\<^sub>c x"
           using add_iters comp_associative2 gnx_eq_gkx m_def by (typecheck_cfuncs, force)
         then have "x = (g\<^bsup>\<circ>m\<^esup>)\<circ>\<^sub>c x"
           using  g_injective iterative_injective_peeling k_type by (typecheck_cfuncs, blast)
         obtain j where j_type[type_rule]: "j \<in>\<^sub>c \<nat>\<^sub>c" and m_def: "successor \<circ>\<^sub>c j = m"
           by (typecheck_cfuncs, metis add_commutes add_respects_zero_on_left distinct k_type m_def nonzero_is_succ)
         then have "x = g \<circ>\<^sub>c (g\<^bsup>\<circ>j\<^esup>)\<circ>\<^sub>c x"
           using \<open>x = (g\<^bsup>\<circ>m\<^esup>) \<circ>\<^sub>c x\<close> comp_associative2 m_def succ_iters by (typecheck_cfuncs, force)
         then have False
           by (metis comp_type f_is_g_itered f_type j_type not_under_g)
         then show "n = k"
           by simp
       qed
       then show False
         using distinct by auto
     qed
     then show False
       using \<open>\<forall>f. f : \<nat>\<^sub>c \<rightarrow> A \<longrightarrow> \<not> injective f\<close> f_type by blast
   qed
qed

theorem Herrlichs_finiteness_criterion': 
  "is_infinite A = (\<exists> f. f: \<nat>\<^sub>c \<rightarrow> A \<and> injective f)"
  by (metis Herrlichs_finiteness_criterion either_finite_or_infinite epi_is_surj is_finite_def is_infinite_def iso_imp_epi_and_monic)
  


(*Do we want to explicitly use N?*)
lemma infinite_set_contain_countable_subset:
  assumes Infinite_X: "is_infinite X"
  shows "\<exists> C. (countable C \<and> is_infinite C \<and> C \<le>\<^sub>c X)"
  by (metis CollectI Herrlichs_finiteness_criterion' assms injective_imp_monomorphism is_smaller_than_def natural_numbers_are_countably_infinite)








lemma Infinite_Set_Coprod_One:
  "(is_finite X) = (\<not>(X \<cong> X \<Coprod> one))"
proof(auto)
  assume fin_X: "is_finite X"
  assume sets_iso: " X \<cong> X \<Coprod> one"
  then obtain \<phi> where \<phi>_type[type_rule]: "\<phi> : X \<Coprod> one \<rightarrow> X" and \<phi>_iso: "isomorphism \<phi>"
    by (meson is_isomorphic_def isomorphic_is_symmetric fin_X)
  then obtain \<phi>_inv where \<phi>_inv[type_rule]: "\<phi>_inv : X \<rightarrow> X \<Coprod> one" 
                      and \<phi>_inv_def: "\<phi>_inv \<circ>\<^sub>c \<phi> = id (X \<Coprod> one) \<and> \<phi> \<circ>\<^sub>c \<phi>_inv = id X" 
                      and \<phi>_inv_iso: "isomorphism \<phi>_inv"
    by (metis \<phi>_iso cfunc_type_def isomorphism_def)
  have coproj_mono_not_epi:"\<not>epimorphism (left_coproj X one) \<and> monomorphism (left_coproj X one)"
    by (metis cfunc_type_def coproducts_disjoint epi_is_surj id_right_unit id_type left_coproj_are_monomorphisms left_proj_type right_proj_type surjective_def2)
  then have "isomorphism(\<phi> \<circ>\<^sub>c left_coproj X one)"
    by (typecheck_cfuncs, metis \<phi>_iso fin_X cfunc_type_def composition_of_monic_pair_is_monic coproj_mono_not_epi is_finite_def iso_imp_epi_and_monic)
  then have "isomorphism(\<phi>_inv \<circ>\<^sub>c \<phi> \<circ>\<^sub>c left_coproj X one)"
    using \<phi>_inv_iso isomorphism_comp' by (typecheck_cfuncs, blast)
  then have "epimorphism (left_coproj X one)"
    by (smt (z3) \<phi>_inv \<phi>_inv_def \<phi>_type comp_associative2 id_left_unit2 iso_imp_epi_and_monic left_proj_type)
  then show False
    using coproj_mono_not_epi by auto
next
  assume "\<not> X \<cong> X \<Coprod> one"
  have "(\<not>(is_finite X)) \<longrightarrow> X \<cong> X \<Coprod> one"
    sorry
  then show "is_finite X "
    by (simp add: \<open>\<not> X \<cong> X \<Coprod> one\<close>)
    
qed

  










lemma canonically_finite_sets_are_finite:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "is_finite [n]\<^sub>c"
  sorry






thm nat_induction

(*
  (0) [sn] is not isomorphic to [n] (via facts about \ and order preserving maps).
  (1) Summation facts. 
  (2) [n^m]\<cong>[n]^[m]
  (3) If X is infinite then X \<cong> X U 1
  (4) Iso to a Canonically finite set is finite.
   Corollary: Canonically finite sets are finite. Proof:
    Assume X \<cong> [n] for some n then \<not>(X\<cong> X U 1) (for it X \<cong> X U 1 then [n] \<cong> [sn] a contradiction) so X is finite by (3) above.
  (5) Theorem: Finite sets are isomorphic to [n] for some n .   (proof uses AC).
  Corollary: Finite sets are countable. 
  Corollary: finite sets are closed under coprods, prods, and exps
*)




lemma smaller_than_countable_is_countable:
  assumes "X \<le>\<^sub>c Y" "countable Y"
  shows "countable X"
  by (smt assms cfunc_type_def comp_type composition_of_monic_pair_is_monic countable_def is_smaller_than_def)


lemma iso_pres_finite:
  assumes "X \<cong> Y"
  assumes "is_finite(X)"
  shows "is_finite(Y)"
  using assms is_isomorphic_def is_smaller_than_def iso_imp_epi_and_monic isomorphic_is_symmetric smaller_than_finite_is_finite by blast


lemma iso_pres_countable:
  assumes "X \<cong> Y" "countable Y"
  shows "countable X"
  using assms(1) assms(2) is_isomorphic_def is_smaller_than_def iso_imp_epi_and_monic smaller_than_countable_is_countable by blast


lemma not_finite_and_infinite:
  "\<not>(is_finite(X) \<and> is_infinite(X))"
  using epi_is_surj is_finite_def is_infinite_def iso_imp_epi_and_monic by blast

lemma iso_pres_infinite:
  assumes "X \<cong> Y"
  assumes "is_infinite(X)"
  shows "is_infinite(Y)"
  using assms either_finite_or_infinite not_finite_and_infinite iso_pres_finite isomorphic_is_symmetric by blast




(*Consider moving the result below*)

lemma coprod_leq_product:
  assumes X_not_init: "\<not>(initial_object(X))" 
  assumes Y_not_init: "\<not>(initial_object(Y))" 
  assumes X_not_term: "\<not>(terminal_object(X))"
  assumes Y_not_term: "\<not>(terminal_object(Y))"
  shows "(X \<Coprod> Y) \<le>\<^sub>c (X \<times>\<^sub>c Y)"
proof - 
  obtain x1 x2 where x1x2_def[type_rule]:  "(x1 \<in>\<^sub>c X)" "(x2 \<in>\<^sub>c X)" "(x1 \<noteq> x2)"
    using is_empty_def X_not_init X_not_term iso_empty_initial iso_to1_is_term no_el_iff_iso_0 single_elem_iso_one by blast
  obtain y1 y2 where y1y2_def[type_rule]:  "(y1 \<in>\<^sub>c Y)" "(y2 \<in>\<^sub>c Y)" "(y1 \<noteq> y2)"
    using is_empty_def Y_not_init Y_not_term iso_empty_initial iso_to1_is_term no_el_iff_iso_0 single_elem_iso_one by blast
  then have y1_mono[type_rule]: "monomorphism(y1)"
    using element_monomorphism by blast
  obtain m where m_def: "m = \<langle>id(X), y1 \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<amalg> ((\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (one,y1)\<^esub>, y1\<^sup>c\<rangle>) \<circ>\<^sub>c  try_cast y1)"
    by simp
  have type1: "\<langle>id(X), y1 \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> : X \<rightarrow> (X \<times>\<^sub>c Y)"
    by (meson cfunc_prod_type comp_type id_type terminal_func_type y1y2_def)
  have trycast_y1_type: "try_cast y1 : Y \<rightarrow> one \<Coprod> (Y \<setminus> (one,y1))"
    by (meson element_monomorphism try_cast_type y1y2_def)
  have y1'_type[type_rule]: "y1\<^sup>c : Y \<setminus> (one,y1) \<rightarrow> Y"
    using complement_morphism_type one_terminal_object terminal_el__monomorphism y1y2_def by blast
  have type4: "\<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (one,y1)\<^esub>, y1\<^sup>c\<rangle> : Y \<setminus> (one,y1) \<rightarrow> (X \<times>\<^sub>c Y)"
    using cfunc_prod_type comp_type terminal_func_type x1x2_def y1'_type by blast
  have type5: "\<langle>x2, y2\<rangle> \<in>\<^sub>c (X \<times>\<^sub>c Y)"
    by (simp add: cfunc_prod_type x1x2_def y1y2_def)
  then have type6: "\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (one,y1)\<^esub>, y1\<^sup>c\<rangle> :(one \<Coprod> (Y \<setminus> (one,y1))) \<rightarrow> (X \<times>\<^sub>c Y)"
    using cfunc_coprod_type type4 by blast
  then have type7: "((\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (one,y1)\<^esub>, y1\<^sup>c\<rangle>) \<circ>\<^sub>c  try_cast y1) : Y \<rightarrow> (X \<times>\<^sub>c Y)"
    using comp_type trycast_y1_type by blast
  then have m_type: "m : X  \<Coprod> Y \<rightarrow> (X \<times>\<^sub>c Y)"
    by (simp add: cfunc_coprod_type m_def type1)

  have relative: "\<And>y. y \<in>\<^sub>c Y \<Longrightarrow> (y \<in>\<^bsub>Y\<^esub> (one, y1)) = (y = y1)"
  proof(auto)
    fix y 
    assume y_type: "y \<in>\<^sub>c Y"
    show "y \<in>\<^bsub>Y\<^esub> (one, y1) \<Longrightarrow> y = y1"
      by (metis cfunc_type_def factors_through_def id_right_unit2 id_type one_unique_element relative_member_def2)
  next 
    show "y1 \<in>\<^sub>c Y \<Longrightarrow> y1 \<in>\<^bsub>Y\<^esub> (one, y1)"
      by (metis cfunc_type_def factors_through_def id_right_unit2 id_type relative_member_def2 y1_mono)
  qed


  have "injective(m)"
  proof(unfold injective_def ,auto)
    fix a b 
    assume "a \<in>\<^sub>c domain m" "b \<in>\<^sub>c domain m"
    then have a_type[type_rule]: "a \<in>\<^sub>c X  \<Coprod> Y" and b_type[type_rule]: "b \<in>\<^sub>c X  \<Coprod> Y"
      using m_type unfolding cfunc_type_def by auto
    assume eqs: "m \<circ>\<^sub>c a = m \<circ>\<^sub>c b"

      have m_leftproj_l_equals: "\<And> l. l  \<in>\<^sub>c X \<Longrightarrow> m \<circ>\<^sub>c left_coproj X Y \<circ>\<^sub>c l = \<langle>l, y1\<rangle>"
      proof-
        fix l 
        assume l_type: "l \<in>\<^sub>c X"
        have "m \<circ>\<^sub>c left_coproj X Y \<circ>\<^sub>c l = (\<langle>id(X), y1 \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<amalg> ((\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (one,y1)\<^esub>, y1\<^sup>c\<rangle>) \<circ>\<^sub>c  try_cast y1)) \<circ>\<^sub>c left_coproj X Y \<circ>\<^sub>c l"
          by (simp add: m_def)
        also have "... = (\<langle>id(X), y1 \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<amalg> ((\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (one,y1)\<^esub>, y1\<^sup>c\<rangle>) \<circ>\<^sub>c  try_cast y1) \<circ>\<^sub>c left_coproj X Y) \<circ>\<^sub>c l"
          using comp_associative2 l_type by (typecheck_cfuncs, blast)
        also have "... = \<langle>id(X), y1 \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c l"
          by (typecheck_cfuncs, simp add: left_coproj_cfunc_coprod)
        also have "... = \<langle>id(X)\<circ>\<^sub>c l , (y1 \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c l\<rangle>"
          using l_type cfunc_prod_comp by (typecheck_cfuncs, auto)
        also have "... = \<langle>l , y1 \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c l\<rangle>"
          using l_type comp_associative2 id_left_unit2 by (typecheck_cfuncs, auto)
        also have "... = \<langle>l , y1\<rangle>"
          using l_type by (typecheck_cfuncs,metis id_right_unit2 id_type one_unique_element)
        then show "m \<circ>\<^sub>c left_coproj X Y \<circ>\<^sub>c l = \<langle>l,y1\<rangle>"
          by (simp add: calculation)
      qed

      have m_rightproj_y1_equals: "m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c y1 = \<langle>x2, y2\<rangle>"
          proof - 
            have "m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c y1 = (m \<circ>\<^sub>c right_coproj X Y) \<circ>\<^sub>c y1"
              using  comp_associative2 m_type by (typecheck_cfuncs, auto)
            also have "... = ((\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (one,y1)\<^esub>, y1\<^sup>c\<rangle>) \<circ>\<^sub>c  try_cast y1) \<circ>\<^sub>c y1"
              using m_def right_coproj_cfunc_coprod type1 by (typecheck_cfuncs, auto)
            also have "... = (\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (one,y1)\<^esub>, y1\<^sup>c\<rangle>) \<circ>\<^sub>c  try_cast y1 \<circ>\<^sub>c y1"
              using  comp_associative2 by (typecheck_cfuncs, auto)
            also have "... = (\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (one,y1)\<^esub>, y1\<^sup>c\<rangle>) \<circ>\<^sub>c left_coproj one (Y \<setminus> (one,y1))"
              using  try_cast_m_m y1_mono y1y2_def(1) by auto
            also have "... =  \<langle>x2, y2\<rangle>"
              using left_coproj_cfunc_coprod type4 type5 by blast
            then show ?thesis using calculation by auto
          qed

     have m_rightproj_not_y1_equals: "\<And> r. r  \<in>\<^sub>c Y \<and> r \<noteq> y1 \<Longrightarrow>
          \<exists>k. k \<in>\<^sub>c Y \<setminus> (one,y1) \<and> try_cast y1 \<circ>\<^sub>c r = right_coproj one (Y \<setminus> (one,y1)) \<circ>\<^sub>c k \<and> 
          m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c r = \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
          proof(auto)
           fix r 
           assume r_type: "r \<in>\<^sub>c Y"
           assume r_not_y1: "r \<noteq> y1"
           then obtain k where k_def: "k \<in>\<^sub>c Y \<setminus> (one,y1) \<and> try_cast y1 \<circ>\<^sub>c r = right_coproj one (Y \<setminus> (one,y1)) \<circ>\<^sub>c k"
            using r_type relative try_cast_not_in_X y1_mono y1y2_def(1) by blast
           have m_rightproj_l_equals: "m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c r = \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
           
           proof -
             have "m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c r = (m \<circ>\<^sub>c right_coproj X Y) \<circ>\<^sub>c r"
              using r_type comp_associative2 m_type by (typecheck_cfuncs, auto)
            also have "... = ((\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (one,y1)\<^esub>, y1\<^sup>c\<rangle>) \<circ>\<^sub>c  try_cast y1) \<circ>\<^sub>c r"
              using m_def right_coproj_cfunc_coprod type1 by (typecheck_cfuncs, auto)
            also have "... = (\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (one,y1)\<^esub>, y1\<^sup>c\<rangle>) \<circ>\<^sub>c  (try_cast y1 \<circ>\<^sub>c r)"
              using r_type comp_associative2 by (typecheck_cfuncs, auto)
            also have "... = (\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (one,y1)\<^esub>, y1\<^sup>c\<rangle>) \<circ>\<^sub>c (right_coproj one (Y \<setminus> (one,y1)) \<circ>\<^sub>c k)"
              using k_def by auto
            also have "... = ((\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (one,y1)\<^esub>, y1\<^sup>c\<rangle>) \<circ>\<^sub>c right_coproj one (Y \<setminus> (one,y1))) \<circ>\<^sub>c k"
              using comp_associative2 k_def by (typecheck_cfuncs, blast)
            also have "... =  \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (one,y1)\<^esub>, y1\<^sup>c\<rangle> \<circ>\<^sub>c k"
              using right_coproj_cfunc_coprod type4 type5 by auto
            also have "... =  \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (one,y1)\<^esub> \<circ>\<^sub>c k, y1\<^sup>c \<circ>\<^sub>c k \<rangle>"
              using cfunc_prod_comp comp_associative2 k_def by (typecheck_cfuncs, auto)
            also have "... =  \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
              by (metis id_right_unit2 id_type k_def one_unique_element terminal_func_comp terminal_func_type x1x2_def(1))
            then show ?thesis using calculation by auto
          qed
          then show "\<exists>k. k \<in>\<^sub>c Y \<setminus> (one, y1) \<and>
             try_cast y1 \<circ>\<^sub>c r = right_coproj one (Y \<setminus> (one, y1)) \<circ>\<^sub>c k \<and>
             m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c r = \<langle>x1,y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
            using k_def by blast
        qed

  
    show "a = b"
    proof(cases "\<exists>x. a = left_coproj X Y \<circ>\<^sub>c x  \<and> x \<in>\<^sub>c X")
      assume "\<exists>x. a = left_coproj X Y \<circ>\<^sub>c x  \<and> x \<in>\<^sub>c X"
      then obtain x where x_def: "a = left_coproj X Y \<circ>\<^sub>c x  \<and> x \<in>\<^sub>c X"
        by auto
      then have m_proj_a: "m \<circ>\<^sub>c left_coproj X Y \<circ>\<^sub>c x = \<langle>x, y1\<rangle>"
        using m_leftproj_l_equals by (simp add: x_def)
      show "a = b"
      proof(cases "\<exists>c. b = left_coproj X Y \<circ>\<^sub>c c  \<and> c \<in>\<^sub>c X")
        assume "\<exists>c. b = left_coproj X Y \<circ>\<^sub>c c \<and> c \<in>\<^sub>c X"
        then obtain c where c_def: "b = left_coproj X Y \<circ>\<^sub>c c  \<and> c \<in>\<^sub>c X"
          by auto
        then have "m \<circ>\<^sub>c left_coproj X Y \<circ>\<^sub>c c = \<langle>c, y1\<rangle>"
          by (simp add: m_leftproj_l_equals)
        then show ?thesis
          using c_def element_pair_eq eqs m_proj_a x_def y1y2_def(1) by auto
      next
        assume "\<nexists>c. b = left_coproj X Y \<circ>\<^sub>c c \<and> c \<in>\<^sub>c X"
        then obtain c where c_def: "b = right_coproj X Y \<circ>\<^sub>c c  \<and> c \<in>\<^sub>c Y"
          using b_type coprojs_jointly_surj by blast
        show "a = b"
        proof(cases "c = y1")
          assume "c = y1"       
          have m_rightproj_l_equals: "m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c c = \<langle>x2, y2\<rangle>"
            by (simp add: \<open>c = y1\<close> m_rightproj_y1_equals)       
          then show ?thesis
            using \<open>c = y1\<close> c_def cart_prod_eq2 eqs m_proj_a x1x2_def(2) x_def y1y2_def(2) y1y2_def(3) by auto
        next
          assume "c \<noteq> y1"       
          then obtain k where k_def:  "m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c c = \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
            using c_def m_rightproj_not_y1_equals by blast                     
          then have "\<langle>x, y1\<rangle> = \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
            using c_def eqs m_proj_a x_def by auto
          then have "(x = x1) \<and> (y1 = y1\<^sup>c \<circ>\<^sub>c k)"
            by (smt \<open>c \<noteq> y1\<close> c_def cfunc_type_def comp_associative comp_type element_pair_eq k_def m_rightproj_not_y1_equals monomorphism_def3 try_cast_m_m' try_cast_mono trycast_y1_type x1x2_def(1) x_def y1'_type y1_mono y1y2_def(1))
          then have False
            by (smt \<open>c \<noteq> y1\<close>  c_def comp_type complement_disjoint element_pair_eq id_right_unit2 id_type k_def m_rightproj_not_y1_equals x_def y1'_type y1_mono y1y2_def(1))
          then show ?thesis by auto
        qed
      qed
    next 
      assume "\<nexists>x. a = left_coproj X Y \<circ>\<^sub>c x \<and> x \<in>\<^sub>c X"
      then obtain y where y_def: "a = right_coproj X Y \<circ>\<^sub>c y \<and> y \<in>\<^sub>c Y"
        using a_type coprojs_jointly_surj by blast

      show "a = b"
      proof(cases "y = y1")
        assume "y = y1"
        then  have m_rightproj_y_equals: "m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c y = \<langle>x2, y2\<rangle>"
          using m_rightproj_y1_equals by blast
        then have "m \<circ>\<^sub>c a  = \<langle>x2, y2\<rangle>"
          using y_def by blast
        show "a = b"
        proof(cases "\<exists>c. b = left_coproj X Y \<circ>\<^sub>c c  \<and> c \<in>\<^sub>c X")
          assume "\<exists>c. b = left_coproj X Y \<circ>\<^sub>c c \<and> c \<in>\<^sub>c X"
          then obtain c where c_def: "b = left_coproj X Y \<circ>\<^sub>c c \<and> c \<in>\<^sub>c X"
            by blast
          then show "a = b"
            using cart_prod_eq2 eqs m_leftproj_l_equals m_rightproj_y_equals x1x2_def(2) y1y2_def y_def by auto
        next
          assume "\<nexists>c. b = left_coproj X Y \<circ>\<^sub>c c \<and> c \<in>\<^sub>c X"
          then obtain c where c_def: "b = right_coproj X Y \<circ>\<^sub>c c \<and> c \<in>\<^sub>c Y"
            using b_type coprojs_jointly_surj by blast
          show "a = b"
          proof(cases "c = y")
            assume "c = y"
            show "a = b"
              by (simp add: \<open>c = y\<close> c_def y_def)
          next
            assume "c \<noteq> y"
            then have "c \<noteq> y1"
              by (simp add: \<open>y = y1\<close>)
            then obtain k where k_def: "k \<in>\<^sub>c Y \<setminus> (one,y1) \<and> try_cast y1 \<circ>\<^sub>c c = right_coproj one (Y \<setminus> (one,y1)) \<circ>\<^sub>c k \<and> 
          m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c c = \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
              using c_def m_rightproj_not_y1_equals by blast
            then have "\<langle>x2, y2\<rangle> = \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
              using \<open>m \<circ>\<^sub>c a = \<langle>x2,y2\<rangle>\<close> c_def eqs by auto
            then have False
              using comp_type element_pair_eq k_def x1x2_def y1'_type y1y2_def(2) by auto
            then show ?thesis
              by simp
          qed
        qed
      next
        assume "y \<noteq> y1"
        then obtain k where k_def: "k \<in>\<^sub>c Y \<setminus> (one,y1) \<and> try_cast y1 \<circ>\<^sub>c y = right_coproj one (Y \<setminus> (one,y1)) \<circ>\<^sub>c k \<and> 
          m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c y = \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
          using m_rightproj_not_y1_equals y_def by blast  
        then have "m \<circ>\<^sub>c a  = \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
          using y_def by blast
        show "a = b"
        proof(cases "\<exists>c. b = right_coproj X Y \<circ>\<^sub>c c  \<and> c \<in>\<^sub>c Y")
          assume "\<exists>c. b = right_coproj X Y \<circ>\<^sub>c c  \<and> c \<in>\<^sub>c Y"
          then obtain c where c_def: "b = right_coproj X Y \<circ>\<^sub>c c \<and> c \<in>\<^sub>c Y"
            by blast  
          show "a = b"
          proof(cases "c = y1")
            assume "c = y1" 
            show "a = b"
              proof -
                obtain cc :: cfunc where
                  f1: "cc \<in>\<^sub>c Y \<setminus> (one, y1) \<and> try_cast y1 \<circ>\<^sub>c y = right_coproj one (Y \<setminus> (one, y1)) \<circ>\<^sub>c cc \<and> m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c y = \<langle>x1,y1\<^sup>c \<circ>\<^sub>c cc\<rangle>"
                  using \<open>\<And>thesis. (\<And>k. k \<in>\<^sub>c Y \<setminus> (one, y1) \<and> try_cast y1 \<circ>\<^sub>c y = right_coproj one (Y \<setminus> (one, y1)) \<circ>\<^sub>c k \<and> m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c y = \<langle>x1,y1\<^sup>c \<circ>\<^sub>c k\<rangle> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> by blast
                have "\<langle>x2,y2\<rangle> = m \<circ>\<^sub>c a"
              using \<open>c = y1\<close> c_def eqs m_rightproj_y1_equals by presburger
              then show ?thesis
              using f1 cart_prod_eq2 comp_type x1x2_def y1'_type y1y2_def(2) y_def by force
              qed
          next
              assume "c \<noteq> y1"              
              then obtain k' where k'_def: "k' \<in>\<^sub>c Y \<setminus> (one,y1) \<and> try_cast y1 \<circ>\<^sub>c c = right_coproj one (Y \<setminus> (one,y1)) \<circ>\<^sub>c k' \<and> 
              m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c c = \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k'\<rangle>"
                using c_def m_rightproj_not_y1_equals by blast
              then have "\<langle>x1, y1\<^sup>c \<circ>\<^sub>c k'\<rangle> = \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
                using c_def eqs k_def y_def by auto
              then have "(x1 = x1) \<and> (y1\<^sup>c \<circ>\<^sub>c k' = y1\<^sup>c \<circ>\<^sub>c k)"
                using  element_pair_eq k'_def k_def by (typecheck_cfuncs, blast)
              then have "k' = k"
                by (metis cfunc_type_def complement_morphism_mono k'_def k_def monomorphism_def y1'_type y1_mono)
              then have "c = y"
                by (metis c_def cfunc_type_def k'_def k_def monomorphism_def try_cast_mono trycast_y1_type y1_mono y_def)
              then show "a = b"
                by (simp add: c_def y_def)
          qed
        next
            assume "\<nexists>c. b = right_coproj X Y \<circ>\<^sub>c c \<and> c \<in>\<^sub>c Y"
            then obtain c where c_def:  "b = left_coproj X Y \<circ>\<^sub>c c \<and> c \<in>\<^sub>c X"
              using b_type coprojs_jointly_surj by blast
            then have  "m \<circ>\<^sub>c left_coproj X Y \<circ>\<^sub>c c = \<langle>c, y1\<rangle>"
              by (simp add: m_leftproj_l_equals)      
            then have "\<langle>c, y1\<rangle> = \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
                using \<open>m \<circ>\<^sub>c a = \<langle>x1,y1\<^sup>c \<circ>\<^sub>c k\<rangle>\<close> \<open>m \<circ>\<^sub>c left_coproj X Y \<circ>\<^sub>c c = \<langle>c,y1\<rangle>\<close> c_def eqs by auto      
            then have "(c = x1) \<and> (y1 = y1\<^sup>c \<circ>\<^sub>c k)"
              using c_def cart_prod_eq2 comp_type k_def x1x2_def(1) y1'_type y1y2_def(1) by auto 
            then have False
              by (metis cfunc_type_def complement_disjoint id_right_unit id_type k_def y1_mono y1y2_def(1))
            then show ?thesis
              by simp
        qed
      qed
    qed
  qed
  then have "monomorphism m"
    using injective_imp_monomorphism by auto 
  then show ?thesis
    using is_smaller_than_def m_type by blast
qed


lemma sets_squared:
  "A\<^bsup>\<Omega>\<^esup> \<cong> A \<times>\<^sub>c A "
proof - 
  obtain \<phi> where \<phi>_def: "\<phi> = \<langle>eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>,
                              eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>\<rangle>"
    by simp
  have type1[type_rule]: "\<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> : A\<^bsup>\<Omega>\<^esup> \<rightarrow> \<Omega> \<times>\<^sub>c (A\<^bsup>\<Omega>\<^esup>)"
    by typecheck_cfuncs
  have type2[type_rule]: "\<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> : A\<^bsup>\<Omega>\<^esup> \<rightarrow> \<Omega> \<times>\<^sub>c (A\<^bsup>\<Omega>\<^esup>)"
    by typecheck_cfuncs
  have \<phi>_type[type_rule]: "\<phi> : A\<^bsup>\<Omega>\<^esup> \<rightarrow> A \<times>\<^sub>c A"
    unfolding \<phi>_def by typecheck_cfuncs
  have "injective(\<phi>)"
  proof(unfold injective_def,auto)
    fix f g 
    assume "f \<in>\<^sub>c domain \<phi>" then have f_type[type_rule]: "f \<in>\<^sub>c A\<^bsup>\<Omega>\<^esup>" 
      using \<phi>_type cfunc_type_def by (typecheck_cfuncs, auto)
    assume "g \<in>\<^sub>c domain \<phi>" then have g_type[type_rule]: "g \<in>\<^sub>c A\<^bsup>\<Omega>\<^esup>" 
      using \<phi>_type cfunc_type_def by (typecheck_cfuncs, auto)
    assume eqs: "\<phi> \<circ>\<^sub>c f = \<phi> \<circ>\<^sub>c g"
    show "f = g"
    proof(rule one_separator[where X = one, where Y = "A\<^bsup>\<Omega>\<^esup>"])
      show "f \<in>\<^sub>c A\<^bsup>\<Omega>\<^esup>" 
        by typecheck_cfuncs
      show "g \<in>\<^sub>c A\<^bsup>\<Omega>\<^esup>"
        by typecheck_cfuncs
      show "\<And>id_1. id_1 \<in>\<^sub>c one \<Longrightarrow> f \<circ>\<^sub>c id_1 = g \<circ>\<^sub>c id_1"
      proof(rule same_evals_equal[where Z = one, where X = A, where A = \<Omega>])
        show "\<And>id_1. id_1 \<in>\<^sub>c one \<Longrightarrow> f \<circ>\<^sub>c id_1 \<in>\<^sub>c A\<^bsup>\<Omega>\<^esup>"
          by (simp add: comp_type f_type)
        show "\<And>id_1. id_1 \<in>\<^sub>c one \<Longrightarrow> g \<circ>\<^sub>c id_1 \<in>\<^sub>c A\<^bsup>\<Omega>\<^esup>"
          by (simp add: comp_type g_type)
        show "\<And>id_1.
       id_1 \<in>\<^sub>c one \<Longrightarrow>
       eval_func A \<Omega> \<circ>\<^sub>c id\<^sub>c \<Omega> \<times>\<^sub>f f \<circ>\<^sub>c id_1 =
       eval_func A \<Omega> \<circ>\<^sub>c id\<^sub>c \<Omega> \<times>\<^sub>f g \<circ>\<^sub>c id_1"
        proof  -
          fix id_1
          assume id1_is: "id_1 \<in>\<^sub>c one"
          then have id1_eq: "id_1 = id(one)"
            using id_type one_unique_element by auto

          obtain a1 a2 where phi_f_def: "\<phi> \<circ>\<^sub>c f = \<langle>a1,a2\<rangle> \<and> a1 \<in>\<^sub>c A \<and> a2 \<in>\<^sub>c A"
            using \<phi>_type cart_prod_decomp comp_type f_type by blast
          have equation1: "\<langle>a1,a2\<rangle> =  \<langle>eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t>, f \<rangle>  ,
                              eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> , f \<rangle> \<rangle>"
          proof - 
              have "\<langle>a1,a2\<rangle> = \<langle>eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>,
                                  eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>\<rangle> \<circ>\<^sub>c f"
                using \<phi>_def phi_f_def by auto
              also have "... = \<langle>eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> \<circ>\<^sub>c f ,
                                  eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> \<circ>\<^sub>c f\<rangle>"
                by (typecheck_cfuncs,smt cfunc_prod_comp comp_associative2)
              also have "... = \<langle>eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c f, id(A\<^bsup>\<Omega>\<^esup>) \<circ>\<^sub>c f \<rangle>  ,
                                  eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c f, id(A\<^bsup>\<Omega>\<^esup>)\<circ>\<^sub>c f \<rangle> \<rangle>"
                by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
              also have "... = \<langle>eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t>, f \<rangle>  ,
                                  eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> , f \<rangle> \<rangle>"    
                by (typecheck_cfuncs, metis id1_eq id1_is id_left_unit2 id_right_unit2 terminal_func_unique)
              then show ?thesis using calculation by auto
          qed
          have equation2: "\<langle>a1,a2\<rangle> =  \<langle>eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t>, g \<rangle>  ,
                              eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> , g \<rangle> \<rangle>"
          proof - 
              have "\<langle>a1,a2\<rangle> = \<langle>eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>,
                                  eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>\<rangle> \<circ>\<^sub>c g"
                using \<phi>_def eqs phi_f_def by auto
                also have "... = \<langle>eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> \<circ>\<^sub>c g ,
                                  eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> \<circ>\<^sub>c g\<rangle>"
                by (typecheck_cfuncs,smt cfunc_prod_comp comp_associative2)
              also have "... = \<langle>eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c g, id(A\<^bsup>\<Omega>\<^esup>) \<circ>\<^sub>c g \<rangle>  ,
                                  eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c g, id(A\<^bsup>\<Omega>\<^esup>)\<circ>\<^sub>c g \<rangle> \<rangle>"
                by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
              also have "... = \<langle>eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t>, g \<rangle>  ,
                                  eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> , g \<rangle> \<rangle>"    
                by (typecheck_cfuncs, metis id1_eq id1_is id_left_unit2 id_right_unit2 terminal_func_unique)
              then show ?thesis using calculation by auto
         qed
            have "\<langle>eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t>, f \<rangle>  , eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> , f \<rangle> \<rangle> = 
                             \<langle>eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t>, g \<rangle>  , eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> , g \<rangle> \<rangle>"
              using equation1 equation2 by auto
            then have equation3: "(eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t>, f \<rangle> = eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t>, g\<rangle>) \<and> 
                                  (eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f>, f \<rangle> = eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f>, g\<rangle>)"
              using  cart_prod_eq2 by (typecheck_cfuncs, auto)
            have "eval_func A \<Omega> \<circ>\<^sub>c id\<^sub>c \<Omega> \<times>\<^sub>f f  = eval_func A \<Omega> \<circ>\<^sub>c id\<^sub>c \<Omega> \<times>\<^sub>f g"
            proof(rule one_separator[where X = "\<Omega> \<times>\<^sub>c one", where Y = A])
              show "eval_func A \<Omega> \<circ>\<^sub>c id\<^sub>c \<Omega> \<times>\<^sub>f f : \<Omega> \<times>\<^sub>c one \<rightarrow> A"
                by typecheck_cfuncs
              show "eval_func A \<Omega> \<circ>\<^sub>c id\<^sub>c \<Omega> \<times>\<^sub>f g : \<Omega> \<times>\<^sub>c one \<rightarrow> A"
                by typecheck_cfuncs
              show "\<And>x. x \<in>\<^sub>c \<Omega> \<times>\<^sub>c one \<Longrightarrow>
         (eval_func A \<Omega> \<circ>\<^sub>c id\<^sub>c \<Omega> \<times>\<^sub>f f) \<circ>\<^sub>c x = (eval_func A \<Omega> \<circ>\<^sub>c id\<^sub>c \<Omega> \<times>\<^sub>f g) \<circ>\<^sub>c x"
              proof - 
                fix x
                assume x_type[type_rule]: "x \<in>\<^sub>c \<Omega> \<times>\<^sub>c one"
                then obtain w i where  x_def: "(w \<in>\<^sub>c \<Omega>) \<and> (i \<in>\<^sub>c one) \<and> (x = \<langle>w,i\<rangle>)"
                  using cart_prod_decomp by blast
                then have i_def: "i = id(one)"
                  using id1_eq id1_is one_unique_element by auto
                have w_def: "(w = \<f>) \<or> (w = \<t>)"
                  by (simp add: true_false_only_truth_values x_def)
                then have x_def2: "(x = \<langle>\<f>,i\<rangle>) \<or> (x = \<langle>\<t>,i\<rangle>)"
                  using x_def by auto
                show "(eval_func A \<Omega> \<circ>\<^sub>c id\<^sub>c \<Omega> \<times>\<^sub>f f) \<circ>\<^sub>c x = (eval_func A \<Omega> \<circ>\<^sub>c id\<^sub>c \<Omega> \<times>\<^sub>f g) \<circ>\<^sub>c x"
                proof(cases "(x = \<langle>\<f>,i\<rangle>)",auto)
                  assume case1: "x = \<langle>\<f>,i\<rangle>"
                  have "(eval_func A \<Omega> \<circ>\<^sub>c (id\<^sub>c \<Omega> \<times>\<^sub>f f)) \<circ>\<^sub>c \<langle>\<f>,i\<rangle> = eval_func A \<Omega> \<circ>\<^sub>c ((id\<^sub>c \<Omega> \<times>\<^sub>f f) \<circ>\<^sub>c \<langle>\<f>,i\<rangle>)"
                    using case1 comp_associative2 x_type by (typecheck_cfuncs, auto)
                  also have "... = eval_func A \<Omega> \<circ>\<^sub>c \<langle>id\<^sub>c \<Omega> \<circ>\<^sub>c  \<f>,f \<circ>\<^sub>c i\<rangle>"
                    using cfunc_cross_prod_comp_cfunc_prod i_def id1_eq id1_is by (typecheck_cfuncs, auto)
                  also have "... = eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f>, f \<rangle>"
                    using f_type false_func_type i_def id_left_unit2 id_right_unit2 by auto
                  also have "... = eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f>, g\<rangle>"
                    using equation3 by blast
                  also have "... = eval_func A \<Omega> \<circ>\<^sub>c \<langle>id\<^sub>c \<Omega> \<circ>\<^sub>c  \<f>,g \<circ>\<^sub>c i\<rangle>"
                    by (typecheck_cfuncs, simp add: i_def id_left_unit2 id_right_unit2)
                  also have "... = eval_func A \<Omega> \<circ>\<^sub>c ((id\<^sub>c \<Omega> \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>\<f>,i\<rangle>)"
                    using cfunc_cross_prod_comp_cfunc_prod i_def id1_eq id1_is by (typecheck_cfuncs, auto)
                  also have "... = (eval_func A \<Omega> \<circ>\<^sub>c (id\<^sub>c \<Omega> \<times>\<^sub>f g)) \<circ>\<^sub>c \<langle>\<f>,i\<rangle>"
                    using case1 comp_associative2 x_type by (typecheck_cfuncs, auto)
                  then show "(eval_func A \<Omega> \<circ>\<^sub>c id\<^sub>c \<Omega> \<times>\<^sub>f f) \<circ>\<^sub>c \<langle>\<f>,i\<rangle> = (eval_func A \<Omega> \<circ>\<^sub>c id\<^sub>c \<Omega> \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>\<f>,i\<rangle>"
                    by (simp add: calculation)
              next
                  assume case2: "x \<noteq> \<langle>\<f>,i\<rangle>"
                  then have x_eq: "x = \<langle>\<t>,i\<rangle>"
                    using x_def2 by blast
                  have "(eval_func A \<Omega> \<circ>\<^sub>c (id\<^sub>c \<Omega> \<times>\<^sub>f f)) \<circ>\<^sub>c \<langle>\<t>,i\<rangle> = eval_func A \<Omega> \<circ>\<^sub>c ((id\<^sub>c \<Omega> \<times>\<^sub>f f) \<circ>\<^sub>c \<langle>\<t>,i\<rangle>)"
                      using case2 x_eq comp_associative2 x_type by (typecheck_cfuncs, auto)
                  also have "... = eval_func A \<Omega> \<circ>\<^sub>c \<langle>id\<^sub>c \<Omega> \<circ>\<^sub>c  \<t>,f \<circ>\<^sub>c i\<rangle>"
                      using cfunc_cross_prod_comp_cfunc_prod i_def id1_eq id1_is by (typecheck_cfuncs, auto)
                  also have "... = eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t>, f \<rangle>"
                    using f_type i_def id_left_unit2 id_right_unit2 true_func_type by auto
                  also have "... = eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t>, g\<rangle>"
                    using equation3 by blast
                  also have "... = eval_func A \<Omega> \<circ>\<^sub>c \<langle>id\<^sub>c \<Omega> \<circ>\<^sub>c  \<t>,g \<circ>\<^sub>c i\<rangle>"
                      by (typecheck_cfuncs, simp add: i_def id_left_unit2 id_right_unit2)
                  also have "... = eval_func A \<Omega> \<circ>\<^sub>c ((id\<^sub>c \<Omega> \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>\<t>,i\<rangle>)"
                      using cfunc_cross_prod_comp_cfunc_prod i_def id1_eq id1_is by (typecheck_cfuncs, auto)
                  also have "... = (eval_func A \<Omega> \<circ>\<^sub>c (id\<^sub>c \<Omega> \<times>\<^sub>f g)) \<circ>\<^sub>c \<langle>\<t>,i\<rangle>"
                    using comp_associative2 x_eq x_type by (typecheck_cfuncs, blast)
                  then show "(eval_func A \<Omega> \<circ>\<^sub>c id\<^sub>c \<Omega> \<times>\<^sub>f f) \<circ>\<^sub>c x = (eval_func A \<Omega> \<circ>\<^sub>c id\<^sub>c \<Omega> \<times>\<^sub>f g) \<circ>\<^sub>c x"
                    by (simp add: calculation x_eq)
                qed
              qed
            qed
            then show "eval_func A \<Omega> \<circ>\<^sub>c id\<^sub>c \<Omega> \<times>\<^sub>f f \<circ>\<^sub>c id_1 = eval_func A \<Omega> \<circ>\<^sub>c id\<^sub>c \<Omega> \<times>\<^sub>f g \<circ>\<^sub>c id_1"
              using  f_type g_type same_evals_equal by blast
          qed
        qed
      qed
    qed
    then have "monomorphism(\<phi>)"
      using injective_imp_monomorphism by auto
    have "surjective(\<phi>)"
      unfolding surjective_def
    proof(auto)
      fix y 
      assume "y \<in>\<^sub>c codomain \<phi>" then have y_type[type_rule]: "y \<in>\<^sub>c A \<times>\<^sub>c A"
        using \<phi>_type cfunc_type_def by auto
      then obtain a1 a2 where y_def[type_rule]: "y = \<langle>a1,a2\<rangle> \<and> a1 \<in>\<^sub>c A \<and> a2 \<in>\<^sub>c A"
        using cart_prod_decomp by blast
      then have aua: "(a1 \<amalg> a2): one \<Coprod> one \<rightarrow> A"
        by (typecheck_cfuncs, simp add: y_def)
     
    
      obtain f where f_def: "f = ((a1 \<amalg> a2) \<circ>\<^sub>c case_bool  \<circ>\<^sub>c left_cart_proj \<Omega> one)\<^sup>\<sharp>"
        by simp
      then have f_type[type_rule]: "f \<in>\<^sub>c A\<^bsup>\<Omega>\<^esup>"
       using case_bool_type aua cfunc_type_def codomain_comp domain_comp f_def left_cart_proj_type transpose_func_type by auto
     have a1_is: "(eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>) \<circ>\<^sub>c f = a1"
     proof-
       have "(eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>) \<circ>\<^sub>c f = eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> \<circ>\<^sub>c f"
         by (typecheck_cfuncs, simp add: comp_associative2)
       also have "... = eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c f, id(A\<^bsup>\<Omega>\<^esup>) \<circ>\<^sub>c f\<rangle>"
         by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
       also have "... = eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<t>, f\<rangle>"
         by (metis cfunc_type_def f_type id_left_unit id_right_unit id_type one_unique_element terminal_func_comp terminal_func_type true_func_type)
       also have "... = eval_func A \<Omega> \<circ>\<^sub>c \<langle>id(\<Omega>) \<circ>\<^sub>c \<t>, f \<circ>\<^sub>c id(one)\<rangle>"
         by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2)
       also have "... = eval_func A \<Omega> \<circ>\<^sub>c (id(\<Omega>) \<times>\<^sub>f f) \<circ>\<^sub>c \<langle>\<t>, id(one)\<rangle>"
         by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
       also have "... = (eval_func A \<Omega> \<circ>\<^sub>c (id(\<Omega>) \<times>\<^sub>f f)) \<circ>\<^sub>c \<langle>\<t>, id(one)\<rangle>"
         using comp_associative2 by (typecheck_cfuncs, blast)
       also have "... = ((a1 \<amalg> a2) \<circ>\<^sub>c case_bool  \<circ>\<^sub>c left_cart_proj \<Omega> one) \<circ>\<^sub>c \<langle>\<t>, id(one)\<rangle>"
         by (typecheck_cfuncs, metis  aua f_def flat_cancels_sharp inv_transpose_func_def2)
       also have "... = (a1 \<amalg> a2) \<circ>\<^sub>c case_bool  \<circ>\<^sub>c \<t>"
         by (typecheck_cfuncs, smt case_bool_type aua comp_associative2 left_cart_proj_cfunc_prod)
       also have "... = (a1 \<amalg> a2) \<circ>\<^sub>c left_coproj one one"
         by (simp add: case_bool_true)
       also have "... = a1"
         using left_coproj_cfunc_coprod y_def by blast
       then show ?thesis using calculation by auto
     qed
     have a2_is: "(eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>) \<circ>\<^sub>c f = a2"
     proof-
       have "(eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle>) \<circ>\<^sub>c f = eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub>, id(A\<^bsup>\<Omega>\<^esup>)\<rangle> \<circ>\<^sub>c f"
         by (typecheck_cfuncs, simp add: comp_associative2)
       also have "... = eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f> \<circ>\<^sub>c \<beta>\<^bsub>A\<^bsup>\<Omega>\<^esup>\<^esub> \<circ>\<^sub>c f, id(A\<^bsup>\<Omega>\<^esup>) \<circ>\<^sub>c f\<rangle>"
         by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
       also have "... = eval_func A \<Omega> \<circ>\<^sub>c \<langle>\<f>, f\<rangle>"
         by (metis cfunc_type_def f_type id_left_unit id_right_unit id_type one_unique_element terminal_func_comp terminal_func_type false_func_type)
       also have "... = eval_func A \<Omega> \<circ>\<^sub>c \<langle>id(\<Omega>) \<circ>\<^sub>c \<f>, f \<circ>\<^sub>c id(one)\<rangle>"
         by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2)
       also have "... = eval_func A \<Omega> \<circ>\<^sub>c (id(\<Omega>) \<times>\<^sub>f f) \<circ>\<^sub>c \<langle>\<f>, id(one)\<rangle>"
         by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
       also have "... = (eval_func A \<Omega> \<circ>\<^sub>c (id(\<Omega>) \<times>\<^sub>f f)) \<circ>\<^sub>c \<langle>\<f>, id(one)\<rangle>"
         using comp_associative2 by (typecheck_cfuncs, blast)
       also have "... = ((a1 \<amalg> a2) \<circ>\<^sub>c case_bool  \<circ>\<^sub>c left_cart_proj \<Omega> one) \<circ>\<^sub>c \<langle>\<f>, id(one)\<rangle>"
         by (typecheck_cfuncs, metis  aua f_def flat_cancels_sharp inv_transpose_func_def2)
       also have "... = (a1 \<amalg> a2) \<circ>\<^sub>c case_bool  \<circ>\<^sub>c \<f>"
         by (typecheck_cfuncs, smt aua comp_associative2 left_cart_proj_cfunc_prod)
       also have "... = (a1 \<amalg> a2) \<circ>\<^sub>c right_coproj one one"
         by (simp add: case_bool_false)
       also have "... = a2"
         using right_coproj_cfunc_coprod y_def by blast
       then show ?thesis using calculation by auto
     qed
     have "\<phi> \<circ>\<^sub>c f  = \<langle>a1,a2\<rangle>"
       unfolding \<phi>_def by (typecheck_cfuncs, simp add: a1_is a2_is cfunc_prod_comp)
     then show "\<exists>x. x \<in>\<^sub>c domain \<phi> \<and> \<phi> \<circ>\<^sub>c x = y"
       using \<phi>_type cfunc_type_def f_type y_def by auto
   qed
   then have "epimorphism(\<phi>)"
     by (simp add: surjective_is_epimorphism)
   then have "isomorphism(\<phi>)"
     by (simp add: \<open>monomorphism \<phi>\<close> epi_mon_is_iso)
   then show ?thesis
     using \<phi>_type is_isomorphic_def by blast
qed







(*Perhaps consider putting the next few small lemmas inside the Truth.thy file*)




(*****)


lemma prod_leq_exp:
  assumes "\<not>(terminal_object Y)"
  shows "(X \<times>\<^sub>c Y) \<le>\<^sub>c (Y\<^bsup>X\<^esup>)"
proof(cases "initial_object Y")
  show "initial_object Y \<Longrightarrow> X \<times>\<^sub>c Y \<le>\<^sub>c Y\<^bsup>X\<^esup>"
    by (metis X_times_zero initial_iso_empty initial_maps_mono initial_object_def is_smaller_than_def iso_empty_initial isomorphic_is_reflexive isomorphic_is_transitive prod_pres_iso)
next
  assume "\<not> initial_object Y"
  then obtain y1 y2 where y1_type[type_rule]: "y1 \<in>\<^sub>c Y" and y2_type[type_rule]: "y2 \<in>\<^sub>c Y" and y1_not_y2: "y1\<noteq>y2"
    using assms not_init_not_term by blast
  show "(X \<times>\<^sub>c Y) \<le>\<^sub>c (Y\<^bsup>X\<^esup>)"
  proof(cases "X \<cong> \<Omega>")
      assume "X \<cong> \<Omega>"
      have "\<Omega>  \<le>\<^sub>c  Y"
         using \<open>\<not> initial_object Y\<close> assms not_init_not_term size_2plus_sets by blast
      then obtain m where m_type[type_rule]: "m : \<Omega>  \<rightarrow>  Y" and m_mono: "monomorphism m"
        using is_smaller_than_def by blast
      then have m_id_type[type_rule]: "m \<times>\<^sub>f id(Y) : \<Omega> \<times>\<^sub>c Y \<rightarrow> Y \<times>\<^sub>c Y"
        by typecheck_cfuncs
      have m_id_mono: "monomorphism (m \<times>\<^sub>f id(Y))"
        by (typecheck_cfuncs, simp add: cfunc_cross_prod_mono id_isomorphism iso_imp_epi_and_monic m_mono)  
      obtain n where n_type[type_rule]: "n : Y \<times>\<^sub>c Y  \<rightarrow>  Y\<^bsup>\<Omega>\<^esup>" and n_mono: "monomorphism n"
        by (metis epis_give_monos is_isomorphic_def iso_imp_epi_and_monic sets_squared)
      obtain r where r_type[type_rule]: "r : Y\<^bsup>\<Omega>\<^esup>  \<rightarrow>  Y\<^bsup>X\<^esup>" and r_mono: "monomorphism r"
        by (meson \<open>X \<cong> \<Omega>\<close> exp_pres_iso_right is_isomorphic_def iso_imp_epi_and_monic isomorphic_is_symmetric)
      obtain q where q_type[type_rule]: "q : X \<times>\<^sub>c Y  \<rightarrow>  \<Omega> \<times>\<^sub>c Y" and q_mono: "monomorphism q"
        by (meson \<open>X \<cong> \<Omega>\<close> id_isomorphism id_type is_isomorphic_def iso_imp_epi_and_monic prod_pres_iso) 
      have rnmq_type[type_rule]: "r \<circ>\<^sub>c n \<circ>\<^sub>c (m \<times>\<^sub>f id(Y)) \<circ>\<^sub>c q : X \<times>\<^sub>c Y \<rightarrow> Y\<^bsup>X\<^esup>"
        by typecheck_cfuncs
      have "monomorphism(r \<circ>\<^sub>c n \<circ>\<^sub>c (m \<times>\<^sub>f id(Y)) \<circ>\<^sub>c q)"
        by (typecheck_cfuncs, simp add: cfunc_type_def composition_of_monic_pair_is_monic m_id_mono n_mono q_mono r_mono)
      then show ?thesis
        by (meson is_smaller_than_def rnmq_type)
    next
      assume "\<not> X \<cong> \<Omega>"
      show "X \<times>\<^sub>c Y \<le>\<^sub>c Y\<^bsup>X\<^esup>"
      proof(cases "initial_object X")
        show "initial_object X \<Longrightarrow> X \<times>\<^sub>c Y \<le>\<^sub>c Y\<^bsup>X\<^esup>"
          by (metis is_empty_def initial_iso_empty initial_maps_mono initial_object_def 
              is_smaller_than_def isomorphic_is_transitive no_el_iff_iso_0 nonempty_def 
              not_init_not_term prod_with_empty_is_empty2 product_commutes terminal_object_def)
      next
      assume "\<not> initial_object X"
      show "X \<times>\<^sub>c Y \<le>\<^sub>c Y\<^bsup>X\<^esup>"
      proof(cases "terminal_object X")
        assume "terminal_object X"
        then have "X \<cong> one"
          by (simp add: one_terminal_object terminal_objects_isomorphic)
        have "X \<times>\<^sub>c Y \<cong> Y"
          by (simp add: \<open>terminal_object X\<close> prod_with_term_obj1)
        then have "X \<times>\<^sub>c Y \<cong> Y\<^bsup>X\<^esup>"
          by (meson \<open>X \<cong> one\<close> exp_pres_iso_right exp_set_inj isomorphic_is_symmetric isomorphic_is_transitive set_to_power_one)
        then show ?thesis
          using is_isomorphic_def is_smaller_than_def iso_imp_epi_and_monic by blast
      next
        assume "\<not> terminal_object X"

        obtain into where into_def: "into = (left_cart_proj Y one \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1))) 
                               \<circ>\<^sub>c dist_prod_coprod_inv Y one one \<circ>\<^sub>c (id Y \<times>\<^sub>f case_bool) \<circ>\<^sub>c (id Y \<times>\<^sub>f eq_pred X) "
          by simp
        then have into_type[type_rule]: "into : Y \<times>\<^sub>c (X \<times>\<^sub>c X) \<rightarrow> Y"
          by (simp, typecheck_cfuncs)
   

        obtain \<Theta> where \<Theta>_def: "\<Theta> = (into \<circ>\<^sub>c associate_right Y X X \<circ>\<^sub>c swap X (Y \<times>\<^sub>c X))\<^sup>\<sharp> \<circ>\<^sub>c swap X Y"
          by auto
  
        have \<Theta>_type[type_rule]: "\<Theta> : X \<times>\<^sub>c Y \<rightarrow> Y\<^bsup>X\<^esup>"
          unfolding \<Theta>_def by typecheck_cfuncs

        have f0: "\<And>x. \<And> y. \<And> z. x \<in>\<^sub>c X \<and> y \<in>\<^sub>c Y \<and> z \<in>\<^sub>c X \<Longrightarrow> (\<Theta> \<circ>\<^sub>c \<langle>x, y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id X, \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = into \<circ>\<^sub>c   \<langle>y, \<langle>x, z\<rangle>\<rangle>"
        proof(auto)
          fix x y z
          assume x_type[type_rule]: "x \<in>\<^sub>c X"
          assume y_type[type_rule]: "y \<in>\<^sub>c Y"
          assume z_type[type_rule]: "z \<in>\<^sub>c X"
          show "(\<Theta> \<circ>\<^sub>c \<langle>x,y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id\<^sub>c X,\<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = into \<circ>\<^sub>c \<langle>y,\<langle>x,z\<rangle>\<rangle>"
          proof - 
            have "(\<Theta> \<circ>\<^sub>c \<langle>x,y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id\<^sub>c X,\<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = (\<Theta> \<circ>\<^sub>c \<langle>x,y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id\<^sub>c X \<circ>\<^sub>c z,\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c z\<rangle>"
              by (typecheck_cfuncs, simp add: cfunc_prod_comp)
            also have "... = (\<Theta> \<circ>\<^sub>c \<langle>x,y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>z,id one\<rangle>"
              by (typecheck_cfuncs, metis id_left_unit2 one_unique_element)
            also have "... = (\<Theta>\<^sup>\<flat> \<circ>\<^sub>c (id(X) \<times>\<^sub>f \<langle>x,y\<rangle>)) \<circ>\<^sub>c \<langle>z,id one\<rangle>"
              using inv_transpose_of_composition by (typecheck_cfuncs, presburger)
            also have "... = \<Theta>\<^sup>\<flat> \<circ>\<^sub>c (id(X) \<times>\<^sub>f \<langle>x,y\<rangle>) \<circ>\<^sub>c \<langle>z,id one\<rangle>"
              using comp_associative2 by (typecheck_cfuncs, auto)
            also have "... = \<Theta>\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X) \<circ>\<^sub>c  z, \<langle>x,y\<rangle> \<circ>\<^sub>c  id one\<rangle>"
              by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
            also have "... = \<Theta>\<^sup>\<flat> \<circ>\<^sub>c \<langle>z,\<langle>x,y\<rangle>\<rangle>"
              by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2)
            also have "... = ((into \<circ>\<^sub>c associate_right Y X X \<circ>\<^sub>c swap X (Y \<times>\<^sub>c X))\<^sup>\<sharp> \<circ>\<^sub>c swap X Y)\<^sup>\<flat> \<circ>\<^sub>c \<langle>z,\<langle>x,y\<rangle>\<rangle>"
              by (simp add: \<Theta>_def)
            also have "... = ((into \<circ>\<^sub>c associate_right Y X X \<circ>\<^sub>c swap X (Y \<times>\<^sub>c X))\<^sup>\<sharp>\<^sup>\<flat> \<circ>\<^sub>c (id X \<times>\<^sub>f swap X Y)) \<circ>\<^sub>c \<langle>z,\<langle>x,y\<rangle>\<rangle>"
              using inv_transpose_of_composition by (typecheck_cfuncs, presburger)
            also have "... = (into \<circ>\<^sub>c associate_right Y X X \<circ>\<^sub>c swap X (Y \<times>\<^sub>c X)) \<circ>\<^sub>c  (id X \<times>\<^sub>f swap X Y) \<circ>\<^sub>c \<langle>z,\<langle>x,y\<rangle>\<rangle>"
              by (typecheck_cfuncs, simp add: comp_associative2 inv_transpose_func_def2 transpose_func_def)
            also have "... = (into \<circ>\<^sub>c associate_right Y X X \<circ>\<^sub>c swap X (Y \<times>\<^sub>c X)) \<circ>\<^sub>c  \<langle>id X \<circ>\<^sub>c z, swap X Y \<circ>\<^sub>c \<langle>x,y\<rangle>\<rangle>"
              by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
            also have "... = (into \<circ>\<^sub>c associate_right Y X X \<circ>\<^sub>c swap X (Y \<times>\<^sub>c X)) \<circ>\<^sub>c  \<langle>z, \<langle>y,x\<rangle>\<rangle>"
              using id_left_unit2 swap_ap by (typecheck_cfuncs, presburger)
            also have "... = into \<circ>\<^sub>c associate_right Y X X \<circ>\<^sub>c swap X (Y \<times>\<^sub>c X) \<circ>\<^sub>c  \<langle>z, \<langle>y,x\<rangle>\<rangle>"
              by (typecheck_cfuncs, metis cfunc_type_def comp_associative)
            also have "... = into \<circ>\<^sub>c associate_right Y X X \<circ>\<^sub>c   \<langle>\<langle>y,x\<rangle>, z\<rangle>"
              using swap_ap by (typecheck_cfuncs, presburger)
            also have "... = into \<circ>\<^sub>c   \<langle>y, \<langle>x, z\<rangle>\<rangle>"
              using associate_right_ap by (typecheck_cfuncs, presburger)
            then show ?thesis
              using calculation by presburger
          qed
        qed
  
        have f1: "\<And>x y. x \<in>\<^sub>c X \<Longrightarrow> y \<in>\<^sub>c Y  \<Longrightarrow> (\<Theta> \<circ>\<^sub>c \<langle>x, y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id X, \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x = y"
        proof - 
          fix x y 
          assume x_type[type_rule]: "x \<in>\<^sub>c X"
          assume y_type[type_rule]: "y \<in>\<^sub>c Y"
          have "(\<Theta> \<circ>\<^sub>c \<langle>x, y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id X, \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x = into \<circ>\<^sub>c   \<langle>y, \<langle>x, x\<rangle>\<rangle>"
            by (simp add: f0 x_type y_type)
          also have "... = (left_cart_proj Y one \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1)))
                                 \<circ>\<^sub>c dist_prod_coprod_inv Y one one \<circ>\<^sub>c (id Y \<times>\<^sub>f case_bool) \<circ>\<^sub>c (id Y \<times>\<^sub>f eq_pred X) \<circ>\<^sub>c   \<langle>y, \<langle>x, x\<rangle>\<rangle>"
            using cfunc_type_def comp_associative comp_type into_def by (typecheck_cfuncs, fastforce)
          also have "... = (left_cart_proj Y one \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1)))
                                 \<circ>\<^sub>c dist_prod_coprod_inv Y one one \<circ>\<^sub>c (id Y \<times>\<^sub>f case_bool) \<circ>\<^sub>c  \<langle>id Y \<circ>\<^sub>c y, eq_pred X \<circ>\<^sub>c  \<langle>x, x\<rangle>\<rangle>"
            by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
         also have "... = (left_cart_proj Y one \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1))) 
                                 \<circ>\<^sub>c dist_prod_coprod_inv Y one one \<circ>\<^sub>c (id Y \<times>\<^sub>f case_bool) \<circ>\<^sub>c  \<langle>y, \<t>\<rangle>"
            by (typecheck_cfuncs, metis eq_pred_iff_eq id_left_unit2)
          also have "... = (left_cart_proj Y one \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1))) 
                                 \<circ>\<^sub>c dist_prod_coprod_inv Y one one  \<circ>\<^sub>c  \<langle>y, left_coproj one one\<rangle>"
            by (typecheck_cfuncs, simp add: case_bool_true cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
          also have "... = (left_cart_proj Y one \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1))) 
                                 \<circ>\<^sub>c dist_prod_coprod_inv Y one one  \<circ>\<^sub>c  \<langle>y, left_coproj one one \<circ>\<^sub>c id one\<rangle>"
            by (typecheck_cfuncs, metis id_right_unit2)
          also have "... = (left_cart_proj Y one \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1))) 
                                 \<circ>\<^sub>c left_coproj (Y \<times>\<^sub>c one) (Y \<times>\<^sub>c one) \<circ>\<^sub>c \<langle>y,id one\<rangle>"
            using dist_prod_coprod_inv_left_ap by (typecheck_cfuncs, presburger)
          also have "... = ((left_cart_proj Y one \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1))) 
                                 \<circ>\<^sub>c left_coproj (Y \<times>\<^sub>c one) (Y \<times>\<^sub>c one)) \<circ>\<^sub>c \<langle>y,id one\<rangle>"
            by (typecheck_cfuncs, meson comp_associative2)
          also have "... = left_cart_proj Y one \<circ>\<^sub>c \<langle>y,id one\<rangle>"
            using left_coproj_cfunc_coprod by (typecheck_cfuncs, presburger)
          also have "... = y"
            by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod)
          then show "(\<Theta> \<circ>\<^sub>c \<langle>x, y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id X, \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x = y"
            by (simp add: calculation into_def)
        qed
  
        have f2: "\<And>x y z. x \<in>\<^sub>c X \<Longrightarrow> y \<in>\<^sub>c Y  \<Longrightarrow>  z \<in>\<^sub>c X \<Longrightarrow> z \<noteq> x \<Longrightarrow> y \<noteq> y1 \<Longrightarrow> (\<Theta> \<circ>\<^sub>c \<langle>x, y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id X, \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = y1"
        proof - 
          fix x y z
          assume x_type[type_rule]: "x \<in>\<^sub>c X"
          assume y_type[type_rule]: "y \<in>\<^sub>c Y"
          assume z_type[type_rule]: "z \<in>\<^sub>c X"
          assume "z \<noteq> x"
          assume "y \<noteq> y1"
          have "(\<Theta> \<circ>\<^sub>c \<langle>x, y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id X, \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = into \<circ>\<^sub>c   \<langle>y, \<langle>x, z\<rangle>\<rangle>"
            by (simp add: f0 x_type y_type z_type)
          also have "... = (left_cart_proj Y one \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1)))
                                 \<circ>\<^sub>c dist_prod_coprod_inv Y one one \<circ>\<^sub>c (id Y \<times>\<^sub>f case_bool) \<circ>\<^sub>c (id Y \<times>\<^sub>f eq_pred X) \<circ>\<^sub>c   \<langle>y, \<langle>x, z\<rangle>\<rangle>"
            using cfunc_type_def comp_associative comp_type into_def by (typecheck_cfuncs, fastforce)
          also have "... = (left_cart_proj Y one \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1)))
                                 \<circ>\<^sub>c dist_prod_coprod_inv Y one one \<circ>\<^sub>c (id Y \<times>\<^sub>f case_bool) \<circ>\<^sub>c  \<langle>id Y \<circ>\<^sub>c y, eq_pred X \<circ>\<^sub>c  \<langle>x, z\<rangle>\<rangle>"
            by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
          also have "... = (left_cart_proj Y one \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1))) 
                                 \<circ>\<^sub>c dist_prod_coprod_inv Y one one \<circ>\<^sub>c (id Y \<times>\<^sub>f case_bool) \<circ>\<^sub>c  \<langle>y, \<f>\<rangle>"
            by (typecheck_cfuncs, metis \<open>z \<noteq> x\<close> eq_pred_iff_eq_conv id_left_unit2)
          also have "... = (left_cart_proj Y one \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1))) 
                                 \<circ>\<^sub>c dist_prod_coprod_inv Y one one  \<circ>\<^sub>c  \<langle>y, right_coproj one one\<rangle>"
            by (typecheck_cfuncs, simp add: case_bool_false cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
          also have "... = (left_cart_proj Y one \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1)))
                                 \<circ>\<^sub>c dist_prod_coprod_inv Y one one  \<circ>\<^sub>c  \<langle>y, right_coproj one one \<circ>\<^sub>c id one\<rangle>"
            by (typecheck_cfuncs, simp add: id_right_unit2)
          also have "... = (left_cart_proj Y one \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1)))
                                 \<circ>\<^sub>c right_coproj (Y \<times>\<^sub>c one) (Y \<times>\<^sub>c one) \<circ>\<^sub>c \<langle>y,id one\<rangle>"
            using dist_prod_coprod_inv_right_ap by (typecheck_cfuncs, presburger)
          also have "... = ((left_cart_proj Y one \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1))) 
                                 \<circ>\<^sub>c right_coproj (Y \<times>\<^sub>c one) (Y \<times>\<^sub>c one)) \<circ>\<^sub>c \<langle>y,id one\<rangle>"
            by (typecheck_cfuncs, meson comp_associative2)
          also have "... = ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1)) \<circ>\<^sub>c \<langle>y,id one\<rangle>"
            using right_coproj_cfunc_coprod by (typecheck_cfuncs, auto)
          also have "... = (y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1) \<circ>\<^sub>c \<langle>y,id one\<rangle>"
            using comp_associative2 by (typecheck_cfuncs, force)
          also have "... = (y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y  \<circ>\<^sub>c \<langle>y,y1\<rangle>"
            by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2)
          also have "... = (y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c \<f>"
            by (typecheck_cfuncs, metis \<open>y \<noteq> y1\<close> eq_pred_iff_eq_conv)
          also have "... = y1"
            using case_bool_false right_coproj_cfunc_coprod by (typecheck_cfuncs, presburger)
          then show "(\<Theta> \<circ>\<^sub>c \<langle>x, y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id X, \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = y1"
            by (simp add: calculation)
        qed
      
  
  
  
        have f3: "\<And>x z. x \<in>\<^sub>c X \<Longrightarrow>  z \<in>\<^sub>c X \<Longrightarrow> z \<noteq> x \<Longrightarrow>  (\<Theta> \<circ>\<^sub>c \<langle>x, y1\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id X, \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = y2"
        proof - 
          fix x y z
          assume x_type[type_rule]: "x \<in>\<^sub>c X"
          assume z_type[type_rule]: "z \<in>\<^sub>c X"
          assume "z \<noteq> x"
          have "(\<Theta> \<circ>\<^sub>c \<langle>x, y1\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id X, \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = into \<circ>\<^sub>c   \<langle>y1, \<langle>x, z\<rangle>\<rangle>"
            by (simp add: f0 x_type y1_type z_type)
          also have "... = (left_cart_proj Y one \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1)))
                                 \<circ>\<^sub>c dist_prod_coprod_inv Y one one \<circ>\<^sub>c (id Y \<times>\<^sub>f case_bool) \<circ>\<^sub>c (id Y \<times>\<^sub>f eq_pred X) \<circ>\<^sub>c   \<langle>y1, \<langle>x, z\<rangle>\<rangle>"
            using cfunc_type_def comp_associative comp_type into_def by (typecheck_cfuncs, fastforce)
          also have "... = (left_cart_proj Y one \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1)))
                                 \<circ>\<^sub>c dist_prod_coprod_inv Y one one \<circ>\<^sub>c (id Y \<times>\<^sub>f case_bool) \<circ>\<^sub>c  \<langle>id Y \<circ>\<^sub>c y1, eq_pred X \<circ>\<^sub>c  \<langle>x, z\<rangle>\<rangle>"
            by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
          also have "... = (left_cart_proj Y one \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1))) 
                                 \<circ>\<^sub>c dist_prod_coprod_inv Y one one \<circ>\<^sub>c (id Y \<times>\<^sub>f case_bool) \<circ>\<^sub>c  \<langle>y1, \<f>\<rangle>"
            by (typecheck_cfuncs, metis \<open>z \<noteq> x\<close> eq_pred_iff_eq_conv id_left_unit2)
          also have "... = (left_cart_proj Y one \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1))) 
                                 \<circ>\<^sub>c dist_prod_coprod_inv Y one one  \<circ>\<^sub>c  \<langle>y1, right_coproj one one\<rangle>"
            by (typecheck_cfuncs, simp add: case_bool_false cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
          also have "... = (left_cart_proj Y one \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1)))
                                 \<circ>\<^sub>c dist_prod_coprod_inv Y one one  \<circ>\<^sub>c  \<langle>y1, right_coproj one one \<circ>\<^sub>c id one\<rangle>"
            by (typecheck_cfuncs, simp add: id_right_unit2)
          also have "... = (left_cart_proj Y one \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1)))
                                 \<circ>\<^sub>c right_coproj (Y \<times>\<^sub>c one) (Y \<times>\<^sub>c one) \<circ>\<^sub>c \<langle>y1,id one\<rangle>"
            using dist_prod_coprod_inv_right_ap by (typecheck_cfuncs, presburger)
          also have "... = ((left_cart_proj Y one \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1))) 
                                 \<circ>\<^sub>c right_coproj (Y \<times>\<^sub>c one) (Y \<times>\<^sub>c one)) \<circ>\<^sub>c \<langle>y1,id one\<rangle>"
            by (typecheck_cfuncs, meson comp_associative2)
          also have "... = ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1)) \<circ>\<^sub>c \<langle>y1,id one\<rangle>"
            using right_coproj_cfunc_coprod by (typecheck_cfuncs, auto)
          also have "... = (y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1) \<circ>\<^sub>c \<langle>y1,id one\<rangle>"
            using comp_associative2 by (typecheck_cfuncs, force)
          also have "... = (y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y  \<circ>\<^sub>c \<langle>y1,y1\<rangle>"
            by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2)
          also have "... = (y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c \<t>"
            by (typecheck_cfuncs, metis eq_pred_iff_eq)
          also have "... = y2"
            using case_bool_true left_coproj_cfunc_coprod by (typecheck_cfuncs, presburger)
          then show "(\<Theta> \<circ>\<^sub>c \<langle>x, y1\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id X, \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = y2"
            by (simp add: calculation)
        qed
  
     have \<Theta>_injective: "injective(\<Theta>)"
     proof(unfold injective_def, auto)
       fix xy st
       assume xy_type[type_rule]: "xy \<in>\<^sub>c domain \<Theta>"
       assume st_type[type_rule]: "st \<in>\<^sub>c domain \<Theta>"
       assume equals: "\<Theta> \<circ>\<^sub>c xy = \<Theta> \<circ>\<^sub>c st"
       obtain x y where x_type[type_rule]: "x \<in>\<^sub>c X" and y_type[type_rule]: "y \<in>\<^sub>c Y" and xy_def: "xy = \<langle>x,y\<rangle>"
         by (metis \<Theta>_type cart_prod_decomp cfunc_type_def xy_type)
       obtain s t where s_type[type_rule]: "s \<in>\<^sub>c X" and t_type[type_rule]: "t \<in>\<^sub>c Y" and st_def: "st = \<langle>s,t\<rangle>"
         by (metis \<Theta>_type cart_prod_decomp cfunc_type_def st_type)   
       have equals2: "\<Theta> \<circ>\<^sub>c \<langle>x,y\<rangle> = \<Theta> \<circ>\<^sub>c \<langle>s,t\<rangle>"
         using equals st_def xy_def by auto
       have "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
       proof(cases "y = y1")  
         assume "y = y1"
         show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
         proof(cases "t = y1")
           show "t = y1 \<Longrightarrow> \<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
             by (typecheck_cfuncs, metis \<open>y = y1\<close> equals f1 f3 st_def xy_def y1_not_y2)
         next
           assume "t \<noteq> y1"
           show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
           proof(cases "s = x")
             show "s = x \<Longrightarrow> \<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
               by (typecheck_cfuncs, metis equals2 f1)
           next
             assume "s \<noteq> x"  (*This step, in particular, is why we require X to not be isomorphic to Omega*)
             obtain z where z_type[type_rule]: "z \<in>\<^sub>c X" and z_not_x: "z \<noteq> x" and z_not_s: "z \<noteq> s"
               by (metis \<open>\<not> X \<cong> \<Omega>\<close> \<open>\<not> initial_object X\<close> \<open>\<not> terminal_object X\<close> sets_size_3_plus)
             have t_sz: "(\<Theta> \<circ>\<^sub>c \<langle>s, t\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id X, \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = y1"
               by (simp add: \<open>t \<noteq> y1\<close> f2 s_type t_type z_not_s z_type)
             have y_xz: "(\<Theta> \<circ>\<^sub>c \<langle>x, y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id X, \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = y2"
               by (simp add: \<open>y = y1\<close> f3 x_type z_not_x z_type)    
             then have "y1 = y2"
               using equals2 t_sz by auto
             then have False
               using y1_not_y2 by auto
             then show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
               by simp
           qed
         qed
       next
         assume "y \<noteq> y1"
         show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
         proof(cases "y = y2")
           assume "y = y2"
           show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
           proof(cases "t = y2",auto)
             show "t = y2 \<Longrightarrow> \<langle>x,y\<rangle> = \<langle>s,y2\<rangle>"
               by (typecheck_cfuncs, metis \<open>y = y2\<close> \<open>y \<noteq> y1\<close> equals f1 f2 st_def xy_def)
           next
             assume "t \<noteq> y2"
             show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
             proof(cases "x = s", auto)
               show "x = s \<Longrightarrow> \<langle>s,y\<rangle> = \<langle>s,t\<rangle>"
                 by (metis equals2 f1 s_type t_type y_type)
             next
               assume "x \<noteq> s"
               show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
               proof(cases "t = y1",auto)
                 show "t = y1 \<Longrightarrow> \<langle>x,y\<rangle> = \<langle>s,y1\<rangle>"
                   by (metis \<open>\<not> X \<cong> \<Omega>\<close> \<open>\<not> initial_object X\<close> \<open>\<not> terminal_object X\<close> \<open>y = y2\<close> \<open>y \<noteq> y1\<close> equals f2 f3 s_type sets_size_3_plus st_def x_type xy_def y2_type)
               next
                 assume "t \<noteq> y1"
                 show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
                   by (typecheck_cfuncs, metis \<open>t \<noteq> y1\<close> \<open>y \<noteq> y1\<close> equals f1 f2 st_def xy_def)
               qed
             qed
           qed
         next
           assume "y \<noteq> y2"
           show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
           proof(cases "s = x", auto)
             show "s = x \<Longrightarrow> \<langle>x,y\<rangle> = \<langle>x,t\<rangle>"
               by (metis equals2 f1 t_type x_type y_type)
             show "s \<noteq> x \<Longrightarrow> \<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
               by (metis \<open>y \<noteq> y1\<close> \<open>y \<noteq> y2\<close> equals f1 f2 f3 s_type st_def t_type x_type xy_def y_type)
           qed
         qed
       qed
     then show "xy = st"
       by (typecheck_cfuncs, simp add:  st_def xy_def)
   qed
      then show ?thesis
        using \<Theta>_type injective_imp_monomorphism is_smaller_than_def by blast
    qed
  qed  
 qed
qed



  


lemma prod_finite_with_self_finite:
  assumes "is_finite(Y)"
  shows "is_finite(Y \<times>\<^sub>c Y)"
proof(cases "initial_object(Y)")
  assume "initial_object Y"
  then have "Y \<times>\<^sub>c Y \<cong> Y"
    using function_to_empty_set_is_iso initial_iso_empty is_isomorphic_def left_cart_proj_type no_el_iff_iso_0 by blast
  then show ?thesis
    using assms iso_pres_finite isomorphic_is_symmetric by blast
next
  assume "\<not> initial_object Y"
  show ?thesis
  proof(cases "terminal_object Y")
    assume "terminal_object Y"
    then have "Y \<times>\<^sub>c Y \<cong> Y"
      by (simp add: prod_with_term_obj1)
    then show ?thesis
      using assms iso_pres_finite isomorphic_is_symmetric by blast
  next
    assume "\<not> terminal_object Y"
    oops








lemma product_of_finite_is_finite:
  assumes "is_finite(X)" "is_finite(Y)"
  assumes "nonempty(X)" "nonempty(Y)"
  shows "is_finite(X \<times>\<^sub>c Y)"
proof(cases "initial_object(X)")
  assume "initial_object X"
  then have "X \<times>\<^sub>c Y \<cong> \<emptyset>"
    using assms(3) initial_iso_empty no_el_iff_iso_0 by blast
  then show ?thesis
    using \<open>initial_object X\<close> assms(3) initial_iso_empty no_el_iff_iso_0 by blast
next
  assume "\<not> initial_object X"
  show ?thesis
  proof(cases "terminal_object(X)")
    assume "terminal_object(X)" 
    then have "X \<times>\<^sub>c Y \<cong> Y"
      by (simp add: prod_with_term_obj1) 
    then show ?thesis
      using assms(2) iso_pres_finite isomorphic_is_symmetric by blast
  next
    assume "\<not> terminal_object X"
    show ?thesis
    proof(cases "terminal_object(Y)")
      assume "terminal_object Y"
      then have "X \<times>\<^sub>c Y \<cong> X"
        by (simp add: prod_with_term_obj2)
      then show ?thesis
        using assms(1) iso_pres_finite isomorphic_is_symmetric by blast
    next
      assume "\<not> terminal_object Y"
      then show "is_finite (X \<times>\<^sub>c Y)"
        oops

(*
  fix xy
  assume xy_type: "xy:  X \<times>\<^sub>c Y \<rightarrow> X \<times>\<^sub>c Y"
  assume xy_mono: "monomorphism(xy)"
  obtain m where m_def: "m :  X \<rightarrow> X \<times>\<^sub>c Y \<and> monomorphism(m)"
    using assms(4) is_smaller_than_def smaller_than_product1 by blast
  obtain n where n_def: "n :  Y \<rightarrow> X \<times>\<^sub>c Y \<and> monomorphism(n)"
    using assms(3) is_smaller_than_def smaller_than_product2 by blast
  oops
*)




lemma coprod_finite_with_self_finite:
  assumes "is_finite(Y)"
  assumes "is_finite(Y \<times>\<^sub>c Y)"
  shows "is_finite(Y \<Coprod> Y)"
proof(cases "initial_object Y")
  assume "initial_object Y"
  then show ?thesis
    using  assms coprod_with_init_obj2 either_finite_or_infinite iso_pres_infinite not_finite_and_infinite by blast
next
  assume "\<not> initial_object Y"
  show ?thesis
  proof(cases "terminal_object Y")
    assume "terminal_object Y"
    then have "Y \<Coprod> Y \<cong> \<Omega>"
      by (meson coprod_pres_iso isomorphic_is_transitive oneUone_iso_\<Omega> one_terminal_object terminal_objects_isomorphic)
    then show ?thesis
      using either_finite_or_infinite iso_pres_infinite not_finite_and_infinite truth_set_is_finite by blast
  next
    assume "\<not> terminal_object Y"
    then have "(Y \<Coprod> Y) \<le>\<^sub>c (Y \<times>\<^sub>c Y)"
      by (simp add: \<open>\<not> initial_object Y\<close> coprod_leq_product)
    then show ?thesis
      using assms(2) smaller_than_finite_is_finite by blast
  qed
qed
 


lemma coproduct_of_finite_is_finite:
  assumes "is_finite(X)" "is_finite(Y)"
  assumes "is_finite(X \<times>\<^sub>c Y)"
  shows "is_finite(X \<Coprod> Y)"
proof(cases "initial_object(X)")
  assume "initial_object X"
  then have "X \<Coprod> Y \<cong> Y"
    by (simp add: coprod_with_init_obj2)
  then show ?thesis
    using  assms(2) iso_pres_finite isomorphic_is_symmetric by blast
next
  assume "\<not>(initial_object X)"
  show ?thesis
  proof(cases "initial_object(Y)")
    assume "initial_object Y"
    then have "X \<Coprod> Y \<cong> X"
      using coprod_with_init_obj1 by blast
    then show ?thesis
      using assms(1) iso_pres_finite isomorphic_is_symmetric by blast
  next 
    assume "\<not>(initial_object Y)"  
    show ?thesis
    proof(cases "terminal_object(X)")
      assume "terminal_object X"
      then obtain y where y_def:  "y : X \<rightarrow> Y \<and> monomorphism(y)"
        by (meson \<open>\<not> initial_object Y\<close> comp_type iso_empty_initial no_el_iff_iso_0 nonempty_def terminal_el__monomorphism terminal_func_type)
      then have y_id_type: "(y \<bowtie>\<^sub>f  id(Y)) : X \<Coprod> Y \<rightarrow> Y \<Coprod> Y"
        by (simp add: cfunc_bowtie_prod_type id_type)
      then have "monomorphism(y \<bowtie>\<^sub>f  id(Y))"
        by (typecheck_cfuncs, metis cfunc_bowtieprod_inj id_isomorphism injective_imp_monomorphism iso_imp_epi_and_monic mem_Collect_eq monomorphism_imp_injective y_def)
      have "is_finite(Y \<Coprod> Y)"
        by (simp add: assms(4))
      have "(X \<Coprod> Y) \<le>\<^sub>c (Y \<Coprod> Y)"
        using \<open>monomorphism (y \<bowtie>\<^sub>f id\<^sub>c Y)\<close> is_smaller_than_def y_id_type by auto
      then show ?thesis
        using assms(4) smaller_than_finite_is_finite by blast
    next
      assume "\<not>(terminal_object X)"
      show ?thesis 
      proof(cases "terminal_object(Y)")
        assume "terminal_object(Y)"
        then obtain x where x_def:  "x : Y \<rightarrow> X \<and> monomorphism(x)"
          by (meson \<open>\<not> initial_object X\<close> comp_type is_isomorphic_def iso_empty_initial no_el_iff_iso_0 nonempty_def one_terminal_object terminal_el__monomorphism terminal_objects_isomorphic)
      then have y_id_type: "(id(X) \<bowtie>\<^sub>f  x) : X \<Coprod> Y \<rightarrow> X \<Coprod> X"
        by (simp add: cfunc_bowtie_prod_type id_type)
      then have "monomorphism(id(X) \<bowtie>\<^sub>f  x)"
        by (typecheck_cfuncs, metis cfunc_bowtieprod_inj id_isomorphism injective_imp_monomorphism iso_imp_epi_and_monic mem_Collect_eq monomorphism_imp_injective x_def)
      have "is_finite(X \<Coprod> X)"
        by (simp add: assms(3))
      have "(X \<Coprod> Y) \<le>\<^sub>c (X \<Coprod> X)"
        using \<open>monomorphism (id\<^sub>c X \<bowtie>\<^sub>f x)\<close> is_smaller_than_def y_id_type by auto
      then show ?thesis
        using assms(3) smaller_than_finite_is_finite by blast
    next 
      assume "\<not> terminal_object Y"
      then have "(X \<Coprod> Y) \<le>\<^sub>c (X \<times>\<^sub>c Y)"
        by (simp add: \<open>\<not> initial_object X\<close> \<open>\<not> initial_object Y\<close> \<open>\<not> terminal_object X\<close> coprod_leq_product)
      then show "is_finite(X \<Coprod> Y)"
        using assms(5) smaller_than_finite_is_finite by blast
      qed
    qed
  qed
qed


(*
definition triangle_number :: "cfunc" where
  "triangle_number = (THE u. u: \<nat>\<^sub>c \<rightarrow>  \<nat>\<^sub>c \<and> 
     u \<circ>\<^sub>c zero = zero \<and>
     ( u \<circ>\<^sub>c successor \<circ>\<^sub>c n = (u \<circ>\<^sub>c n) +\<^sub>\<nat> n))"





lemma triangle_numbers_exist:
  "\<exists> f. f : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<and> f \<circ>\<^sub>c zero = zero \<and> f \<circ>\<^sub>c successor \<circ>\<^sub>c n = (f \<circ>\<^sub>c n) +\<^sub>\<nat> n"
proof- 
  obtain f where f_def: "n \<in>\<^sub>c \<nat>\<^sub>c  \<Longrightarrow> f : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<and> f \<circ>\<^sub>c zero = zero \<and> f \<circ>\<^sub>c successor \<circ>\<^sub>c n = (f \<circ>\<^sub>c n) +\<^sub>\<nat> n"
    by (typecheck_cfuncs, metis halve_mono halve_nth_even halve_nth_odd halve_type monomorphism_def2 nth_even_def2 nth_odd_def2 zero_is_not_successor)
  then show ?thesis
    by (metis halve_mono halve_nth_even halve_nth_odd halve_type monomorphism_def3 nth_even_def2 nth_odd_def2 zero_is_not_successor zero_type)
qed

*)


(*
(*Proposition 2.6.10*)
lemma NxN_is_countable:
  "countable(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
*)


(*
  obtain f where f_def:
    "f = ((\<langle>id \<nat>\<^sub>c, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c right_cart_proj one \<nat>\<^sub>c) \<amalg> id (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c))
          \<circ>\<^sub>c dist_prod_coprod_inv2 one \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (predecessor \<times>\<^sub>f successor)"
    by auto

  have f_type[type_rule]: "f : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
    unfolding f_def by typecheck_cfuncs

  obtain seq where seq_type[type_rule]: "seq : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c" and
    seq_triangle: "seq \<circ>\<^sub>c zero = \<langle>zero, zero\<rangle>" and
    seq_square: "seq \<circ>\<^sub>c successor = f \<circ>\<^sub>c seq"
    using natural_number_object_property[where q = "\<langle>zero, zero\<rangle>", where f=f, where X="\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"]
    unfolding triangle_commutes_def square_commutes_def by (auto, typecheck_cfuncs, metis)

  (* seq((n+m)(n+m+1)/2 + n) = (m, n)? *)
  (* seq(0) = (0,0) = seq(0*1/2 + 0) *)
  (* seq(1) = (1,0) = seq(1*2/2 + 0) *)
  (* seq(2) = (0,1) = seq(1*2/2 + 1) *)
  (* seq(3) = (2,0) = seq(2*3/2 + 0) *)
  (* seq(4) = (1,1) = seq(2*3/2 + 1) *)
  (* seq(5) = (0,2) = seq(2*3/2 + 2) *)
  (* seq(6) = (3,0) = seq(3*4/2 + 0) *)

  have "\<And> m n k. m \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> k \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow>
    seq \<circ>\<^sub>c k = \<langle>m, n\<rangle> \<longleftrightarrow> seq \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>k, m\<rangle> = \<langle>zero, add2 \<circ>\<^sub>c \<langle>m, n\<rangle>\<rangle>"
    

    have "\<And> n. n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> seq \<circ>\<^sub>c halve \<circ>\<^sub>c (n \<cdot>\<^sub>\<nat> (successor \<circ>\<^sub>c n)) = \<langle>n, zero\<rangle>"
  proof -
    fix n
    assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"

    have "seq \<circ>\<^sub>c halve \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, successor\<rangle> = \<langle>id \<nat>\<^sub>c, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
    proof (rule natural_number_object_func_unique[where X="\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c", where f="successor \<times>\<^sub>f id \<nat>\<^sub>c"])
      show "seq \<circ>\<^sub>c halve \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,successor\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
        by typecheck_cfuncs
      show "\<langle>id\<^sub>c \<nat>\<^sub>c,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
        by typecheck_cfuncs
      show "successor \<times>\<^sub>f id \<nat>\<^sub>c : \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
        by typecheck_cfuncs

      show "(seq \<circ>\<^sub>c halve \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,successor\<rangle>) \<circ>\<^sub>c zero = \<langle>id\<^sub>c \<nat>\<^sub>c,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c zero"
      proof -
        have "(seq \<circ>\<^sub>c halve \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,successor\<rangle>) \<circ>\<^sub>c zero = seq \<circ>\<^sub>c halve \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>zero, successor \<circ>\<^sub>c zero\<rangle>"
          by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 id_left_unit2)
        also have "... = seq \<circ>\<^sub>c halve \<circ>\<^sub>c zero"
          using mult_def s0_is_right_id zero_type by auto
        also have "... = seq \<circ>\<^sub>c zero"
          by (smt comp_associative2 halve_nth_even halve_type id_left_unit2 nth_even_def2 zero_type)
        also have "... = \<langle>zero, zero\<rangle>"
          by (simp add: seq_triangle)
        also have "... = \<langle>id\<^sub>c \<nat>\<^sub>c,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c zero"
          by (typecheck_cfuncs, simp add: cart_prod_extract_left)
        then show ?thesis
          using calculation by auto
      qed

      show "(seq \<circ>\<^sub>c halve \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,successor\<rangle>) \<circ>\<^sub>c successor
        = (successor \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c seq \<circ>\<^sub>c halve \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,successor\<rangle>"
      proof -
        have "(seq \<circ>\<^sub>c halve \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,successor\<rangle>) \<circ>\<^sub>c successor = seq \<circ>\<^sub>c halve \<circ>\<^sub>c mult2 \<circ>\<^sub>c \<langle>successor, successor \<circ>\<^sub>c successor\<rangle>"
          by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 id_left_unit2)
        also have "... = undefined"

(*  have "\<And> m. seq \<circ>\<^sub>c (k +\<^sub>\<nat> m) = \<langle>zero, m\<rangle>"

  have "\<And> k m. k \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> seq \<circ>\<^sub>c k = \<langle>m, zero\<rangle> \<Longrightarrow> seq \<circ>\<^sub>c (k +\<^sub>\<nat> m) = \<langle>zero, m\<rangle>"
  proof -
    fix k m
    assume k_type[type_rule]: "k \<in>\<^sub>c \<nat>\<^sub>c"
    assume seq_k_eq: "seq \<circ>\<^sub>c k = \<langle>m, zero\<rangle>"

    have "eq_pred (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>seq \<circ>\<^sub>c k \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, \<langle>id \<nat>\<^sub>c, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>\<rangle> =
      eq_pred (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>seq\<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>k \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>, \<langle>zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<rangle>"
    proof (rule natural_number_object_func_unique[where X="\<Omega>", where f="id \<Omega>"])
*)
  oops

*)



(*Once we have this  result above we can generalize it to any countable sets*)
lemma product_of_countables_is_countable:
  assumes "countable X" "countable Y"
  assumes NxN_is_countable: "countable(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)" (*DELETE later*)
  shows "countable(X \<times>\<^sub>c Y)"
proof - 
  have "\<exists>f. f: X \<rightarrow> \<nat>\<^sub>c \<and> monomorphism(f)"
    using assms(1) countable_def by blast
  then obtain f where f_def: "f: X \<rightarrow> \<nat>\<^sub>c \<and> monomorphism(f)"
    by blast
  have "\<exists>g. g: Y \<rightarrow> \<nat>\<^sub>c \<and> monomorphism(g)"
    using assms(2) countable_def by blast
  then obtain g where g_def: "g: Y \<rightarrow> \<nat>\<^sub>c \<and> monomorphism(g)"
    by blast
  then have fg_type: "(f \<times>\<^sub>f g) : (X \<times>\<^sub>c Y) \<rightarrow> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c)"
    by (simp add: cfunc_cross_prod_type f_def)
  have fg_mono: "monomorphism(f \<times>\<^sub>f g)"
    using cfunc_cross_prod_mono f_def g_def by blast
  obtain \<phi> where \<phi>_def: "(\<phi> : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c) \<rightarrow> \<nat>\<^sub>c) \<and> monomorphism(\<phi>)"
    using NxN_is_countable countable_def by blast
  have "(\<phi> \<circ>\<^sub>c (f \<times>\<^sub>f g) : (X \<times>\<^sub>c Y) \<rightarrow> \<nat>\<^sub>c) \<and> monomorphism(\<phi> \<circ>\<^sub>c (f \<times>\<^sub>f g))"
    using \<phi>_def cfunc_type_def comp_type composition_of_monic_pair_is_monic fg_mono fg_type by auto
  then show "countable(X \<times>\<^sub>c Y)"
    using countable_def by blast
qed

      


lemma NuN_is_countable:
  "countable(\<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c)"
  using countable_def epis_give_monos halve_with_parity_iso halve_with_parity_type iso_imp_epi_and_monic by smt


(*Exercise 2.6.11*)
lemma coproduct_of_countables_is_countable:
  assumes "countable X" "countable Y"
  shows "countable(X \<Coprod> Y)"
  unfolding countable_def
proof-
  obtain x where x_def:  "x : X  \<rightarrow> \<nat>\<^sub>c \<and> monomorphism x"
    using assms(1) countable_def by blast
  obtain y where y_def:  "y : Y  \<rightarrow> \<nat>\<^sub>c \<and> monomorphism y"
    using assms(2) countable_def by blast
  obtain n where n_def: " n : \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<and> monomorphism n"
    using NuN_is_countable countable_def by blast
  have xy_type: "x \<bowtie>\<^sub>f y : X \<Coprod> Y \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c"
    using x_def y_def by (typecheck_cfuncs, auto)
  then have nxy_type: "n \<circ>\<^sub>c (x \<bowtie>\<^sub>f y) : X \<Coprod> Y \<rightarrow> \<nat>\<^sub>c"
    using comp_type n_def by blast
  have "injective(x \<bowtie>\<^sub>f y)"
    using cfunc_bowtieprod_inj monomorphism_imp_injective x_def y_def by blast
  then have "monomorphism(x \<bowtie>\<^sub>f y)"
    using injective_imp_monomorphism by auto
  then have "monomorphism(n \<circ>\<^sub>c (x \<bowtie>\<^sub>f y))"
    using cfunc_type_def composition_of_monic_pair_is_monic n_def xy_type by auto
  then show "\<exists>f. f : X \<Coprod> Y \<rightarrow> \<nat>\<^sub>c \<and> monomorphism f"
    using nxy_type by blast
qed
   
  
(*This is not ETCS?*)
lemma Maybe_Not_ETCS:
  assumes i_zero: "i 0 = x" and i_suc: "\<And> n. i (Suc n) = (m \<circ> i) n" 
  assumes m_mono: "\<And> p q. m p = m q \<Longrightarrow> p = q"
  assumes x_def: "\<And> y. m y \<noteq> x"
  shows "\<And>q. i p = i q \<Longrightarrow> p = q"
proof (induct p)
  fix q
  show "i 0 = i q \<Longrightarrow> 0 = q"
  proof (induct q)
    show "0 = 0"
      by simp
  next
    fix q
    assume "i 0 = i (Suc q)"
    then have "x = (m \<circ> i) q"
      using i_suc i_zero by auto
    then have False
      using x_def by auto
    then show "0 = Suc q"
      by simp
  qed
next
  fix p q
  assume ind_hyp: "\<And>q. i p = i q \<Longrightarrow> p = q"

  show "i (Suc p) = i q \<Longrightarrow> Suc p = q"
  proof (induct q)
    assume "i (Suc p) = i 0"
    then have "x = (m \<circ> i) p"
      using i_suc i_zero by auto
    then have False
      using x_def by auto
    then show "Suc p = 0"
      by simp
  next
    fix q
    assume "i (Suc p) = i (Suc q)"
    then have "(m \<circ> i) p = (m \<circ> i) q"
      by (simp add: i_suc)
    then have "i p = i q"
      by (metis comp_apply m_mono)
    then have "p = q"
      by (meson ind_hyp)
    then show "Suc p = Suc q"
      by simp
  qed
qed

(*Is the above really just Herrlich?*)
(*restate with \<nexists> symbol*)
lemma finite_iff_nosurj_to_N:
  shows "(is_finite(X)) = (\<not>(\<exists>s. (s : X \<rightarrow> \<nat>\<^sub>c) \<and> surjective(s)))"
proof(safe)
  fix s 
  assume X_fin: "is_finite X"
  assume s_type: "s : X \<rightarrow> \<nat>\<^sub>c"
  assume s_surj: "surjective s"
  have "\<exists>g. (g: \<nat>\<^sub>c \<rightarrow> X \<and> monomorphism(g) )"
    using epis_give_monos s_surj s_type surjective_is_epimorphism by blast
  then have "is_finite \<nat>\<^sub>c"
    using X_fin is_smaller_than_def smaller_than_finite_is_finite by blast
  then show False
    using natural_numbers_are_countably_infinite not_finite_and_infinite by blast
next 
  assume "\<nexists>s. s : X \<rightarrow> \<nat>\<^sub>c \<and> surjective s"
  show "is_finite X"
  proof(rule ccontr)
    assume "\<not> is_finite X"
    then have "is_infinite X"
      using either_finite_or_infinite by blast
    then obtain m where m_type[type_rule]: "m : X \<rightarrow> X" and  m_mono: "monomorphism(m)" and 
     m_not_surj:  "\<not>surjective(m)"
      using is_infinite_def by blast
    obtain x where x_type[type_rule]: "x \<in>\<^sub>c X" and 
      x_def: "\<And> y.  y \<in>\<^sub>c X \<Longrightarrow>  m \<circ>\<^sub>c y \<noteq> x"
      using m_not_surj m_type surjective_def2 by auto

    obtain i where 
      i_type[type_rule]: "i : \<nat>\<^sub>c \<rightarrow> X" and ibase: "i \<circ>\<^sub>c zero = x" and i_induct: "m \<circ>\<^sub>c i = i \<circ>\<^sub>c successor"
      using m_type natural_number_object_property2 x_type by blast
    have "injective(i)"
      unfolding injective_def
    proof(auto)
      fix p q
      assume "p \<in>\<^sub>c domain i"
      then have [type_rule]: "p \<in>\<^sub>c \<nat>\<^sub>c"
        using cfunc_type_def i_type by auto
      assume "q \<in>\<^sub>c domain i"
      then have [type_rule]: "q \<in>\<^sub>c \<nat>\<^sub>c"
        using cfunc_type_def i_type by auto
      assume eqs: "i \<circ>\<^sub>c p = i \<circ>\<^sub>c q"  
  
      have main_result: "FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle> eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i), eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f id \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
      proof (rule natural_number_object_func_unique[where X="\<Omega>", where f="id \<Omega>"])
  
        show "FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
          by typecheck_cfuncs
        show "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
          by typecheck_cfuncs
        show "id\<^sub>c \<Omega> : \<Omega> \<rightarrow> \<Omega>"
          by typecheck_cfuncs
        show  zero_case: "(FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c zero = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero"
        proof - 
          have "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero =  (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<times>\<^sub>c one\<^esub>)\<^sup>\<sharp>"
          proof (rule same_evals_equal[where Z=one, where X=\<Omega>, where A="\<nat>\<^sub>c"])
            show "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero \<in>\<^sub>c \<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>"
              by typecheck_cfuncs
            show "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp> \<in>\<^sub>c \<Omega>\<^bsup>\<nat>\<^sub>c\<^esup>"
              by typecheck_cfuncs 
            show "eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero =
      eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp>"
            proof - 
              have "eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero = 
                    eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero)"
                by (typecheck_cfuncs, metis identity_distributes_across_composition)
              also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero)"
                by (typecheck_cfuncs, simp add: cfunc_type_def comp_associative transpose_func_def)
              also have "... = eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp>"
              proof(rule one_separator[where X = "\<nat>\<^sub>c \<times>\<^sub>c one", where Y=\<Omega>])
                show "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero : \<nat>\<^sub>c \<times>\<^sub>c one \<rightarrow> \<Omega>"
                  by typecheck_cfuncs
                show " eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp> : \<nat>\<^sub>c \<times>\<^sub>c one \<rightarrow> \<Omega>"
                  by typecheck_cfuncs
                show "\<And>pone. pone \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c one \<Longrightarrow>
           (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero) \<circ>\<^sub>c pone =
           (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp>) \<circ>\<^sub>c pone"
                proof - 
                  fix pone
                  assume pone_type: "pone \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c one"
                  then obtain p where p_def: "pone = \<langle>p, id one\<rangle>" and p_type[type_rule]: "p \<in>\<^sub>c \<nat>\<^sub>c"
                    by (metis cart_prod_decomp id_type one_unique_element)
  
                  have RHS: "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp>) \<circ>\<^sub>c pone = \<t>"
                  proof - 
                    have "(eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp>) \<circ>\<^sub>c pone = 
                           eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp>) \<circ>\<^sub>c \<langle>p, id one\<rangle>"
                      by (typecheck_cfuncs, simp add: comp_associative2 p_def)
                    also have "... = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>) \<circ>\<^sub>c \<langle>p, id one\<rangle>"
                      by (typecheck_cfuncs, metis calculation flat_cancels_sharp inv_transpose_func_def2 p_def) 
                    also have "... = \<t>"
                      by (typecheck_cfuncs, smt (z3) comp_associative2 id_right_unit2 terminal_func_comp terminal_func_unique)
                    then show ?thesis
                      by (simp add: calculation)
                  qed
                  
                  have LHS: "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero) \<circ>\<^sub>c pone = \<t>"
                  proof - 
                    have "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero) \<circ>\<^sub>c pone = 
                           IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero) \<circ>\<^sub>c \<langle>p, id one\<rangle>"
                      using comp_associative2 p_def by (typecheck_cfuncs, force)
                    also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>p, zero\<rangle>"
                      by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2)
                    also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i) \<circ>\<^sub>c \<langle>p, zero\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>p, zero\<rangle> \<rangle>"
                      using cfunc_prod_comp comp_associative2 by (typecheck_cfuncs, force)
                    also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c   \<langle>i \<circ>\<^sub>c p, i \<circ>\<^sub>c zero\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c p, id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero\<rangle> \<rangle>"
                      by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
                    also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c p, x\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>p, zero\<rangle> \<rangle>"
                      by (typecheck_cfuncs, simp add: ibase id_left_unit2)
                    also have "... = \<t>"
                    proof(cases "p = zero")
                      assume "p = zero"
                      then show "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c p,x\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>p,zero\<rangle>\<rangle> = \<t>"
                        by (typecheck_cfuncs, metis IMPLIES_true_true_is_true  eq_pred_iff_eq ibase)
                    next
                      assume "p \<noteq> zero"
                      then obtain j where j_def: "p = successor \<circ>\<^sub>c j" and j_type[type_rule]: "j \<in>\<^sub>c \<nat>\<^sub>c"
                        using \<open>p \<noteq> zero\<close> nonzero_is_succ by (typecheck_cfuncs, blast)
                      have "i \<circ>\<^sub>c p = m \<circ>\<^sub>c i \<circ>\<^sub>c j"
                        using comp_associative2 i_induct j_def successor_type by (typecheck_cfuncs, force)
                      then have "i \<circ>\<^sub>c p \<noteq> x"
                        using \<open>i \<circ>\<^sub>c p = m \<circ>\<^sub>c i \<circ>\<^sub>c j\<close> comp_type j_type x_def by (typecheck_cfuncs, presburger)
                      then have "eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c p, x\<rangle> = \<f>"
                        using \<open>i \<circ>\<^sub>c p \<noteq> x\<close> eq_pred_iff_eq_conv by (typecheck_cfuncs, blast)
                      then show "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c p,x\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>p,zero\<rangle>\<rangle> = \<t>"
                        by (typecheck_cfuncs, metis IMPLIES_false_false_is_true \<open>eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c p,x\<rangle> = \<f>\<close> \<open>p \<noteq> zero\<close> eq_pred_iff_eq_conv)
                    qed
                    then show ?thesis
                      by (simp add: calculation)
                  qed
                  show "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero) \<circ>\<^sub>c pone =
                                    (eval_func \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp>) \<circ>\<^sub>c pone "
                    by (simp add: LHS RHS)
                qed
              qed
              then show ?thesis
                using calculation by presburger
            qed
          qed
          then show ?thesis  
                by (typecheck_cfuncs, metis FORALL_is_pullback \<open>(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>)\<^sup>\<sharp>\<close> cfunc_type_def comp_associative is_pullback_def square_commutes_def terminal_func_comp)
        qed
        
  
  
  
  
        show "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor = id\<^sub>c \<Omega> \<circ>\<^sub>c \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
          by (typecheck_cfuncs, smt (z3) comp_associative2 id_left_unit2 terminal_func_comp)
  
        show "(FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor
          = id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>"
        proof (rule one_separator[where X="\<nat>\<^sub>c", where Y=\<Omega>])
          show "(FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<Omega>"
            by typecheck_cfuncs
          show "id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
            by typecheck_cfuncs
        next
          fix p
          assume p_type[type_rule]: "p \<in>\<^sub>c \<nat>\<^sub>c"
  
          have case1: "((FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor) \<circ>\<^sub>c p = \<t>
            \<Longrightarrow> (id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c p = \<t>"
          proof - 
            assume "((FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor) \<circ>\<^sub>c p = \<t>"
            then have "(FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c (successor \<circ>\<^sub>c p) = \<t>"
              using  comp_associative2 by (typecheck_cfuncs, force)
            then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c (successor \<circ>\<^sub>c p) = \<t>"
              by (typecheck_cfuncs, smt (z3) cfunc_type_def codomain_comp comp_associative)
            then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c ((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f (successor \<circ>\<^sub>c p)))\<^sup>\<sharp> = \<t>"
              by (typecheck_cfuncs, metis sharp_comp)
            then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c ((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, (successor \<circ>\<^sub>c p) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>"
              by (typecheck_cfuncs, metis cfunc_cross_prod_right_terminal_decomp)
            then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c ((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, (successor \<circ>\<^sub>c p) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>"
            proof -
              have "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, (successor \<circ>\<^sub>c p) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one
                  = (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, (successor \<circ>\<^sub>c p) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one"
                by (typecheck_cfuncs, simp add: comp_associative2)
              then show "FORALL \<nat>\<^sub>c \<circ>\<^sub>c ((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, (successor \<circ>\<^sub>c p) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>
                \<Longrightarrow> FORALL \<nat>\<^sub>c \<circ>\<^sub>c ((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, (successor \<circ>\<^sub>c p) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>"
                using p_type by force
            qed
            then have "(\<And>q. q \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, (successor \<circ>\<^sub>c p) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c q = \<t>)"
            proof (rule_tac FORALL_true_implies_all_true[where X="\<nat>\<^sub>c"], auto)
              show "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,(successor \<circ>\<^sub>c p) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
                by (typecheck_cfuncs)
            qed
            then have f1: "\<And> q. q \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, (successor \<circ>\<^sub>c p) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c q = \<t>"
              by auto
            have ind_hyp: "\<And> q. q \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (i \<circ>\<^sub>c q  =  i \<circ>\<^sub>c (successor \<circ>\<^sub>c p)) \<Longrightarrow> (q = (successor \<circ>\<^sub>c p))"    
            proof - 
              fix q
              assume q_type[type_rule]: "q \<in>\<^sub>c \<nat>\<^sub>c"
              have "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, (successor \<circ>\<^sub>c p) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c q = \<t>"
                using f1 by (typecheck_cfuncs, blast)
              then have "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, (successor \<circ>\<^sub>c p) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c q = \<t>"
                using  comp_associative2 by (typecheck_cfuncs, force)
              then have "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c \<langle>q, (successor \<circ>\<^sub>c p)\<rangle>  = \<t>"
                by (typecheck_cfuncs, metis cart_prod_extract_left)
              then have "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>q, (successor \<circ>\<^sub>c p)\<rangle>  = \<t>"
                using  comp_associative2 by (typecheck_cfuncs, force)
              then have "IMPLIES \<circ>\<^sub>c \<langle>(eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i)) \<circ>\<^sub>c \<langle>q, (successor \<circ>\<^sub>c p)\<rangle>, (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>q, (successor \<circ>\<^sub>c p)\<rangle> \<rangle>   = \<t>"
                by (typecheck_cfuncs, metis cfunc_prod_comp)
              then have "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i) \<circ>\<^sub>c \<langle>q, (successor \<circ>\<^sub>c p)\<rangle>,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>q, (successor \<circ>\<^sub>c p)\<rangle>\<rangle>   = \<t>"
                by (typecheck_cfuncs, smt (verit, ccfv_threshold)  cfunc_type_def comp_associative domain_comp)
              then have "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c q, i \<circ>\<^sub>c (successor \<circ>\<^sub>c p)\<rangle>, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>q, (successor \<circ>\<^sub>c p)\<rangle>\<rangle> = \<t>"
                using cfunc_cross_prod_comp_cfunc_prod id_cross_prod id_left_unit2 by (typecheck_cfuncs, force)
              then have "(eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c q, i \<circ>\<^sub>c (successor \<circ>\<^sub>c p)\<rangle> = \<t>) \<Longrightarrow> (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>q, (successor \<circ>\<^sub>c p)\<rangle> = \<t>)  "
                by (typecheck_cfuncs, metis IMPLIES_true_false_is_false \<open>IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c q,i \<circ>\<^sub>c successor \<circ>\<^sub>c p\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>q,successor \<circ>\<^sub>c p\<rangle>\<rangle> = \<t>\<close> true_false_only_truth_values)
              then show "(i \<circ>\<^sub>c q  =  i \<circ>\<^sub>c (successor \<circ>\<^sub>c p)) \<Longrightarrow> (q = (successor \<circ>\<^sub>c p))"
                using  eq_pred_iff_eq by (typecheck_cfuncs, auto)
            qed
            have "\<And>q. q \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i), eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f id \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,p \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c q = \<t>"
            proof -
              fix q
              assume q_type[type_rule]: "q \<in>\<^sub>c \<nat>\<^sub>c"
              have "i \<circ>\<^sub>c q = i \<circ>\<^sub>c p \<Longrightarrow> q = p"
              proof -
                assume "i \<circ>\<^sub>c q = i \<circ>\<^sub>c p"
                then have "m \<circ>\<^sub>c i \<circ>\<^sub>c q = m \<circ>\<^sub>c i \<circ>\<^sub>c p"
                  by auto
                then have "i \<circ>\<^sub>c successor \<circ>\<^sub>c q = i \<circ>\<^sub>c successor \<circ>\<^sub>c p"
                  using comp_associative2 i_induct i_type m_type p_type q_type successor_type by auto
                then have "successor \<circ>\<^sub>c q = successor \<circ>\<^sub>c p"
                  by (simp add: ind_hyp q_type succ_n_type)
                then show "q = p"
                  by (simp add: p_type q_type succ_inject)
              qed
              then have "eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c q, i \<circ>\<^sub>c p\<rangle> = \<t> \<Longrightarrow> eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>q, p\<rangle> = \<t>"
                using  eq_pred_iff_eq by (typecheck_cfuncs, blast)
              then have "eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i) \<circ>\<^sub>c \<langle>q, p\<rangle> = \<t> \<Longrightarrow> eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f id \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>q, p\<rangle> = \<t>"
                by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
              then have "(eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i)) \<circ>\<^sub>c \<langle>q, p\<rangle> = \<t> \<Longrightarrow> (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f id \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>q, p\<rangle> = \<t>"
                using comp_associative2 by (typecheck_cfuncs, auto)
              then have "IMPLIES \<circ>\<^sub>c \<langle>(eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i)) \<circ>\<^sub>c \<langle>q, p\<rangle>, (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f id \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>q, p\<rangle>\<rangle> = \<t>"
                by (typecheck_cfuncs, metis IMPLIES_false_is_true_false true_false_only_truth_values)
              then have "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i), eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f id \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c \<langle>q, p\<rangle>  = \<t>"
                by (typecheck_cfuncs, simp add: cfunc_prod_comp)
              then have "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i), eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f id \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c (\<langle>id\<^sub>c \<nat>\<^sub>c,p \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c q) = \<t>"
                by (typecheck_cfuncs, metis cart_prod_extract_left)
              then show "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i), eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f id \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,p \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c q = \<t>"
                using comp_associative2 by (typecheck_cfuncs, auto)
            qed
            then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c ((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i), eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f id \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,p \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>"
              using all_true_implies_FORALL_true by (typecheck_cfuncs, blast)
            then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i), eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f id \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c (\<langle>id\<^sub>c \<nat>\<^sub>c,p \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one))\<^sup>\<sharp> = \<t>"
              by (typecheck_cfuncs, smt (z3) cfunc_type_def comp_associative domain_comp)
            then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c ((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i), eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f id \<nat>\<^sub>c)\<rangle>) \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f p))\<^sup>\<sharp> = \<t>"
              by (typecheck_cfuncs, metis cfunc_cross_prod_right_terminal_decomp cfunc_type_def comp_associative domain_comp)
            then have "(FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c p = \<t>"
              by (typecheck_cfuncs, smt (z3) sharp_comp comp_associative2)
            then show "(id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c p = \<t>"
              by (typecheck_cfuncs, smt id_left_unit2)
              
          qed
  
          have case2: "(id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c p = \<t>
              \<Longrightarrow> ((FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor) \<circ>\<^sub>c p = \<t>"
          proof -
            assume "(id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c p = \<t>"
            then have "(FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c p = \<t>"
              by (typecheck_cfuncs_prems, insert id_left_unit2, presburger)
            then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c ((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c p) = \<t>"
              by (typecheck_cfuncs, simp add: comp_associative2)
            then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c ((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f p))\<^sup>\<sharp> = \<t>"
              by (typecheck_cfuncs, metis sharp_comp)
            then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c ((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, p \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>"
              by (typecheck_cfuncs, metis cfunc_cross_prod_right_terminal_decomp)
            then have "\<And>q. q \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, p \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c q = \<t>"
            proof -
              assume "FORALL \<nat>\<^sub>c \<circ>\<^sub>c ((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,p \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>"
              then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c ((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,p \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>"
                using p_type by auto
              then show "\<And>q. q \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, p \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c q = \<t>"
                by (rule_tac FORALL_true_implies_all_true[where X="\<nat>\<^sub>c"], auto, 
                    typecheck_cfuncs, typecheck_cfuncs, smt comp_associative2)
            qed
            then have f1: "\<And> q. q \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, p \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c q = \<t>"
              by auto
            have ind_hyp: "\<And> q. q \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (i \<circ>\<^sub>c q  =  i \<circ>\<^sub>c p) \<Longrightarrow> (q = p)"
            proof - 
              fix q
              assume q_type[type_rule]: "q \<in>\<^sub>c \<nat>\<^sub>c"
              have "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, p \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c q = \<t>"
                by (simp add: f1  p_type q_type)
              then have "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, p \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c q = \<t>"
                using  comp_associative2 by (typecheck_cfuncs, force)
              then have "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c \<langle>q, p\<rangle>  = \<t>"
                by (typecheck_cfuncs, metis cart_prod_extract_left)
              then have "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>q, p\<rangle>  = \<t>"
                using  comp_associative2 by (typecheck_cfuncs, force)
              then have "IMPLIES \<circ>\<^sub>c \<langle>(eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i)) \<circ>\<^sub>c \<langle>q, p\<rangle>, (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c)) \<circ>\<^sub>c \<langle>q, p\<rangle>\<rangle>   = \<t>"
                by (typecheck_cfuncs, metis cfunc_prod_comp)
              then have "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i) \<circ>\<^sub>c \<langle>q, p\<rangle>, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>q, p\<rangle> \<rangle>   = \<t>"
                by (typecheck_cfuncs, smt (verit, ccfv_threshold) cfunc_type_def comp_associative domain_comp)
              then have "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c  \<langle>i \<circ>\<^sub>c q, i \<circ>\<^sub>c p\<rangle>, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>q, p\<rangle>\<rangle>   = \<t>"
                using cfunc_cross_prod_comp_cfunc_prod id_cross_prod id_left_unit2 by (typecheck_cfuncs, force)            
              then have "(eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c q, i \<circ>\<^sub>c p\<rangle> = \<t>) \<Longrightarrow> (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>q, p\<rangle> = \<t>)"
                by (typecheck_cfuncs, metis IMPLIES_true_false_is_false  eq_pred_iff_eq eq_pred_iff_eq_conv)
              then show "(i \<circ>\<^sub>c q  =  i \<circ>\<^sub>c p) \<Longrightarrow>  (q = p)"
                using eq_pred_iff_eq by (typecheck_cfuncs, auto)
            qed
            show "((FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor) \<circ>\<^sub>c p = \<t>"
            proof - 
              have  "\<And> q. q \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, (successor \<circ>\<^sub>c p) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c q = \<t>"
              proof  -
                fix q 
                assume q_type[type_rule]: "q \<in>\<^sub>c \<nat>\<^sub>c"
                have "i \<circ>\<^sub>c q = i \<circ>\<^sub>c (successor \<circ>\<^sub>c p) \<Longrightarrow> q = (successor \<circ>\<^sub>c p)"
                proof -
                  assume iq_eq_isp: "i \<circ>\<^sub>c q = i \<circ>\<^sub>c successor \<circ>\<^sub>c p"
  
                  have "q = zero \<or> (\<exists>r. r \<in>\<^sub>c \<nat>\<^sub>c \<and> q = successor \<circ>\<^sub>c r)"
                    using nonzero_is_succ q_type by blast
                  then show "q = successor \<circ>\<^sub>c p"
                  proof auto
                    assume q_zero: "q = zero"
                    then have "i \<circ>\<^sub>c zero = i \<circ>\<^sub>c successor \<circ>\<^sub>c p"
                      using iq_eq_isp by auto
                    then have "x = m \<circ>\<^sub>c i \<circ>\<^sub>c p"
                      using comp_associative2 i_induct ibase successor_type by (typecheck_cfuncs, auto)
                    then have False
                      using comp_type i_type p_type x_def by blast
                    then show "zero = successor \<circ>\<^sub>c p"
                      by auto
                  next
                    fix r
                    assume r_type[type_rule]: "r \<in>\<^sub>c \<nat>\<^sub>c"
                    assume q_succ: "q = successor \<circ>\<^sub>c r"
                    then have "i \<circ>\<^sub>c successor \<circ>\<^sub>c r = i \<circ>\<^sub>c successor \<circ>\<^sub>c p"
                      using iq_eq_isp by auto
                    then have "m \<circ>\<^sub>c i \<circ>\<^sub>c r = m \<circ>\<^sub>c i \<circ>\<^sub>c p"
                      using comp_associative2 i_induct successor_type by (typecheck_cfuncs, auto)
                    then have "i \<circ>\<^sub>c r = i \<circ>\<^sub>c p"
                      by (metis (mono_tags, lifting) cfunc_type_def codomain_comp i_type m_mono m_type monomorphism_def p_type r_type)
                    then have "r = p"
                      using ind_hyp r_type by blast
                    then show "successor \<circ>\<^sub>c r = successor \<circ>\<^sub>c p"
                      by auto
                  qed
                qed
                then have "(eq_pred X \<circ>\<^sub>c \<langle> i \<circ>\<^sub>c q ,i \<circ>\<^sub>c (successor \<circ>\<^sub>c p)\<rangle> = \<t>) \<Longrightarrow> (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>q , (successor \<circ>\<^sub>c p)\<rangle> = \<t>) "
                  using  eq_pred_iff_eq by (typecheck_cfuncs, blast)
                then have "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle> i \<circ>\<^sub>c q ,i \<circ>\<^sub>c (successor \<circ>\<^sub>c p)\<rangle>, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>q , (successor \<circ>\<^sub>c p)\<rangle> \<rangle> = \<t>"
                  by (typecheck_cfuncs, metis IMPLIES_false_is_true_false  true_false_only_truth_values) 
                then have "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i) \<circ>\<^sub>c \<langle>q ,(successor \<circ>\<^sub>c p)\<rangle>, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>q ,(successor \<circ>\<^sub>c p)\<rangle> \<rangle> = \<t>"
                  using  cfunc_cross_prod_comp_cfunc_prod id_left_unit2 by (typecheck_cfuncs, auto)
                then have "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>q ,(successor \<circ>\<^sub>c p)\<rangle> = \<t>"
                  using  cfunc_prod_comp comp_associative2 by (typecheck_cfuncs, force )
                then have "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,(successor \<circ>\<^sub>c p) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c q = \<t>"
                  by (metis  cart_prod_extract_left p_type q_type succ_n_type)               
                then show "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,(successor \<circ>\<^sub>c p) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c q = \<t>"
                  using  comp_associative2 by (typecheck_cfuncs, force)
              qed
              then have "\<And>q. q \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, (successor \<circ>\<^sub>c p)  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c q = \<t>"
                using  comp_associative2 by (typecheck_cfuncs, auto)
              then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c (((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, (successor \<circ>\<^sub>c p)  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>"
                using  all_true_implies_FORALL_true comp_associative2 by (typecheck_cfuncs, force)
              then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c ((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, (successor \<circ>\<^sub>c p)  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>"
                by (typecheck_cfuncs, simp add:  comp_associative2)
              then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c ((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f (successor \<circ>\<^sub>c p)))\<^sup>\<sharp> = \<t>"
                by (typecheck_cfuncs, metis cfunc_cross_prod_right_terminal_decomp)             
              then have "(FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c (successor \<circ>\<^sub>c p) = \<t>"
                by (typecheck_cfuncs, smt (z3) comp_associative2 sharp_comp)
              then show "((FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor) \<circ>\<^sub>c p = \<t>"
                using  comp_associative2 by (typecheck_cfuncs, auto)
      
            qed
          qed
  
          show "((FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor) \<circ>\<^sub>c p
              = (id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c p"
            by (typecheck_cfuncs, metis case1 case2 true_false_only_truth_values)
        qed
      qed
  
    have "(FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i), eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f id \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<longrightarrow> (p=q)"
    proof(auto) 
      assume "FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i), eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f id \<nat>\<^sub>c)\<rangle>)\<^sup>\<sharp> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
      then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c 
          (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c q = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c q"
        by(typecheck_cfuncs, simp add: comp_associative2)
      then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c
          (IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>  \<circ>\<^sub>c q = \<t>"
        by (typecheck_cfuncs, metis  id_right_unit2 id_type one_unique_element terminal_func_comp terminal_func_type)
      then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c ((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f q))\<^sup>\<sharp> = \<t>"
        by (typecheck_cfuncs, metis sharp_comp)
      then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c
          ((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>) 
              \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, q \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>"
        by (typecheck_cfuncs, metis cfunc_cross_prod_right_terminal_decomp)
      then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c 
          ((IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle>
              \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, q \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t>"
        using cfunc_cross_prod_right_terminal_decomp cfunc_type_def comp_associative domain_comp by (typecheck_cfuncs, fastforce)
      then have "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, q \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c p = \<t>"
        using FORALL_true_implies_all_true  by (typecheck_cfuncs, blast)
      then have "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, q \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c p = \<t>"
        by (typecheck_cfuncs, smt (verit, ccfv_threshold)  cfunc_type_def comp_associative domain_comp)
      then have "IMPLIES \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c i \<times>\<^sub>f i, eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>p, q\<rangle> = \<t>"
        by (typecheck_cfuncs, metis cart_prod_extract_left)
      then have "IMPLIES \<circ>\<^sub>c \<langle>(eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i)) \<circ>\<^sub>c \<langle>p, q\<rangle>, (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>p, q\<rangle> \<rangle>  = \<t>"
        using  cfunc_prod_comp by (typecheck_cfuncs, force)
      then have "(eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i)) \<circ>\<^sub>c \<langle>p, q\<rangle> = \<t> \<Longrightarrow> (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>p, q\<rangle> = \<t>"
        by (typecheck_cfuncs, metis IMPLIES_true_false_is_false true_false_only_truth_values)
      then have "eq_pred X \<circ>\<^sub>c (i \<times>\<^sub>f i) \<circ>\<^sub>c \<langle>p, q\<rangle> = \<t>   \<Longrightarrow> eq_pred \<nat>\<^sub>c \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f id\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>p, q\<rangle> = \<t>"
        by (typecheck_cfuncs, simp add:  comp_associative2)
      then have "eq_pred X \<circ>\<^sub>c \<langle>i \<circ>\<^sub>c p, i \<circ>\<^sub>c q\<rangle> = \<t> \<Longrightarrow> eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>p, q\<rangle> = \<t>"
        using  cfunc_cross_prod_comp_cfunc_prod id_cross_prod id_left_unit2 by (typecheck_cfuncs, force)
      then have "i \<circ>\<^sub>c p = i \<circ>\<^sub>c q \<Longrightarrow> p = q"
        using  eq_pred_iff_eq by (typecheck_cfuncs, auto)
      then show "p = q"
        using eqs by auto
    qed

    then show "p = q"
      using main_result by linarith
  qed
  then have "\<exists> s. s : X \<rightarrow> \<nat>\<^sub>c \<and> surjective s"
    by (metis \<open>injective i\<close> epi_is_surj i_type injective_imp_monomorphism mem_Collect_eq monos_give_epis nonempty_def zero_type)
  then show False
    using \<open>\<nexists>s. s : X \<rightarrow> \<nat>\<^sub>c \<and> surjective s\<close> by auto
  qed
qed


lemma infinite_greater_than_N:
  assumes "is_infinite X"
  shows "\<nat>\<^sub>c \<le>\<^sub>c X"
  by (metis assms epis_give_monos finite_iff_nosurj_to_N is_smaller_than_def not_finite_and_infinite surjective_is_epimorphism)






(* Definition 2.6.12 *)
definition fixed_point :: "cfunc \<Rightarrow> cfunc \<Rightarrow> bool " (infix "is'_fixed'_point'_of" 50) where 
  "fixed_point a g = (\<exists> A. g : A \<rightarrow> A \<and> a \<in>\<^sub>c A \<and> g \<circ>\<^sub>c a = a)"

lemma fixed_point_def2: 
  assumes "g : A \<rightarrow> A" "a \<in>\<^sub>c A"
  shows "fixed_point a g = (g \<circ>\<^sub>c a = a)"
  unfolding fixed_point_def using assms by blast
  
(*Definition 2.6.12b*)
definition fixed_point_property :: "cset \<Rightarrow> bool" where
  "fixed_point_property A = (\<forall> g. g : A \<rightarrow> A \<longrightarrow> (\<exists> a . fixed_point a g \<and> a \<in>\<^sub>c A))"

(*Theorem 2.6.13*)
lemma Lawveres_fixed_point_theorem:
  assumes p_type[type_rule]: "p : X \<rightarrow> A\<^bsup>X\<^esup>"
  assumes p_surj: "surjective p"
  shows "fixed_point_property A"
proof(unfold fixed_point_property_def,auto) 
  fix g 
  assume g_type[type_rule]: "g : A \<rightarrow> A"
  obtain \<phi> where \<phi>_def: "\<phi> = p\<^sup>\<flat>"
    by auto
  then have \<phi>_type[type_rule]: "\<phi> : X \<times>\<^sub>c X \<rightarrow> A"
    by (simp add: flat_type p_type)
  obtain f where f_def: "f = g \<circ>\<^sub>c \<phi> \<circ>\<^sub>c diagonal(X)"
    by auto
  then have f_type[type_rule]:"f : X \<rightarrow> A"
    using \<phi>_type comp_type diagonal_type f_def g_type by blast
  obtain x_f where x_f: "metafunc f = p \<circ>\<^sub>c x_f \<and> x_f \<in>\<^sub>c X"
    using assms by (typecheck_cfuncs, metis p_surj surjective_def2)
  have "\<phi>\<^bsub>(-,x_f)\<^esub> = f"
  proof(rule one_separator[where X = "X", where Y = A])
    show "\<phi>\<^bsub>(-,x_f)\<^esub> : X \<rightarrow> A"
      using assms by (typecheck_cfuncs, simp add: x_f)
    show "f : X \<rightarrow> A"
      by (simp add: f_type)
    show "\<And>x. x \<in>\<^sub>c X \<Longrightarrow> \<phi>\<^bsub>(-,x_f)\<^esub> \<circ>\<^sub>c x = f \<circ>\<^sub>c x"
    proof - 
      fix x 
      assume x_type[type_rule]: "x \<in>\<^sub>c X"
      have "\<phi>\<^bsub>(-,x_f)\<^esub> \<circ>\<^sub>c x = \<phi> \<circ>\<^sub>c \<langle>x, x_f\<rangle>"
        using assms by (typecheck_cfuncs, meson right_param_on_el x_f)
      also have "... = ((eval_func A X) \<circ>\<^sub>c (id X \<times>\<^sub>f p)) \<circ>\<^sub>c \<langle>x, x_f\<rangle>"
        using assms \<phi>_def inv_transpose_func_def2 by auto
      also have "... = (eval_func A X) \<circ>\<^sub>c (id X \<times>\<^sub>f p) \<circ>\<^sub>c \<langle>x, x_f\<rangle>"
        by (typecheck_cfuncs, metis comp_associative2 x_f)
      also have "... = (eval_func A X) \<circ>\<^sub>c \<langle>id X  \<circ>\<^sub>c  x, p \<circ>\<^sub>c x_f\<rangle>"
        using cfunc_cross_prod_comp_cfunc_prod x_f by (typecheck_cfuncs, force)
      also have "... = (eval_func A X) \<circ>\<^sub>c \<langle>x, metafunc f\<rangle>"
        using id_left_unit2 x_f by (typecheck_cfuncs, auto)
      also have "... = f \<circ>\<^sub>c x"
        by (simp add: eval_lemma f_type x_type)
      then show "\<phi>\<^bsub>(-,x_f)\<^esub> \<circ>\<^sub>c x = f \<circ>\<^sub>c x"
        by (simp add: calculation)
    qed
  qed
  then have "\<phi>\<^bsub>(-,x_f)\<^esub> \<circ>\<^sub>c x_f = g \<circ>\<^sub>c \<phi> \<circ>\<^sub>c diagonal(X) \<circ>\<^sub>c x_f"
    by (typecheck_cfuncs, smt (z3) cfunc_type_def comp_associative domain_comp f_def x_f)
  then have "\<phi> \<circ>\<^sub>c \<langle>x_f, x_f\<rangle> = g \<circ>\<^sub>c \<phi> \<circ>\<^sub>c \<langle>x_f, x_f\<rangle>"
    using  diag_on_elements right_param_on_el x_f by (typecheck_cfuncs, auto)
  then have "(\<phi> \<circ>\<^sub>c \<langle>x_f, x_f\<rangle>) is_fixed_point_of g"
    by (metis \<open>\<phi>\<^bsub>(-,x_f)\<^esub> = f\<close> \<open>\<phi>\<^bsub>(-,x_f)\<^esub> \<circ>\<^sub>c x_f = g \<circ>\<^sub>c \<phi> \<circ>\<^sub>c diagonal X \<circ>\<^sub>c x_f\<close> comp_type diag_on_elements f_type fixed_point_def2 g_type x_f)
  then show "\<exists>a. a is_fixed_point_of g \<and> a \<in>\<^sub>c A"
    using fixed_point_def cfunc_type_def g_type by auto
qed

(*Theorem 2.6.14*)
lemma Cantors_Negative_Theorem:
  "\<nexists> s. s : X \<rightarrow> \<P> X \<and> surjective(s)"
proof(rule ccontr, auto)
  fix s 
  assume s_type: "s : X \<rightarrow> \<P> X"
  assume s_surj: "surjective s"
  then have Omega_has_ffp: "fixed_point_property \<Omega>"
    using Lawveres_fixed_point_theorem powerset_def s_type by auto
  have Omega_doesnt_have_ffp: "\<not>(fixed_point_property \<Omega>)"
    unfolding fixed_point_property_def
  proof(unfold fixed_point_def, auto)   
    have  "NOT : \<Omega> \<rightarrow> \<Omega> \<and> (\<forall>a. (\<forall>A. a \<in>\<^sub>c A \<longrightarrow> NOT : A \<rightarrow> A \<longrightarrow> NOT \<circ>\<^sub>c a \<noteq> a) \<or> \<not> a \<in>\<^sub>c \<Omega>)"
      by (typecheck_cfuncs, metis AND_complementary AND_idempotent OR_complementary OR_idempotent true_false_distinct)
    then show "\<exists>g. g : \<Omega> \<rightarrow> \<Omega> \<and> (\<forall>a. (\<forall>A. a \<in>\<^sub>c A \<longrightarrow> g : A \<rightarrow> A \<longrightarrow> g \<circ>\<^sub>c a \<noteq> a) \<or> \<not> a \<in>\<^sub>c \<Omega>)"
      by auto
  qed
  show False
    using Omega_doesnt_have_ffp Omega_has_ffp by auto
qed


(* Visit the Cardinality.thy file.  This is already proved there.  I think Cardinality and Countable should be merged*)
lemma generalized_Cantors_Negative_Theorem:
  assumes "\<Omega> \<le>\<^sub>c Y"
  shows "\<nexists> s. s : X \<rightarrow> Y\<^bsup>X\<^esup> \<and> surjective(s)"
proof(rule ccontr, auto)
  fix s 
  assume s_type: "s : X \<rightarrow> Y\<^bsup>X\<^esup>"
  assume s_surj: "surjective s"
  obtain m where m_def: "m : Y\<^bsup>X\<^esup> \<rightarrow> X" and m_mono: "monomorphism(m)"
    using epis_give_monos s_surj s_type surjective_is_epimorphism by blast
  have "\<Omega>\<^bsup>X\<^esup> \<le>\<^sub>c Y\<^bsup>X\<^esup>"
    apply typecheck_cfuncs


(*Exercise 2.6.15*)
lemma Cantors_Positive_Theorem:
  "\<exists>m. m : X \<rightarrow> \<Omega>\<^bsup>X\<^esup> \<and> injective m"
proof - 
  have eq_pred_sharp_type[type_rule]: "(eq_pred X)\<^sup>\<sharp> : X \<rightarrow>  \<Omega>\<^bsup>X\<^esup>"
    by (typecheck_cfuncs)
  have "injective((eq_pred X)\<^sup>\<sharp>)"
    unfolding injective_def
  proof(auto)
    fix x y 
    assume "x \<in>\<^sub>c domain (eq_pred X\<^sup>\<sharp>)" then have x_type[type_rule]: "x \<in>\<^sub>c X"
      using cfunc_type_def eq_pred_sharp_type by auto
    assume "y \<in>\<^sub>c domain (eq_pred X\<^sup>\<sharp>)" then have y_type[type_rule]:"y \<in>\<^sub>c X"
      using cfunc_type_def eq_pred_sharp_type by auto
    assume eq: "eq_pred X\<^sup>\<sharp> \<circ>\<^sub>c x = eq_pred X\<^sup>\<sharp> \<circ>\<^sub>c y"
    have "eq_pred X \<circ>\<^sub>c \<langle>x, x\<rangle> = eq_pred X \<circ>\<^sub>c \<langle>x, y\<rangle>"
    proof - 
      have "eq_pred X \<circ>\<^sub>c \<langle>x, x\<rangle> = ((eval_func \<Omega> X) \<circ>\<^sub>c (id X \<times>\<^sub>f (eq_pred X\<^sup>\<sharp>)) ) \<circ>\<^sub>c \<langle>x, x\<rangle>"
        using transpose_func_def by (typecheck_cfuncs, presburger)
      also have "... = (eval_func \<Omega> X) \<circ>\<^sub>c (id X \<times>\<^sub>f (eq_pred X\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>x, x\<rangle>"
        by (typecheck_cfuncs, simp add: comp_associative2)
      also have "... = (eval_func \<Omega> X) \<circ>\<^sub>c \<langle>id X \<circ>\<^sub>c x, (eq_pred X\<^sup>\<sharp>) \<circ>\<^sub>c x\<rangle>"
        using cfunc_cross_prod_comp_cfunc_prod by (typecheck_cfuncs, force)
      also have "... = (eval_func \<Omega> X) \<circ>\<^sub>c \<langle>id X \<circ>\<^sub>c x, (eq_pred X\<^sup>\<sharp>) \<circ>\<^sub>c y\<rangle>"
        by (simp add: eq)
      also have "... = (eval_func \<Omega> X) \<circ>\<^sub>c (id X \<times>\<^sub>f (eq_pred X\<^sup>\<sharp>)) \<circ>\<^sub>c \<langle>x, y\<rangle>"
        by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
      also have "... = ((eval_func \<Omega> X) \<circ>\<^sub>c (id X \<times>\<^sub>f (eq_pred X\<^sup>\<sharp>)) ) \<circ>\<^sub>c \<langle>x, y\<rangle>"
        using comp_associative2 by (typecheck_cfuncs, blast)
      also have "... = eq_pred X \<circ>\<^sub>c \<langle>x, y\<rangle>"
        using transpose_func_def by (typecheck_cfuncs, presburger)
      then show ?thesis
        by (simp add: calculation)
    qed
    then show "x = y"
      by (metis eq_pred_iff_eq x_type y_type)
  qed
  then show "\<exists>m. m : X \<rightarrow> \<Omega>\<^bsup>X\<^esup> \<and> injective m"
    using eq_pred_sharp_type injective_imp_monomorphism by blast
qed


(*Corollary 2.6.15*)
(*This is only a note: For any set X, the set \<P>X of its subsets is strictly larger than X*)






end