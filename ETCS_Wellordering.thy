theory ETCS_Wellordering
  imports ETCS_Axioms ETCS_Comparison
begin


lemma NOT_eq_pred_left_coproj:
  assumes u_type[type_rule]: "u \<in>\<^sub>c X \<Coprod> Y" and x_type[type_rule]: "x \<in>\<^sub>c X"
  shows "NOT \<circ>\<^sub>c eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>u, left_coproj X Y \<circ>\<^sub>c x\<rangle> = ((NOT \<circ>\<^sub>c  eq_pred X \<circ>\<^sub>c \<langle>id X, x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<amalg> (\<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>))  \<circ>\<^sub>c u"
proof- 
  have "NOT \<circ>\<^sub>c eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>u, left_coproj X Y \<circ>\<^sub>c x\<rangle> = NOT \<circ>\<^sub>c (((eq_pred X \<circ>\<^sub>c \<langle>id X, x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)) \<circ>\<^sub>c u)"
    by (simp add: eq_pred_left_coproj u_type x_type)
  also have "... = ( (NOT \<circ>\<^sub>c(eq_pred X \<circ>\<^sub>c \<langle>id X, x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>)) \<amalg>  (NOT \<circ>\<^sub>c(\<f> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>))) \<circ>\<^sub>c u"
    by (typecheck_cfuncs, smt (z3) cfunc_coprod_comp comp_associative2)
  also have "... = ((NOT \<circ>\<^sub>c  eq_pred X \<circ>\<^sub>c \<langle>id X, x \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>) \<amalg> (\<t> \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>)  ) \<circ>\<^sub>c u"
    using NOT_false_is_true comp_associative2 by (typecheck_cfuncs, auto)
    then show ?thesis
    using calculation by auto
qed





lemma NOT_eq_pred_right_coproj:
  assumes u_type[type_rule]: "u \<in>\<^sub>c X \<Coprod> Y" and y_type[type_rule]: "y \<in>\<^sub>c Y"
  shows "NOT \<circ>\<^sub>c eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>u, right_coproj X Y \<circ>\<^sub>c y\<rangle> = ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (NOT \<circ>\<^sub>c  eq_pred Y \<circ>\<^sub>c \<langle>id Y, y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>)) \<circ>\<^sub>c u"
proof- 
  have "NOT \<circ>\<^sub>c eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>u, right_coproj X Y \<circ>\<^sub>c y\<rangle> = NOT \<circ>\<^sub>c (((\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (eq_pred Y \<circ>\<^sub>c \<langle>id Y, y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>)) \<circ>\<^sub>c u)"
    by (simp add: eq_pred_right_coproj u_type y_type)
  also have "... = (( (NOT \<circ>\<^sub>c(\<f> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>)) \<amalg> (NOT \<circ>\<^sub>c(eq_pred Y \<circ>\<^sub>c \<langle>id Y, y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>))) \<circ>\<^sub>c u)"
    by (typecheck_cfuncs, smt (z3) cfunc_coprod_comp comp_associative2)
  also have "... = ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<amalg> (NOT \<circ>\<^sub>c  eq_pred Y \<circ>\<^sub>c \<langle>id Y, y \<circ>\<^sub>c \<beta>\<^bsub>Y\<^esub>\<rangle>)) \<circ>\<^sub>c u"
    by (typecheck_cfuncs, simp add: NOT_false_is_true comp_associative2)
  then show ?thesis
    using calculation by auto
qed




lemma eq_pred_func_pair:
  assumes f1_type[type_rule]: "f1: A \<rightarrow> X" 
  assumes f2_type[type_rule]: "f2: A \<rightarrow> X"  
  assumes g1_type[type_rule]: "g1: A \<rightarrow> Y" 
  assumes g2_type[type_rule]: "g2: A \<rightarrow> Y" 
  shows "eq_pred (X\<times>\<^sub>c Y) \<circ>\<^sub>c \<langle>\<langle>f1,g1\<rangle>, \<langle>f2, g2\<rangle>\<rangle> = 
         AND \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>f1,f2\<rangle>,  eq_pred Y \<circ>\<^sub>c \<langle>g1,g2\<rangle>\<rangle>"
proof(rule ccontr)
  assume "eq_pred (X \<times>\<^sub>c Y) \<circ>\<^sub>c \<langle>\<langle>f1,g1\<rangle>,\<langle>f2,g2\<rangle>\<rangle> \<noteq> AND \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>f1,f2\<rangle>,eq_pred Y \<circ>\<^sub>c \<langle>g1,g2\<rangle>\<rangle>"
  then obtain a where a_type[type_rule]: "a \<in>\<^sub>c A" and a_def: "(eq_pred (X \<times>\<^sub>c Y) \<circ>\<^sub>c \<langle>\<langle>f1,g1\<rangle>,\<langle>f2,g2\<rangle>\<rangle>) \<circ>\<^sub>c a \<noteq> (AND \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>f1,f2\<rangle>,eq_pred Y \<circ>\<^sub>c \<langle>g1,g2\<rangle>\<rangle>) \<circ>\<^sub>c a"
    by (typecheck_cfuncs, meson  one_separator)
  then show False 
  proof (cases "(eq_pred (X \<times>\<^sub>c Y) \<circ>\<^sub>c \<langle>\<langle>f1,g1\<rangle>,\<langle>f2,g2\<rangle>\<rangle>) \<circ>\<^sub>c a = \<t>")
    assume a1: "(eq_pred (X \<times>\<^sub>c Y) \<circ>\<^sub>c \<langle>\<langle>f1,g1\<rangle>,\<langle>f2,g2\<rangle>\<rangle>) \<circ>\<^sub>c a = \<t>"
    then have "eq_pred (X \<times>\<^sub>c Y) \<circ>\<^sub>c \<langle>\<langle>f1,g1\<rangle>,\<langle>f2,g2\<rangle>\<rangle> \<circ>\<^sub>c a  = \<t>"
      by (typecheck_cfuncs, simp add: a1 comp_associative2)
    then have "eq_pred (X \<times>\<^sub>c Y) \<circ>\<^sub>c \<langle>\<langle>f1,g1\<rangle> \<circ>\<^sub>c a ,\<langle>f2,g2\<rangle> \<circ>\<^sub>c a\<rangle>   = \<t>"
      using  cfunc_prod_comp by (typecheck_cfuncs, force)
    then have "\<langle>f1,g1\<rangle> \<circ>\<^sub>c a =  \<langle>f2, g2\<rangle> \<circ>\<^sub>c a"
      by (typecheck_cfuncs, meson comp_type eq_pred_iff_eq)
    then have "\<langle>f1 \<circ>\<^sub>c a,g1 \<circ>\<^sub>c a\<rangle>  =  \<langle>f2 \<circ>\<^sub>c a , g2\<circ>\<^sub>c a \<rangle>"
      using  cfunc_prod_comp by (typecheck_cfuncs, force)
    then have contradiction: "(f1 \<circ>\<^sub>c a = f2 \<circ>\<^sub>c a) \<and> (g1 \<circ>\<^sub>c a = g2 \<circ>\<^sub>c a)"
      using cart_prod_eq2 by (typecheck_cfuncs, auto)
    have "(AND \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>f1,f2\<rangle>,eq_pred Y \<circ>\<^sub>c \<langle>g1,g2\<rangle>\<rangle>) \<circ>\<^sub>c a = \<f>"
      using a_def a1  by (typecheck_cfuncs, metis  true_false_only_truth_values)
    then have "AND \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>f1,f2\<rangle>,eq_pred Y \<circ>\<^sub>c \<langle>g1,g2\<rangle>\<rangle> \<circ>\<^sub>c a = \<f>"
      by (typecheck_cfuncs, simp add:  comp_associative2)
    then have "AND \<circ>\<^sub>c \<langle>(eq_pred X \<circ>\<^sub>c \<langle>f1,f2\<rangle>) \<circ>\<^sub>c a, (eq_pred Y \<circ>\<^sub>c \<langle>g1,g2\<rangle>) \<circ>\<^sub>c a\<rangle>  = \<f>"
      using  cfunc_prod_comp by (typecheck_cfuncs, force)
    then have "(((eq_pred X \<circ>\<^sub>c \<langle>f1,f2\<rangle>) \<circ>\<^sub>c a) = \<f>) \<or> (((eq_pred Y \<circ>\<^sub>c \<langle>g1,g2\<rangle>) \<circ>\<^sub>c a) = \<f>)"
      by (typecheck_cfuncs, metis AND_true_true_is_true  true_false_only_truth_values)
    then have "((eq_pred X \<circ>\<^sub>c \<langle>f1,f2\<rangle> \<circ>\<^sub>c a) = \<f>) \<or> ((eq_pred Y \<circ>\<^sub>c \<langle>g1,g2\<rangle> \<circ>\<^sub>c a) = \<f>)"
      by (typecheck_cfuncs, simp add:  comp_associative2)
    then have "((eq_pred X \<circ>\<^sub>c \<langle>f1 \<circ>\<^sub>c a,f2 \<circ>\<^sub>c a\<rangle>) = \<f>) \<or> ((eq_pred Y \<circ>\<^sub>c \<langle>g1 \<circ>\<^sub>c a, g2 \<circ>\<^sub>c a\<rangle>) = \<f>)"
      using  cfunc_prod_comp by (typecheck_cfuncs, force)
    then have "(f1 \<circ>\<^sub>c a \<noteq> f2 \<circ>\<^sub>c a) \<or> (g1 \<circ>\<^sub>c a \<noteq> g2 \<circ>\<^sub>c a)"
      using  eq_pred_iff_eq_conv by (typecheck_cfuncs, blast)
    then show False
      by (simp add: contradiction)
  next
    assume "(eq_pred (X \<times>\<^sub>c Y) \<circ>\<^sub>c \<langle>\<langle>f1,g1\<rangle>,\<langle>f2,g2\<rangle>\<rangle>) \<circ>\<^sub>c a \<noteq> \<t>"
    then have a1: "(eq_pred (X \<times>\<^sub>c Y) \<circ>\<^sub>c \<langle>\<langle>f1,g1\<rangle>,\<langle>f2,g2\<rangle>\<rangle>) \<circ>\<^sub>c a = \<f>"
      using true_false_only_truth_values by (typecheck_cfuncs, blast)
    then have "eq_pred (X \<times>\<^sub>c Y) \<circ>\<^sub>c \<langle>\<langle>f1,g1\<rangle>,\<langle>f2,g2\<rangle>\<rangle> \<circ>\<^sub>c a = \<f>"
      by (typecheck_cfuncs, simp add: a1 comp_associative2)
    then have "eq_pred (X \<times>\<^sub>c Y) \<circ>\<^sub>c \<langle>\<langle>f1,g1\<rangle> \<circ>\<^sub>c a ,\<langle>f2,g2\<rangle> \<circ>\<^sub>c a\<rangle>   = \<f>"
      using  cfunc_prod_comp by (typecheck_cfuncs, force)
    then have "\<langle>f1,g1\<rangle> \<circ>\<^sub>c a \<noteq>  \<langle>f2, g2\<rangle> \<circ>\<^sub>c a"
      using  eq_pred_iff_eq_conv by (typecheck_cfuncs, presburger)
    then have "\<langle>f1 \<circ>\<^sub>c a,g1 \<circ>\<^sub>c a\<rangle>  \<noteq>  \<langle>f2 \<circ>\<^sub>c a , g2\<circ>\<^sub>c a \<rangle>"
      using  cfunc_prod_comp by (typecheck_cfuncs, force)
    then have contradiction: "(f1 \<circ>\<^sub>c a \<noteq> f2 \<circ>\<^sub>c a) \<or> (g1 \<circ>\<^sub>c a \<noteq> g2 \<circ>\<^sub>c a)"
      using cart_prod_eq2 by (typecheck_cfuncs, auto)
    have "(AND \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>f1,f2\<rangle>,eq_pred Y \<circ>\<^sub>c \<langle>g1,g2\<rangle>\<rangle>) \<circ>\<^sub>c a = \<t>"
      by (typecheck_cfuncs, metis  a1 a_def true_false_only_truth_values)
    then have "AND \<circ>\<^sub>c \<langle>eq_pred X \<circ>\<^sub>c \<langle>f1,f2\<rangle>,eq_pred Y \<circ>\<^sub>c \<langle>g1,g2\<rangle>\<rangle> \<circ>\<^sub>c a = \<t>"
      by (typecheck_cfuncs, simp add:  comp_associative2)
    then have "AND \<circ>\<^sub>c \<langle>(eq_pred X \<circ>\<^sub>c \<langle>f1,f2\<rangle>) \<circ>\<^sub>c a, (eq_pred Y \<circ>\<^sub>c \<langle>g1,g2\<rangle>) \<circ>\<^sub>c a\<rangle>  = \<t>"
      using  cfunc_prod_comp by (typecheck_cfuncs, force)
    then have "(((eq_pred X \<circ>\<^sub>c \<langle>f1,f2\<rangle>) \<circ>\<^sub>c a) = \<t>) \<and> (((eq_pred Y \<circ>\<^sub>c \<langle>g1,g2\<rangle>) \<circ>\<^sub>c a) = \<t>)"
      by (typecheck_cfuncs, metis AND_false_left_is_false AND_false_right_is_false  true_false_only_truth_values)
    then have "((eq_pred X \<circ>\<^sub>c \<langle>f1,f2\<rangle> \<circ>\<^sub>c a) = \<t>) \<and> ((eq_pred Y \<circ>\<^sub>c \<langle>g1,g2\<rangle> \<circ>\<^sub>c a) = \<t>)"
      by (typecheck_cfuncs, simp add:  comp_associative2)
    then have "((eq_pred X \<circ>\<^sub>c \<langle>f1 \<circ>\<^sub>c a,f2 \<circ>\<^sub>c a\<rangle>) = \<t>) \<and> ((eq_pred Y \<circ>\<^sub>c \<langle>g1 \<circ>\<^sub>c a, g2 \<circ>\<^sub>c a\<rangle>) = \<t>)"
      using  cfunc_prod_comp by (typecheck_cfuncs, force)
    then have "(f1 \<circ>\<^sub>c a = f2 \<circ>\<^sub>c a) \<and> (g1 \<circ>\<^sub>c a = g2 \<circ>\<^sub>c a)"
      using  eq_pred_iff_eq by (typecheck_cfuncs, blast)  
    then show False
      using contradiction by blast
  qed
qed


lemma eq_pred_func_copair:
  assumes f1_type[type_rule]: "f1: X \<rightarrow> Z" 
  assumes f2_type[type_rule]: "f2: X \<rightarrow> Z"  
  assumes g1_type[type_rule]: "g1: Y \<rightarrow> Z" 
  assumes g2_type[type_rule]: "g2: Y \<rightarrow> Z" 
  shows "eq_pred Z \<circ>\<^sub>c \<langle>(f1\<amalg>g1), (f2\<amalg>g2)\<rangle> = 
        (eq_pred Z \<circ>\<^sub>c \<langle>f1,f2\<rangle>)\<amalg>(eq_pred Z \<circ>\<^sub>c \<langle>g1,g2\<rangle>)"
proof(rule ccontr)
  assume "eq_pred Z \<circ>\<^sub>c \<langle>f1 \<amalg> g1,f2 \<amalg> g2\<rangle> \<noteq> (eq_pred Z \<circ>\<^sub>c \<langle>f1,f2\<rangle>) \<amalg> (eq_pred Z \<circ>\<^sub>c \<langle>g1,g2\<rangle>)"
  then obtain xy where xy_type[type_rule]: "xy \<in>\<^sub>c X \<Coprod> Y" and xy_def: "(eq_pred Z \<circ>\<^sub>c \<langle>f1 \<amalg> g1,f2 \<amalg> g2\<rangle>) \<circ>\<^sub>c xy \<noteq> ((eq_pred Z \<circ>\<^sub>c \<langle>f1,f2\<rangle>) \<amalg> (eq_pred Z \<circ>\<^sub>c \<langle>g1,g2\<rangle>)) \<circ>\<^sub>c xy"
    using  one_separator by (typecheck_cfuncs, blast)
  show False
  proof(cases "\<exists> x. x \<in>\<^sub>c X \<and> xy = left_coproj X Y \<circ>\<^sub>c x")
    assume "\<exists>x. x \<in>\<^sub>c X \<and> xy = left_coproj X Y \<circ>\<^sub>c x"
    then obtain x where x_type[type_rule]: "x \<in>\<^sub>c X" and x_def: "xy = left_coproj X Y \<circ>\<^sub>c x"
      by blast
    show False
    proof(cases "(eq_pred Z \<circ>\<^sub>c \<langle>f1 \<amalg> g1,f2 \<amalg> g2\<rangle>) \<circ>\<^sub>c xy = \<t>")
      assume LHS_true: "(eq_pred Z \<circ>\<^sub>c \<langle>f1 \<amalg> g1,f2 \<amalg> g2\<rangle>) \<circ>\<^sub>c xy = \<t>"
      
      then have "eq_pred Z \<circ>\<^sub>c \<langle>f1 \<amalg> g1,f2 \<amalg> g2\<rangle> \<circ>\<^sub>c xy = \<t>"
        using  comp_associative2 by (typecheck_cfuncs, force)
      then have "(eq_pred Z \<circ>\<^sub>c \<langle>(f1 \<amalg> g1),(f2 \<amalg> g2)\<rangle> \<circ>\<^sub>c (left_coproj X Y \<circ>\<^sub>c x))  = \<t>"
        using LHS_true x_def by blast
      then have "(eq_pred Z \<circ>\<^sub>c \<langle>(f1 \<amalg> g1)\<circ>\<^sub>c (left_coproj X Y \<circ>\<^sub>c x) ,(f2 \<amalg> g2) \<circ>\<^sub>c (left_coproj X Y \<circ>\<^sub>c x)\<rangle> )  = \<t>"
        using cfunc_prod_comp by (typecheck_cfuncs, auto)
      then have "(eq_pred Z \<circ>\<^sub>c \<langle>((f1 \<amalg> g1)\<circ>\<^sub>c left_coproj X Y) \<circ>\<^sub>c x ,((f2 \<amalg> g2) \<circ>\<^sub>c left_coproj X Y) \<circ>\<^sub>c x\<rangle> )  = \<t>"
        using  comp_associative2 by (typecheck_cfuncs, force)
      then have contradiction: "eq_pred Z \<circ>\<^sub>c \<langle>f1 \<circ>\<^sub>c x ,f2 \<circ>\<^sub>c x\<rangle>  = \<t>"
        by (typecheck_cfuncs, metis  g1_type g2_type left_coproj_cfunc_coprod)
      have "((eq_pred Z \<circ>\<^sub>c \<langle>f1,f2\<rangle>) \<amalg> (eq_pred Z \<circ>\<^sub>c \<langle>g1,g2\<rangle>)) \<circ>\<^sub>c xy = \<f>"
        by (typecheck_cfuncs, metis LHS_true true_false_only_truth_values xy_def)
      then have f0: "(((eq_pred Z \<circ>\<^sub>c \<langle>f1,f2\<rangle>) \<amalg> (eq_pred Z \<circ>\<^sub>c \<langle>g1,g2\<rangle>)) \<circ>\<^sub>c left_coproj X Y) \<circ>\<^sub>c x = \<f>"
        using  comp_associative2 x_def by (typecheck_cfuncs, auto)
      have "((eq_pred Z \<circ>\<^sub>c \<langle>f1,f2\<rangle>) \<amalg> (eq_pred Z \<circ>\<^sub>c \<langle>g1,g2\<rangle>)) \<circ>\<^sub>c left_coproj X Y = eq_pred Z \<circ>\<^sub>c \<langle>f1,f2\<rangle>"
        using left_coproj_cfunc_coprod by (typecheck_cfuncs, presburger)
      then have "(eq_pred Z \<circ>\<^sub>c \<langle>f1,f2\<rangle>) \<circ>\<^sub>c x = \<f>"
        using f0 by presburger
      then have "eq_pred Z \<circ>\<^sub>c \<langle>f1,f2\<rangle> \<circ>\<^sub>c x = \<f>"
        by (typecheck_cfuncs, simp add:  comp_associative2)
      then have "eq_pred Z \<circ>\<^sub>c \<langle>f1 \<circ>\<^sub>c x,f2  \<circ>\<^sub>c x\<rangle> = \<f>"
        using  cfunc_prod_comp by (typecheck_cfuncs, force)
      then show False
        using contradiction true_false_distinct by auto
    next
      assume "(eq_pred Z \<circ>\<^sub>c \<langle>f1 \<amalg> g1,f2 \<amalg> g2\<rangle>) \<circ>\<^sub>c xy \<noteq> \<t>"
      then have LHS_false: "(eq_pred Z \<circ>\<^sub>c \<langle>f1 \<amalg> g1,f2 \<amalg> g2\<rangle>) \<circ>\<^sub>c xy = \<f>"
        using  true_false_only_truth_values by (typecheck_cfuncs, blast)
      then have "eq_pred Z \<circ>\<^sub>c \<langle>f1 \<amalg> g1,f2 \<amalg> g2\<rangle> \<circ>\<^sub>c xy = \<f>"
        using  comp_associative2 by (typecheck_cfuncs, force)
      then have "(eq_pred Z \<circ>\<^sub>c \<langle>(f1 \<amalg> g1),(f2 \<amalg> g2)\<rangle> \<circ>\<^sub>c (left_coproj X Y \<circ>\<^sub>c x))  = \<f>"
        using LHS_false x_def by blast
      then have "(eq_pred Z \<circ>\<^sub>c \<langle>(f1 \<amalg> g1)\<circ>\<^sub>c (left_coproj X Y \<circ>\<^sub>c x) ,(f2 \<amalg> g2) \<circ>\<^sub>c (left_coproj X Y \<circ>\<^sub>c x)\<rangle> )  = \<f>"
        using cfunc_prod_comp by (typecheck_cfuncs, auto)
      then have "(eq_pred Z \<circ>\<^sub>c \<langle>((f1 \<amalg> g1)\<circ>\<^sub>c left_coproj X Y) \<circ>\<^sub>c x ,((f2 \<amalg> g2) \<circ>\<^sub>c left_coproj X Y) \<circ>\<^sub>c x\<rangle> )  = \<f>"
        using  comp_associative2 by (typecheck_cfuncs, force)
      then have contradiction: "eq_pred Z \<circ>\<^sub>c \<langle>f1 \<circ>\<^sub>c x ,f2 \<circ>\<^sub>c x\<rangle>   = \<f>"
        by (typecheck_cfuncs, metis  g1_type g2_type left_coproj_cfunc_coprod)
      have "((eq_pred Z \<circ>\<^sub>c \<langle>f1,f2\<rangle>) \<amalg> (eq_pred Z \<circ>\<^sub>c \<langle>g1,g2\<rangle>)) \<circ>\<^sub>c xy = \<t>"
        by (typecheck_cfuncs, metis LHS_false true_false_only_truth_values xy_def)
      then have f0: "(((eq_pred Z \<circ>\<^sub>c \<langle>f1,f2\<rangle>) \<amalg> (eq_pred Z \<circ>\<^sub>c \<langle>g1,g2\<rangle>)) \<circ>\<^sub>c left_coproj X Y) \<circ>\<^sub>c x = \<t>"
        using  comp_associative2 x_def by (typecheck_cfuncs, auto)
      have "((eq_pred Z \<circ>\<^sub>c \<langle>f1,f2\<rangle>) \<amalg> (eq_pred Z \<circ>\<^sub>c \<langle>g1,g2\<rangle>)) \<circ>\<^sub>c left_coproj X Y = eq_pred Z \<circ>\<^sub>c \<langle>f1,f2\<rangle>"
        using left_coproj_cfunc_coprod by (typecheck_cfuncs, presburger)
      then have "(eq_pred Z \<circ>\<^sub>c \<langle>f1,f2\<rangle>) \<circ>\<^sub>c x = \<t>"
        using f0 by presburger
      then have "eq_pred Z \<circ>\<^sub>c \<langle>f1,f2\<rangle> \<circ>\<^sub>c x = \<t>"
        by (typecheck_cfuncs, simp add:  comp_associative2)
      then have "eq_pred Z \<circ>\<^sub>c \<langle>f1 \<circ>\<^sub>c x,f2  \<circ>\<^sub>c x\<rangle> = \<t>"
        using  cfunc_prod_comp by (typecheck_cfuncs, force)
      then show False
        using contradiction true_false_distinct by auto
    qed
  next
    assume "\<nexists>x. x \<in>\<^sub>c X \<and> xy = left_coproj X Y \<circ>\<^sub>c x"
    then obtain y where y_type[type_rule]: "y \<in>\<^sub>c Y" and y_def: " xy = right_coproj X Y \<circ>\<^sub>c y"
      using  coprojs_jointly_surj by (typecheck_cfuncs, blast)
    show False
    proof(cases "(eq_pred Z \<circ>\<^sub>c \<langle>f1 \<amalg> g1,f2 \<amalg> g2\<rangle>) \<circ>\<^sub>c xy = \<t>")
      assume LHS_true: "(eq_pred Z \<circ>\<^sub>c \<langle>f1 \<amalg> g1,f2 \<amalg> g2\<rangle>) \<circ>\<^sub>c xy = \<t>"
      
      then have "eq_pred Z \<circ>\<^sub>c \<langle>f1 \<amalg> g1,f2 \<amalg> g2\<rangle> \<circ>\<^sub>c xy = \<t>"
        using  comp_associative2 by (typecheck_cfuncs, force)
      then have "(eq_pred Z \<circ>\<^sub>c \<langle>(f1 \<amalg> g1),(f2 \<amalg> g2)\<rangle> \<circ>\<^sub>c (right_coproj X Y \<circ>\<^sub>c y))  = \<t>"
        using LHS_true y_def by blast
      then have "(eq_pred Z \<circ>\<^sub>c \<langle>(f1 \<amalg> g1)\<circ>\<^sub>c (right_coproj X Y \<circ>\<^sub>c y) ,(f2 \<amalg> g2) \<circ>\<^sub>c (right_coproj X Y \<circ>\<^sub>c y)\<rangle> )  = \<t>"
        using cfunc_prod_comp by (typecheck_cfuncs, auto)
      then have "(eq_pred Z \<circ>\<^sub>c \<langle>((f1 \<amalg> g1)\<circ>\<^sub>c right_coproj X Y) \<circ>\<^sub>c y ,((f2 \<amalg> g2) \<circ>\<^sub>c right_coproj X Y) \<circ>\<^sub>c y\<rangle> )  = \<t>"
        using  comp_associative2 by (typecheck_cfuncs, force)
      then have contradiction: "eq_pred Z \<circ>\<^sub>c \<langle>g1 \<circ>\<^sub>c y ,g2 \<circ>\<^sub>c y\<rangle>  = \<t>"
        by (typecheck_cfuncs, metis  f1_type f2_type right_coproj_cfunc_coprod)
      have "((eq_pred Z \<circ>\<^sub>c \<langle>f1,f2\<rangle>) \<amalg> (eq_pred Z \<circ>\<^sub>c \<langle>g1,g2\<rangle>)) \<circ>\<^sub>c xy = \<f>"
        by (typecheck_cfuncs, metis LHS_true true_false_only_truth_values xy_def)
      then have f0: "(((eq_pred Z \<circ>\<^sub>c \<langle>f1,f2\<rangle>) \<amalg> (eq_pred Z \<circ>\<^sub>c \<langle>g1,g2\<rangle>)) \<circ>\<^sub>c right_coproj X Y) \<circ>\<^sub>c y = \<f>"
        using  comp_associative2 y_def by (typecheck_cfuncs, auto)
      have "((eq_pred Z \<circ>\<^sub>c \<langle>f1,f2\<rangle>) \<amalg> (eq_pred Z \<circ>\<^sub>c \<langle>g1,g2\<rangle>)) \<circ>\<^sub>c right_coproj X Y = eq_pred Z \<circ>\<^sub>c \<langle>g1,g2\<rangle>"
        using right_coproj_cfunc_coprod by (typecheck_cfuncs, presburger)
      then have "(eq_pred Z \<circ>\<^sub>c \<langle>g1,g2\<rangle>) \<circ>\<^sub>c y = \<f>"
        using f0 by presburger
      then have "eq_pred Z \<circ>\<^sub>c \<langle>g1,g2\<rangle> \<circ>\<^sub>cy = \<f>"
        by (typecheck_cfuncs, simp add:  comp_associative2)
      then have "eq_pred Z \<circ>\<^sub>c \<langle>g1 \<circ>\<^sub>c y,g2  \<circ>\<^sub>c y\<rangle> = \<f>"
        using  cfunc_prod_comp by (typecheck_cfuncs, force)
      then show False
        using contradiction true_false_distinct by auto
    next
      assume "(eq_pred Z \<circ>\<^sub>c \<langle>f1 \<amalg> g1,f2 \<amalg> g2\<rangle>) \<circ>\<^sub>c xy \<noteq> \<t>"
      then have LHS_false: "(eq_pred Z \<circ>\<^sub>c \<langle>f1 \<amalg> g1,f2 \<amalg> g2\<rangle>) \<circ>\<^sub>c xy = \<f>"
        using  true_false_only_truth_values by (typecheck_cfuncs, blast)
      then have "eq_pred Z \<circ>\<^sub>c \<langle>f1 \<amalg> g1,f2 \<amalg> g2\<rangle> \<circ>\<^sub>c xy = \<f>"
        using  comp_associative2 by (typecheck_cfuncs, force)
      then have "(eq_pred Z \<circ>\<^sub>c \<langle>(f1 \<amalg> g1),(f2 \<amalg> g2)\<rangle> \<circ>\<^sub>c (right_coproj X Y \<circ>\<^sub>c y))  = \<f>"
        using LHS_false y_def by blast
      then have "(eq_pred Z \<circ>\<^sub>c \<langle>(f1 \<amalg> g1)\<circ>\<^sub>c (right_coproj X Y \<circ>\<^sub>c y) ,(f2 \<amalg> g2) \<circ>\<^sub>c (right_coproj X Y \<circ>\<^sub>c y)\<rangle> )  = \<f>"
        using cfunc_prod_comp by (typecheck_cfuncs, auto)
      then have "(eq_pred Z \<circ>\<^sub>c \<langle>((f1 \<amalg> g1)\<circ>\<^sub>c right_coproj X Y) \<circ>\<^sub>c y ,((f2 \<amalg> g2) \<circ>\<^sub>c right_coproj X Y) \<circ>\<^sub>c y\<rangle> )  = \<f>"
        using  comp_associative2 by (typecheck_cfuncs, force)
      then have contradiction: "eq_pred Z \<circ>\<^sub>c \<langle>g1 \<circ>\<^sub>c y ,g2 \<circ>\<^sub>c y\<rangle>   = \<f>"
        by (typecheck_cfuncs, metis  f1_type f2_type right_coproj_cfunc_coprod)
      have "((eq_pred Z \<circ>\<^sub>c \<langle>f1,f2\<rangle>) \<amalg> (eq_pred Z \<circ>\<^sub>c \<langle>g1,g2\<rangle>)) \<circ>\<^sub>c xy = \<t>"
        by (typecheck_cfuncs, metis LHS_false true_false_only_truth_values xy_def)
      then have f0: "(((eq_pred Z \<circ>\<^sub>c \<langle>f1,f2\<rangle>) \<amalg> (eq_pred Z \<circ>\<^sub>c \<langle>g1,g2\<rangle>)) \<circ>\<^sub>c right_coproj X Y) \<circ>\<^sub>c y = \<t>"
        using  comp_associative2 y_def by (typecheck_cfuncs, auto)
      have "((eq_pred Z \<circ>\<^sub>c \<langle>f1,f2\<rangle>) \<amalg> (eq_pred Z \<circ>\<^sub>c \<langle>g1,g2\<rangle>)) \<circ>\<^sub>c right_coproj X Y = eq_pred Z \<circ>\<^sub>c \<langle>g1,g2\<rangle>"
        using right_coproj_cfunc_coprod by (typecheck_cfuncs, presburger)
      then have "(eq_pred Z \<circ>\<^sub>c \<langle>g1,g2\<rangle>) \<circ>\<^sub>c y = \<t>"
        using f0 by presburger
      then have "eq_pred Z \<circ>\<^sub>c \<langle>g1,g2\<rangle> \<circ>\<^sub>c y = \<t>"
        by (typecheck_cfuncs, simp add:  comp_associative2)
      then have "eq_pred Z \<circ>\<^sub>c \<langle>g1 \<circ>\<^sub>c y, g2  \<circ>\<^sub>c y\<rangle> = \<t>"
        using  cfunc_prod_comp by (typecheck_cfuncs, force)
      then show False
        using contradiction true_false_distinct by auto
    qed
  qed
qed




lemma eq_pred_left_coproj2:
  assumes a_type[type_rule]: "f : A \<rightarrow> X" and b_type[type_rule]: "g : A \<rightarrow> X"
  shows "eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>left_coproj X Y \<circ>\<^sub>c f, left_coproj X Y \<circ>\<^sub>c g\<rangle> = eq_pred X \<circ>\<^sub>c \<langle>f, g\<rangle>"
proof(rule one_separator[where X = A, where Y = \<Omega>])
  show "eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>left_coproj X Y \<circ>\<^sub>c f,left_coproj X Y \<circ>\<^sub>c g\<rangle> : A \<rightarrow> \<Omega>"
    by typecheck_cfuncs
  show "eq_pred X \<circ>\<^sub>c \<langle>f,g\<rangle> : A \<rightarrow> \<Omega>"
    by typecheck_cfuncs
  show "\<And>a. a \<in>\<^sub>c A \<Longrightarrow> (eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>left_coproj X Y \<circ>\<^sub>c f,left_coproj X Y \<circ>\<^sub>c g\<rangle>) \<circ>\<^sub>c a = (eq_pred X \<circ>\<^sub>c \<langle>f,g\<rangle>) \<circ>\<^sub>c a"
  proof - 
    fix a
    assume a_type[type_rule]: "a \<in>\<^sub>c A"
    have "(eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>left_coproj X Y \<circ>\<^sub>c f,left_coproj X Y \<circ>\<^sub>c g\<rangle>) \<circ>\<^sub>c a = 
           eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>left_coproj X Y \<circ>\<^sub>c f,left_coproj X Y \<circ>\<^sub>c g\<rangle>  \<circ>\<^sub>c a"
      using comp_associative2 by (typecheck_cfuncs, force)
    also have "... = eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>left_coproj X Y \<circ>\<^sub>c f \<circ>\<^sub>c a,left_coproj X Y \<circ>\<^sub>c g \<circ>\<^sub>c a\<rangle>"
      by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
    also have "... = (eq_pred X \<circ>\<^sub>c \<langle>f,g\<rangle>) \<circ>\<^sub>c a"
    proof(cases "f \<circ>\<^sub>c a = g \<circ>\<^sub>c a")
      show "f \<circ>\<^sub>c a = g \<circ>\<^sub>c a \<Longrightarrow> eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>left_coproj X Y \<circ>\<^sub>c f \<circ>\<^sub>c a,left_coproj X Y \<circ>\<^sub>c g \<circ>\<^sub>c a\<rangle> = (eq_pred X \<circ>\<^sub>c \<langle>f,g\<rangle>) \<circ>\<^sub>c a"
        by (typecheck_cfuncs, smt (z3)  cfunc_prod_comp comp_associative2 eq_pred_iff_eq)
      show "f \<circ>\<^sub>c a \<noteq> g \<circ>\<^sub>c a \<Longrightarrow> eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>left_coproj X Y \<circ>\<^sub>c f \<circ>\<^sub>c a,left_coproj X Y \<circ>\<^sub>c g \<circ>\<^sub>c a\<rangle> = (eq_pred X \<circ>\<^sub>c \<langle>f,g\<rangle>) \<circ>\<^sub>c a"
        by (typecheck_cfuncs, smt (verit, best) cfunc_prod_comp comp_associative2 eq_pred_iff_eq_conv monomorphism_def3 left_coproj_are_monomorphisms)
    qed
    then show "(eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>left_coproj X Y \<circ>\<^sub>c f,left_coproj X Y \<circ>\<^sub>c g\<rangle>) \<circ>\<^sub>c a = (eq_pred X \<circ>\<^sub>c \<langle>f,g\<rangle>) \<circ>\<^sub>c a"
      using calculation by auto
  qed
qed


lemma eq_pred_right_coproj2:
  assumes a_type[type_rule]: "f : A \<rightarrow> Y" and b_type[type_rule]: "g : A \<rightarrow> Y"
  shows "eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>right_coproj X Y \<circ>\<^sub>c f, right_coproj X Y \<circ>\<^sub>c g\<rangle> = eq_pred Y \<circ>\<^sub>c \<langle>f, g\<rangle>"
proof(rule one_separator[where X = A, where Y = \<Omega>])
  show "eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>right_coproj X Y \<circ>\<^sub>c f,right_coproj X Y \<circ>\<^sub>c g\<rangle> : A \<rightarrow> \<Omega>"
    by typecheck_cfuncs
  show "eq_pred Y \<circ>\<^sub>c \<langle>f,g\<rangle> : A \<rightarrow> \<Omega>"
    by typecheck_cfuncs
  show "\<And>a. a \<in>\<^sub>c A \<Longrightarrow> (eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>right_coproj X Y \<circ>\<^sub>c f,right_coproj X Y \<circ>\<^sub>c g\<rangle>) \<circ>\<^sub>c a = (eq_pred Y \<circ>\<^sub>c \<langle>f,g\<rangle>) \<circ>\<^sub>c a"
  proof - 
    fix a
    assume a_type[type_rule]: "a \<in>\<^sub>c A"
    have "(eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>right_coproj X Y \<circ>\<^sub>c f,right_coproj X Y \<circ>\<^sub>c g\<rangle>) \<circ>\<^sub>c a = 
           eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>right_coproj X Y \<circ>\<^sub>c f,right_coproj X Y \<circ>\<^sub>c g\<rangle>  \<circ>\<^sub>c a"
      using comp_associative2 by (typecheck_cfuncs, force)
    also have "... = eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>right_coproj X Y \<circ>\<^sub>c f \<circ>\<^sub>c a,right_coproj X Y \<circ>\<^sub>c g \<circ>\<^sub>c a\<rangle>"
      by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
    also have "... = (eq_pred Y \<circ>\<^sub>c \<langle>f,g\<rangle>) \<circ>\<^sub>c a"
    proof(cases "f \<circ>\<^sub>c a = g \<circ>\<^sub>c a")
      show "f \<circ>\<^sub>c a = g \<circ>\<^sub>c a \<Longrightarrow> eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>right_coproj X Y \<circ>\<^sub>c f \<circ>\<^sub>c a,right_coproj X Y \<circ>\<^sub>c g \<circ>\<^sub>c a\<rangle> = (eq_pred Y \<circ>\<^sub>c \<langle>f,g\<rangle>) \<circ>\<^sub>c a"
        by (typecheck_cfuncs, smt (z3)  cfunc_prod_comp comp_associative2 eq_pred_iff_eq)
      show "f \<circ>\<^sub>c a \<noteq> g \<circ>\<^sub>c a \<Longrightarrow> eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>right_coproj X Y \<circ>\<^sub>c f \<circ>\<^sub>c a,right_coproj X Y \<circ>\<^sub>c g \<circ>\<^sub>c a\<rangle> = (eq_pred Y \<circ>\<^sub>c \<langle>f,g\<rangle>) \<circ>\<^sub>c a"
        by (typecheck_cfuncs, smt (verit, best) cfunc_prod_comp comp_associative2 eq_pred_iff_eq_conv monomorphism_def3 right_coproj_are_monomorphisms)
    qed
    then show "(eq_pred (X \<Coprod> Y) \<circ>\<^sub>c \<langle>right_coproj X Y \<circ>\<^sub>c f,right_coproj X Y \<circ>\<^sub>c g\<rangle>) \<circ>\<^sub>c a = (eq_pred Y \<circ>\<^sub>c \<langle>f,g\<rangle>) \<circ>\<^sub>c a"
      using calculation by auto
  qed
qed 
  
lemma true_beta_one:
  "\<t> \<circ>\<^sub>c \<beta>\<^bsub>one\<^esub> = \<t>"
  by (metis diagonal_def eq_pred_iff_eq_conv2 eq_pred_square id_type)

lemma false_beta_one:
  "\<f> \<circ>\<^sub>c \<beta>\<^bsub>one\<^esub> = \<f>"
  by (metis false_func_type id_right_unit2 id_type one_unique_element terminal_func_type)

lemma comp_one_id: "a : one \<rightarrow> Y \<Longrightarrow> x : one \<rightarrow> one \<Longrightarrow> a \<circ>\<^sub>c x = a"
  by (metis id_right_unit2 id_type one_unique_element)

lemma ETCS_bool_eq_implies:
  assumes p_type[type_rule]: "p : one \<rightarrow> \<Omega>" and q_type[type_rule]: "q : one \<rightarrow> \<Omega>"
  shows "(p = \<t> \<Longrightarrow> q = \<t>) \<Longrightarrow> (q = \<t> \<Longrightarrow> p = \<t>) \<Longrightarrow> p = q"
  using p_type q_type true_false_only_truth_values by blast

lemma ETCS_bool_eq_implies':
  assumes p_type[type_rule]: "p : X \<rightarrow> \<Omega>" and q_type[type_rule]: "q : X \<rightarrow> \<Omega>"
  shows "(\<And>x. x : one \<rightarrow> X \<Longrightarrow> p \<circ>\<^sub>c x = \<t> \<Longrightarrow> q \<circ>\<^sub>c x = \<t>)
     \<Longrightarrow> (\<And>x. x : one \<rightarrow> X \<Longrightarrow> q \<circ>\<^sub>c x = \<t> \<Longrightarrow> p \<circ>\<^sub>c x = \<t>) \<Longrightarrow> p = q"
  by (etcs_rule one_separator, smt comp_type p_type q_type ETCS_bool_eq_implies)


lemma 
  assumes p_type[type_rule]: "p : \<nat>\<^sub>c \<rightarrow> \<Omega>" and n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes zero_case: "p \<circ>\<^sub>c zero = \<t>"
  assumes successor_case: "\<And>n. n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> p \<circ>\<^sub>c n = \<t> \<Longrightarrow> p \<circ>\<^sub>c successor \<circ>\<^sub>c n = \<t>"
  shows "p \<circ>\<^sub>c n = \<t>"
proof -
  obtain q where
    q_type[type_rule]: "q : one \<rightarrow> \<Omega> \<times>\<^sub>c \<nat>\<^sub>c" and
    q_def: "q = \<langle>p \<circ>\<^sub>c zero, zero\<rangle>"
    by typecheck_cfuncs
  obtain f where
    f_type[type_rule]: "f : \<Omega> \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<Omega> \<times>\<^sub>c \<nat>\<^sub>c" and
    f_def: "f = \<langle>IMPLIES \<circ>\<^sub>c \<langle>left_cart_proj \<Omega> \<nat>\<^sub>c, p \<circ>\<^sub>c successor \<circ>\<^sub>c right_cart_proj \<Omega> \<nat>\<^sub>c\<rangle>, successor \<circ>\<^sub>c right_cart_proj \<Omega> \<nat>\<^sub>c\<rangle>"
    by typecheck_cfuncs

  obtain induct_p where
    induct_p_type[type_rule]: "induct_p : \<nat>\<^sub>c \<rightarrow> \<Omega> \<times>\<^sub>c \<nat>\<^sub>c" and
    induct_p_zero: "induct_p \<circ>\<^sub>c zero = q" and
    induct_p_successor: "induct_p \<circ>\<^sub>c successor = f \<circ>\<^sub>c induct_p"
    by (typecheck_cfuncs, metis natural_number_object_property2)

  have "right_cart_proj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c induct_p = id \<nat>\<^sub>c"
  proof (etcs_rule natural_number_object_func_unique[where f=successor])
    show "(right_cart_proj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c induct_p) \<circ>\<^sub>c zero = id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
      by (etcs_assocr, etcs_subst induct_p_zero, unfold q_def, etcs_subst right_cart_proj_cfunc_prod id_left_unit2, simp)
    show "(right_cart_proj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c induct_p) \<circ>\<^sub>c successor = successor \<circ>\<^sub>c right_cart_proj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c induct_p"
      by (etcs_assocr, etcs_subst induct_p_successor, unfold f_def, etcs_assocl, etcs_subst right_cart_proj_cfunc_prod, simp)
    show "id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor = successor \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c"
      by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2)
  qed
 
  have "left_cart_proj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c induct_p = p"
    proof (etcs_rule natural_number_object_func_unique[where f="id \<Omega>"])

thm type_rule

thm inverse_image_mapping_type

find_theorems "quotient_func ?f ?R \<circ>\<^sub>c ?h = ?P"

(* consider cases for ?f \<circ>\<^sub>c ?g (associate right)
  id\<^sub>c ?X (id_right_unit2, id_left_unit2)
  left_cart_proj ?X ?Y (left_cart_proj_cfunc_prod, left_cart_proj_cfunc_cross_prod)
  right_cart_proj ?X ?Y (right_cart_proj_cfunc_prod, right_cart_proj_cfunc_cross_prod)
  \<langle>?f,?g\<rangle> (cfunc_prod_comp)
  diagonal ?X (diag_on_elements)
  ?f \<times>\<^sub>f ?g (cfunc_cross_prod_comp_cfunc_prod, cfunc_cross_prod_comp_cfunc_cross_prod)
  swap ?X ?Y (swap_ap, swap_cross_prod)
  associate_right ?X ?Y ?Z (associate_right_ap, associate_right_crossprod_ap)
  associate_left ?X ?Y ?Z (associate_left_ap, associate_left_crossprod_ap)
  distribute_right_left ?X ?Y ?Z (distribute_right_left_ap)
  distribute_right_right ?X ?Y ?Z (distribute_right_right_ap)
  distribute_right ?X ?Y ?Z (distribute_right_ap)
  distribute_left_left ?X ?Y ?Z (distribute_left_left_ap)
  distribute_left_right ?X ?Y ?Z (distribute_left_right_ap)
  distribute_left ?X ?Y ?Z (distribute_left_ap)
  outers ?A ?B ?C ?D (outers_apply)
  inners ?A ?B ?C ?D (inners_apply)
  lefts ?A ?B ?C ?D (lefts_apply)
  rights ?A ?B ?C ?D (rights_apply)
  \<beta>\<^bsub>?X\<^esub> (terminal_func_comp)
  inverse_image_mapping ?f ?B ?m
  [?f\<^sup>-\<^sup>1[?B]\<^bsub>?m\<^esub>]map
  fibered_product_morphism ?X ?f ?g ?Y
  fibered_product_left_proj ?X ?f ?g ?Y
  fibered_product_right_proj ?X ?f ?g ?Y
  \<t>
  \<f>
  characteristic_func ?m (characteristic_func_eq, complement_morphism_eq) (TODO:does these work in assocr?)
  eq_pred ?X (eq_pred_square, eq_pred_of_monomorphism, eq_pred_left_coproj2, eq_pred_right_coproj2, eq_pred_left_coproj, eq_pred_right_coproj)
  fiber_morphism ?f ?y
  ?m\<^sup>c
  equiv_class ?R
  quotient_func ?f ?R (quotient_func_eq)
  ?f\<restriction>\<^bsub>(?A, ?n)\<^esub>
  [?f[?A]\<^bsub>?n\<^esub>]map
  left_coproj ?X ?Y
  right_coproj ?X ?Y
  ?f \<amalg> ?g
  dist_prod_coprod ?A ?B ?C
  dist_prod_coprod_inv ?A ?B ?C
  ?f \<bowtie>\<^sub>f ?g
  case_bool
  dist_prod_coprod2 ?A ?B ?C
  dist_prod_coprod_inv2 ?A ?B ?C
  into_super ?m : ?X \<Coprod> (?Y \<setminus> (?X, ?m)) \<rightarrow> ?Y
  try_cast ?m : ?Y \<rightarrow> ?X \<Coprod> (?Y \<setminus> (?X, ?m))
  NOT
  AND
  NOR
  OR
  XOR
  NAND
  IFF
  IMPLIES
  \<alpha>\<^bsub>?X\<^esub>
  eval_func ?X ?A
  ?f\<^sup>\<sharp>
  ?g\<^bsup>?A\<^esup>\<^sub>f
  ?f\<^sup>\<flat>
  ?metafunc ?f
  ?k\<^bsub>[?p,-]\<^esub>
  ?k\<^bsub>[-,?q]\<^esub>
  FORALL ?X
  EXISTS ?X
  zero
  successor
  predecessor
  add1
  add2
  ?m +\<^sub>\<nat> ?n
  leq *)

method etcs_eval = ((etcs_assocr, etcs_subst sharp_comp)
        | (etcs_assocr, etcs_subst terminal_func_comp)
        | (etcs_assocr, etcs_subst cfunc_prod_comp)
        | (etcs_subst true_beta_one)
        | (drule cart_prod_decomp, clarify)
        | (etcs_subst cfunc_cross_prod_comp_cfunc_prod)
        | (etcs_subst_asm cfunc_cross_prod_comp_cfunc_prod)
        | (etcs_subst left_cart_proj_cfunc_prod)
        | (etcs_subst right_cart_proj_cfunc_prod)
        | (etcs_subst_asm left_cart_proj_cfunc_prod)
        | (etcs_subst_asm right_cart_proj_cfunc_prod)
        | (etcs_subst id_left_unit2)
        | (etcs_subst id_right_unit2)
        | (etcs_subst_asm id_left_unit2)
        | (etcs_subst_asm id_right_unit2)
        | (etcs_subst comp_one_id)
        | (etcs_subst_asm comp_one_id))+
thm all_true_implies_FORALL_true
method etcs2hol = 
    (((etcs_rule ETCS_bool_eq_implies, (simp_all)?)
     | (etcs_rule ETCS_bool_eq_implies', (simp_all)?))?,
        (((etcs_assocr)?, etcs_subst sharp_comp)
        | ((etcs_assocr)?, etcs_subst terminal_func_comp)
        | (etcs_rule all_true_implies_FORALL_true)
        | (etcs_rule all_true_implies_FORALL_true2)
        | ((etcs_assocr)?, etcs_subst cfunc_prod_comp)
        (*| ((etcs_assocr_asm)?, etcs_subst_asm cfunc_prod_comp)*)
        | (etcs_subst true_beta_one)
        | (etcs_rule implies_implies_IMPLIES)
        | (etcs_subst sym[OF eq_pred_iff_eq])
        | (etcs_subst_asm sym[OF eq_pred_iff_eq])
        | (drule cart_prod_decomp, clarify)
        | (etcs_subst cfunc_cross_prod_comp_cfunc_prod)
        | (etcs_subst_asm cfunc_cross_prod_comp_cfunc_prod)
        | (etcs_subst left_cart_proj_cfunc_prod)
        | (etcs_subst right_cart_proj_cfunc_prod)
        | (etcs_subst_asm left_cart_proj_cfunc_prod)
        | (etcs_subst_asm right_cart_proj_cfunc_prod)
        | ((etcs_assocr)?, etcs_subst cfunc_cross_prod_comp_cfunc_prod)
        | (etcs_subst id_left_unit2)
        | (etcs_subst id_right_unit2)
        | (etcs_subst_asm id_left_unit2)
        | (etcs_subst_asm id_right_unit2)
        | (etcs_subst comp_one_id)
        | (etcs_subst_asm comp_one_id)
        | (etcs_rule all_true_implies_FORALL_true3)
        | (etcs_subst_asm sharp_comp)
        (*| ((etcs_assocr_asm)?, etcs_erule FORALL_elim)*))+)

(*
apply ((etcs_assocr, etcs_subst sharp_comp)
        | (etcs_assocr, etcs_subst terminal_func_comp)
        | (etcs_rule all_true_implies_FORALL_true2)
        | (etcs_assocr, etcs_subst cfunc_prod_comp)
        | (etcs_subst true_beta_one)
        | (etcs_rule implies_implies_IMPLIES)
        | (etcs_subst sym[OF eq_pred_iff_eq])
        | (etcs_subst_asm sym[OF eq_pred_iff_eq])
        | (drule cart_prod_decomp, clarify)
        | (etcs_subst cfunc_cross_prod_comp_cfunc_prod)
        | (etcs_subst_asm cfunc_cross_prod_comp_cfunc_prod)
        | (etcs_subst left_cart_proj_cfunc_prod)
        | (etcs_subst right_cart_proj_cfunc_prod)
        | (etcs_subst_asm left_cart_proj_cfunc_prod)
        | (etcs_subst_asm right_cart_proj_cfunc_prod)
        | (etcs_subst id_left_unit2)
        | (etcs_subst id_right_unit2)
        | (etcs_subst_asm id_left_unit2)
        | (etcs_subst_asm id_right_unit2)
        | (etcs_subst comp_one_id)
        | (etcs_subst_asm comp_one_id))+
*)

ML_val Subgoal.focus

lemma "n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> EXISTS \<nat>\<^sub>c \<circ>\<^sub>c ((eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, n \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one)\<^sup>\<sharp> = \<t> \<Longrightarrow> Q"
  apply (etcs_erule EXISTS_elim)

thm exE EXISTS_elim
thm conjE
thm impE
thm allE
  oops
lemma "(\<exists>x. P x) \<Longrightarrow> Q x"
  apply (erule exE)
  oops

theorem well_ordering_principle:
  assumes "nonempty A" "(A, m) \<subseteq>\<^sub>c \<nat>\<^sub>c"
  shows "\<exists> a. a \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (A, m) \<and> (\<forall> b. b \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (A, m) \<longrightarrow>  a \<le>\<^sub>\<nat> b)"
proof(cases "zero \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (A, m)")
  show "zero \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (A, m) \<Longrightarrow> \<exists>a. a \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (A, m) \<and> (\<forall>b. b \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (A, m) \<longrightarrow> a \<le>\<^sub>\<nat> b)"
    unfolding leq_infix_def using relative_member_def zero_is_smallest by blast
next
  assume no_zero: " \<not> zero \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (A, m)"
  obtain \<chi>\<^sub>A where \<chi>\<^sub>A_def: "\<chi>\<^sub>A = characteristic_func m"
    by simp
  have \<chi>\<^sub>A_type[type_rule]: "\<chi>\<^sub>A : \<nat>\<^sub>c \<rightarrow> \<Omega>"
    using assms unfolding \<chi>\<^sub>A_def subobject_of_def2 by (auto, typecheck_cfuncs)

  obtain q where q_def: "q = (right_coproj \<Omega> \<nat>\<^sub>c) \<circ>\<^sub>c zero"    (*I redefined q because we only need the special case when 0 is not an element of the set!*)
    by simp
  have q_type[type_rule]: "q : one \<rightarrow> \<Omega> \<Coprod> \<nat>\<^sub>c"
    unfolding q_def by typecheck_cfuncs

  obtain f where f_def: "f = (left_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<Omega>\<^esub>) \<amalg>
    (((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>) \<bowtie>\<^sub>f left_cart_proj \<nat>\<^sub>c one) \<circ>\<^sub>c
  dist_prod_coprod_inv \<nat>\<^sub>c one one \<circ>\<^sub>c \<langle>successor, case_bool \<circ>\<^sub>c \<chi>\<^sub>A \<circ>\<^sub>c successor\<rangle>)"
    by simp
  have f_type[type_rule]: "f : \<Omega> \<Coprod> \<nat>\<^sub>c \<rightarrow> \<Omega> \<Coprod> \<nat>\<^sub>c"
    unfolding f_def by typecheck_cfuncs

  obtain u where u_type[type_rule]: "u: \<nat>\<^sub>c \<rightarrow> \<Omega> \<Coprod> \<nat>\<^sub>c" 
            and  u_zero: "u \<circ>\<^sub>c zero = q" 
            and  u_successor: "f \<circ>\<^sub>c u = u \<circ>\<^sub>c successor"
    using natural_number_object_property2 by (typecheck_cfuncs, blast)

  have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>
          eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c, right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
          eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c, left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
    apply (etcs_rule natural_number_object_func_unique[where f="id \<Omega>"])
      apply etcs2hol
    apply (metis monomorphism_def3 q_def right_coproj_are_monomorphisms right_proj_type u_zero zero_type)
(* (right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f x) \<circ>\<^sub>c \<langle>xa,id\<^sub>c one\<rangle> = (left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f x) \<circ>\<^sub>c \<langle>xa,id\<^sub>c one\<rangle> *)
       apply (etcs2hol)
      apply (metis monomorphism_def3 q_def right_coproj_are_monomorphisms right_proj_type u_zero zero_type)
    apply (etcs2hol)
    apply etcs_assocr_asm
      apply (etcs_subst_asm sharp_comp)
    thm FORALL_elim
      apply (etcs_erule FORALL_elim)
      apply etcs_assocr_asm
      apply (etcs2hol)
    thm IMPLIES_elim'
      apply (etcs_erule IMPLIES_elim')
       apply (etcs2hol)
    
    apply (erule_tac x=xa in FORALL_elim)
        apply (typecheck_cfuncs)
       apply (meson cfunc_cross_prod_type comp_type, simp)
    apply (etcs2hol)
  proof -
    fix x xa
    assume x_type[type_rule]: "x \<in>\<^sub>c \<nat>\<^sub>c" and xa_type[type_rule]: "xa \<in>\<^sub>c \<nat>\<^sub>c"
    obtain p where p_def: "p = (IMPLIES \<circ>\<^sub>c
         \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c
          \<langle>u \<circ>\<^sub>c
           right_cart_proj \<nat>\<^sub>c
            \<nat>\<^sub>c,right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c
                 left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c
        id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor \<circ>\<^sub>c x"
      by auto
    have p_type: "p : \<nat>\<^sub>c \<times>\<^sub>c one \<rightarrow> \<Omega>"
      unfolding p_def by typecheck_cfuncs
    
    have FORALL_elim'': "\<And>P x. FORALL \<nat>\<^sub>c \<circ>\<^sub>c p\<^sup>\<sharp> = \<t> \<Longrightarrow> x \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (p \<circ>\<^sub>c \<langle>x,id\<^sub>c one\<rangle> = \<t> \<Longrightarrow> P) \<Longrightarrow> P"
      using FORALL_elim' p_type xa_type by auto

    show "
       u \<circ>\<^sub>c x = right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c xa \<Longrightarrow>
       FORALL \<nat>\<^sub>c \<circ>\<^sub>c
       ((IMPLIES \<circ>\<^sub>c
         \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c
          \<langle>u \<circ>\<^sub>c
           right_cart_proj \<nat>\<^sub>c
            \<nat>\<^sub>c,right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c
                 left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c
        id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f successor \<circ>\<^sub>c x)\<^sup>\<sharp> =
       \<t> \<Longrightarrow>
       x \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> xa \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> x = xa"
       apply (fold p_def)
       apply (erule_tac x=xa in FORALL_elim'', simp)

    apply etcs2hol
    thm FORALL_elim allE
    apply (erule_tac x=xa in FORALL_elim)
    thm cfunc_prod_comp
    thm implies_implies_IMPLIES
    thm true_beta_one
    thm sym[OF eq_pred_iff_eq]
    thm comp_one_id


    show "(FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c  \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                                         eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c  zero =
      (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero"
      apply (etcs_assocr)
      thm  all_true_implies_FORALL_true sharp_comp
      apply (etcs_rule all_true_implies_FORALL_true2)
        proof - 
          have "(FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c  \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                                         eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c  zero  = 
          FORALL \<nat>\<^sub>c \<circ>\<^sub>c ((IMPLIES \<circ>\<^sub>c  \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
                                         eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)  \<circ>\<^sub>c  (id \<nat>\<^sub>c \<times>\<^sub>f zero))\<^sup>\<sharp>"
            by (typecheck_cfuncs, smt (z3) comp_associative2 sharp_comp)
          also have "... = \<t> \<circ>\<^sub>c \<beta>\<^bsub>one\<^esub>"
          proof(rule all_true_implies_FORALL_true2)
            show "(IMPLIES \<circ>\<^sub>c \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c
                      id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero : \<nat>\<^sub>c \<times>\<^sub>c one \<rightarrow> \<Omega>"
              by typecheck_cfuncs
            show "\<And> n_one. n_one \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c one \<Longrightarrow>
          ((IMPLIES \<circ>\<^sub>c \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c  id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero) \<circ>\<^sub>c
                     n_one = \<t>"
            proof - 
              fix n_one 
              assume n_one_type[type_rule]: "n_one \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c one"
              then obtain n where n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c" and n_def: "n_one = \<langle>n, id one\<rangle>"
                by (typecheck_cfuncs, metis cart_prod_decomp one_unique_element)
              have "((IMPLIES \<circ>\<^sub>c \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c  id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero) \<circ>\<^sub>c
                     n_one = 
                    (IMPLIES \<circ>\<^sub>c \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c  (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero) \<circ>\<^sub>c
                     n_one"
                using comp_associative2 by (typecheck_cfuncs, force)
              also have "... = (IMPLIES \<circ>\<^sub>c \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c  \<langle>n, zero\<rangle>"
                by (typecheck_cfuncs, smt (z3) cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2 id_type n_def)
              also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c  \<langle>n, zero\<rangle>"
                by (typecheck_cfuncs, simp add: comp_associative2)
              also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c ,right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c  \<langle>n, zero\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c  \<langle>n, zero\<rangle>\<rangle> "
                by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2)
              also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>n, zero\<rangle>,right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>n, zero\<rangle>\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>n, zero\<rangle>,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>n, zero\<rangle>\<rangle> \<rangle> "
                using cfunc_prod_comp comp_associative2 by (typecheck_cfuncs, force)
              also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u \<circ>\<^sub>c zero,right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero, n\<rangle> \<rangle>"
                using left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod by (typecheck_cfuncs, presburger)
              also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c zero, right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero, n\<rangle>\<rangle>"
                using u_zero q_def by auto
              also have "... = IMPLIES \<circ>\<^sub>c \<langle>eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero, n\<rangle> ,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>zero, n\<rangle>\<rangle>"
                by (typecheck_cfuncs, simp add: eq_pred_right_coproj2)
              also have "... = \<t>"
                by (typecheck_cfuncs, metis IMPLIES_false_is_true_false true_false_only_truth_values)
              then show "((IMPLIES \<circ>\<^sub>c \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c  id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero) \<circ>\<^sub>c
                     n_one = \<t>"
                using calculation by auto
            qed
          qed
          also have "... = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero"
            using comp_associative2 terminal_func_comp by (typecheck_cfuncs, force)
          then show ?thesis
            using calculation by auto
    qed






    show "(FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c 
          \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
          eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor
        = id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c 
          \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
          eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>"
    proof (rule one_separator[where X="\<nat>\<^sub>c", where Y=\<Omega>])
      show "(FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,
          right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c
            successor : \<nat>\<^sub>c \<rightarrow> \<Omega>"
        by typecheck_cfuncs
      show "id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c  \<langle>u \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c
          \<nat>\<^sub>c,right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
        by typecheck_cfuncs
    next
      fix n
      assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
      show "((FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c 
          \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
          eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor) \<circ>\<^sub>c n
        = (id\<^sub>c \<Omega> \<circ>\<^sub>c FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c 
          \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
          eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c n"
      proof (cases "((FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c 
          \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
          eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor) \<circ>\<^sub>c n = \<t>")
        assume "((FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c 
          \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
          eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor) \<circ>\<^sub>c n = \<t>"
        




        then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c 
          \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
          eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c successor \<circ>\<^sub>c n = \<t>"
          by (typecheck_cfuncs_prems, smt (z3) cfunc_type_def codomain_comp comp_associative)
        then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c ((IMPLIES \<circ>\<^sub>c 
          \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
          eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f (successor \<circ>\<^sub>c n)))\<^sup>\<sharp> = \<t>"
          by (typecheck_cfuncs_prems, metis sharp_comp)
        then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c ((IMPLIES \<circ>\<^sub>c 
          \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
          eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c 
          \<langle>id \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c one, (successor \<circ>\<^sub>c n) \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one\<rangle>)\<^sup>\<sharp> = \<t>"
          by (typecheck_cfuncs, metis cfunc_cross_prod_def2)
        then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c ((IMPLIES \<circ>\<^sub>c 
          \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
          eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c 
          \<langle>left_cart_proj \<nat>\<^sub>c one, (successor \<circ>\<^sub>c n) \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one\<rangle>)\<^sup>\<sharp> = \<t>"
          by (typecheck_cfuncs, metis  id_left_unit2)
        then have "FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c 
          \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
          eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c 
          \<langle>left_cart_proj \<nat>\<^sub>c one, (successor \<circ>\<^sub>c n) \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one\<rangle>)\<^sup>\<sharp> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>one\<^esub>"
          by (typecheck_cfuncs, metis  cfunc_type_def comp_associative id_right_unit2 id_type one_unique_element)
        then have "\<And> x y. x \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> y \<in>\<^sub>c one \<Longrightarrow>  IMPLIES \<circ>\<^sub>c 
          \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
          eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c 
          \<langle>left_cart_proj \<nat>\<^sub>c one, (successor \<circ>\<^sub>c n) \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c one\<rangle> \<circ>\<^sub>c \<langle>x, y\<rangle> = \<t>"
          oops
 



          find_theorems "left_cart_proj"
(*      have "(FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c 
            \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
            eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c successor
          = FORALL \<nat>\<^sub>c \<circ>\<^sub>c ((IMPLIES \<circ>\<^sub>c 
            \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>,
            eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f successor))\<^sup>\<sharp>"
        by (typecheck_cfuncs, smt (z3) comp_associative2 sharp_comp)
      also have "... = FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c 
            \<langle>(eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f successor),
            (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c,left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f successor)\<rangle>)\<^sup>\<sharp>"
        by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2)
      also have "... = FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c 
            \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>(u \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f successor), 
              (right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f successor)\<rangle>,
            eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f successor), left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f successor)\<rangle>\<rangle>)\<^sup>\<sharp>"
        by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2)
      also have "... = FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c 
            \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>(u \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f successor), 
              (right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f successor)\<rangle>,
            eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c , left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>)\<^sup>\<sharp>"*)

  have "\<And>n. n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> u \<circ>\<^sub>c n = right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c n \<or> (\<exists> \<omega>. \<omega> \<in>\<^sub>c \<Omega> \<and> u \<circ>\<^sub>c n = left_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c \<omega>)"
  proof auto
    fix n
    assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"

  obtain q' where q'_def: "q' = \<langle>\<t>, zero\<rangle>"   (*I redefined q' because we only need the special case when 0 is not an element of the set!*)
    by simp
  have q'_type[type_rule]: "q' : one \<rightarrow> \<Omega> \<times>\<^sub>c \<nat>\<^sub>c"
    unfolding q'_def by typecheck_cfuncs


  
  obtain f' where f'_def: "f' = \<langle>
        AND \<circ>\<^sub>c \<langle>left_cart_proj \<Omega> \<nat>\<^sub>c, \<chi>\<^sub>A \<circ>\<^sub>c successor \<circ>\<^sub>c right_cart_proj \<Omega> \<nat>\<^sub>c\<rangle>, 
        successor \<circ>\<^sub>c right_cart_proj \<Omega> \<nat>\<^sub>c
      \<rangle>"
    by simp
  have f'_type[type_rule]: "f' : \<Omega> \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<Omega> \<times>\<^sub>c \<nat>\<^sub>c"
    unfolding f'_def by typecheck_cfuncs

  obtain v1 where v1_def: "v1 = \<langle>FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>leq, NOT \<circ>\<^sub>c \<chi>\<^sub>A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>, id \<nat>\<^sub>c\<rangle>"
    by simp
  have v1_type[type_rule]: "v1 : \<nat>\<^sub>c \<rightarrow> \<Omega> \<times>\<^sub>c \<nat>\<^sub>c"
    unfolding v1_def by typecheck_cfuncs

  have v1z_eqs_q': "v1 \<circ>\<^sub>c zero = q'"
  proof - 
    have f1: "(FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>leq, NOT \<circ>\<^sub>c \<chi>\<^sub>A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c zero = \<t>"
    proof - 
      have "(FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>leq, NOT \<circ>\<^sub>c \<chi>\<^sub>A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c zero
          = FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>leq, NOT \<circ>\<^sub>c \<chi>\<^sub>A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c zero"
        by (typecheck_cfuncs, smt comp_associative2)
      also have "... = FORALL \<nat>\<^sub>c \<circ>\<^sub>c((IMPLIES \<circ>\<^sub>c \<langle>leq, NOT \<circ>\<^sub>c \<chi>\<^sub>A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c (id (\<nat>\<^sub>c) \<times>\<^sub>f zero))\<^sup>\<sharp>"
        by (typecheck_cfuncs, metis sharp_comp)
      also have "... = \<t> \<circ>\<^sub>c \<beta>\<^bsub>one\<^esub>"
      proof(rule all_true_implies_FORALL_true2)
        show "(IMPLIES \<circ>\<^sub>c \<langle>leq,NOT \<circ>\<^sub>c \<chi>\<^sub>A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero : \<nat>\<^sub>c \<times>\<^sub>c one \<rightarrow> \<Omega>"
          by typecheck_cfuncs
      next  
        show "\<And>xy. xy \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c one \<Longrightarrow> ((IMPLIES \<circ>\<^sub>c \<langle>leq,NOT \<circ>\<^sub>c \<chi>\<^sub>A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero) \<circ>\<^sub>c xy = \<t>"
        proof - 
          fix n_one
          assume n_one_type[type_rule]: "n_one \<in>\<^sub>c \<nat>\<^sub>c \<times>\<^sub>c one"
          obtain n where n_def: "n_one = \<langle>n,id(one)\<rangle>" and n_type: "n \<in>\<^sub>c \<nat>\<^sub>c"
            by (metis cart_prod_decomp id_type n_one_type terminal_func_unique)
          have "((IMPLIES \<circ>\<^sub>c \<langle>leq,NOT \<circ>\<^sub>c \<chi>\<^sub>A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero) \<circ>\<^sub>c n_one = 
                 (IMPLIES \<circ>\<^sub>c \<langle>leq,NOT \<circ>\<^sub>c \<chi>\<^sub>A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c (id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero) \<circ>\<^sub>c n_one"
            by (typecheck_cfuncs, metis cfunc_type_def comp_associative)
          also have "... = (IMPLIES \<circ>\<^sub>c \<langle>leq,NOT \<circ>\<^sub>c \<chi>\<^sub>A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c \<langle>n, zero\<rangle>"
            by (typecheck_cfuncs, smt (z3) cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2 id_type n_def n_type)
          also have "... =  IMPLIES \<circ>\<^sub>c \<langle>leq,NOT \<circ>\<^sub>c \<chi>\<^sub>A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c \<langle>n, zero\<rangle>"
            by (typecheck_cfuncs, metis comp_associative2 n_type)
          also have "... =  IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>n, zero\<rangle> ,NOT \<circ>\<^sub>c \<chi>\<^sub>A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n, zero\<rangle> \<rangle>"
            by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2 n_type)
          also have "... =  IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>n, zero\<rangle> ,NOT \<circ>\<^sub>c \<chi>\<^sub>A \<circ>\<^sub>c zero\<rangle>"
            using n_type right_cart_proj_cfunc_prod by (typecheck_cfuncs, presburger)
          also have "... =  IMPLIES \<circ>\<^sub>c \<langle>leq \<circ>\<^sub>c \<langle>n, zero\<rangle> ,\<t>\<rangle>"
            by (typecheck_cfuncs, metis NOT_false_is_true \<chi>\<^sub>A_def assms(2) characteristic_func_true_relative_member no_zero subobject_of_def2 true_false_only_truth_values)
          also have "... =  \<t>"
            by (typecheck_cfuncs, metis IMPLIES_false_is_true_false n_type true_false_only_truth_values)
          then show "((IMPLIES \<circ>\<^sub>c \<langle>leq,NOT \<circ>\<^sub>c \<chi>\<^sub>A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>) \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c \<times>\<^sub>f zero) \<circ>\<^sub>c n_one = \<t>"
            by (simp add: calculation)
        qed
      qed
      also have "... = \<t>"
        by (typecheck_cfuncs, metis id_right_unit2 id_type one_unique_element)
      then show ?thesis
        using calculation by auto
    qed
    have "v1 \<circ>\<^sub>c zero = \<langle>(FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>leq, NOT \<circ>\<^sub>c \<chi>\<^sub>A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>) \<circ>\<^sub>c zero, id \<nat>\<^sub>c \<circ>\<^sub>c zero \<rangle>"
      using cfunc_prod_comp v1_def by (typecheck_cfuncs, blast)
    also have "... = q'"
      by (typecheck_cfuncs, simp add: f1 id_left_unit2 q'_def)
    then show ?thesis
      by (simp add: calculation)
  qed



  obtain v2 where v2_def: "v2 = \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u, right_coproj \<Omega> \<nat>\<^sub>c\<rangle>, id \<nat>\<^sub>c \<rangle>"
    by simp
  have v2_type[type_rule]: "v2 : \<nat>\<^sub>c \<rightarrow> \<Omega> \<times>\<^sub>c \<nat>\<^sub>c"
    unfolding v2_def by typecheck_cfuncs


  have v2z_eqs_q': "v2 \<circ>\<^sub>c zero = q'"
  proof - 
    have "v2 \<circ>\<^sub>c zero  = \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u, right_coproj \<Omega> \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c zero , zero\<rangle>"
      by (typecheck_cfuncs, smt (verit, best) cfunc_prod_comp comp_associative2 comp_type id_left_unit2 id_type v2_def)
    also have " ... = \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u \<circ>\<^sub>c zero , right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c zero\<rangle>  , zero\<rangle>"
      by (typecheck_cfuncs, simp add: cfunc_prod_comp)
    also have " ... = \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c zero , right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c zero\<rangle>  , zero\<rangle>"
      by (simp add: q_def u_zero)
    also have "... = \<langle>\<t>  , zero\<rangle>"
      by (typecheck_cfuncs, metis eq_pred_iff_eq)
    then show ?thesis
      by (simp add: calculation q'_def)
  qed






  have "v1 = v2"
  proof (rule natural_number_object_func_unique[where X="\<Omega> \<times>\<^sub>c \<nat>\<^sub>c", where f=f'])
    show "v1 : \<nat>\<^sub>c \<rightarrow> \<Omega> \<times>\<^sub>c \<nat>\<^sub>c" "v2 : \<nat>\<^sub>c \<rightarrow> \<Omega> \<times>\<^sub>c \<nat>\<^sub>c" "f' : \<Omega> \<times>\<^sub>c \<nat>\<^sub>c \<rightarrow> \<Omega> \<times>\<^sub>c \<nat>\<^sub>c"
      by (typecheck_cfuncs, presburger)

    show "v1 \<circ>\<^sub>c zero = v2 \<circ>\<^sub>c zero"
      by (simp add: v1z_eqs_q' v2z_eqs_q')

    show "v1 \<circ>\<^sub>c successor = f' \<circ>\<^sub>c v1"
      sorry

    show "v2 \<circ>\<^sub>c successor = f' \<circ>\<^sub>c v2"
    proof(rule one_separator[where X = "\<nat>\<^sub>c", where Y = "\<Omega> \<times>\<^sub>c \<nat>\<^sub>c"])
      show "v2 \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<Omega> \<times>\<^sub>c \<nat>\<^sub>c" "f' \<circ>\<^sub>c v2 : \<nat>\<^sub>c \<rightarrow> \<Omega> \<times>\<^sub>c \<nat>\<^sub>c"
        by (typecheck_cfuncs, presburger)
      show "\<And>n. n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> (v2 \<circ>\<^sub>c successor) \<circ>\<^sub>c n = (f' \<circ>\<^sub>c v2) \<circ>\<^sub>c n"
      proof - 
        fix n
        assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c" 
      (*  assume case1: "u \<circ>\<^sub>c  n = right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c  n"    (*This is an assumption to try to make the calculations fall out easier*)
*)


        have "(v2 \<circ>\<^sub>c successor) \<circ>\<^sub>c n = v2 \<circ>\<^sub>c (successor  \<circ>\<^sub>c n)"
          by (typecheck_cfuncs, simp add: comp_associative2)
        also have "... = \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u, right_coproj \<Omega> \<nat>\<^sub>c\<rangle>  \<circ>\<^sub>c (successor  \<circ>\<^sub>c n), id \<nat>\<^sub>c  \<circ>\<^sub>c (successor  \<circ>\<^sub>c n)\<rangle>"
          by (typecheck_cfuncs, smt (verit, best) cfunc_prod_comp comp_associative2 comp_type v2_def) 
        also have "... = \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u \<circ>\<^sub>c (successor  \<circ>\<^sub>c n), right_coproj \<Omega> \<nat>\<^sub>c  \<circ>\<^sub>c (successor  \<circ>\<^sub>c n) \<rangle>  ,  (successor  \<circ>\<^sub>c n)\<rangle>"
          using cfunc_prod_comp id_left_unit2 by (typecheck_cfuncs, force)
        also have "... = \<langle>((\<f>  \<circ>\<^sub>c \<beta>\<^bsub>\<Omega>\<^esub>) \<amalg> (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c , (successor  \<circ>\<^sub>c n)  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>)) \<circ>\<^sub>c u \<circ>\<^sub>c (successor  \<circ>\<^sub>c n) ,  (successor  \<circ>\<^sub>c n)\<rangle>"
          using eq_pred_right_coproj by (typecheck_cfuncs, presburger)
        also have "... = \<langle>((\<f>  \<circ>\<^sub>c \<beta>\<^bsub>\<Omega>\<^esub>) \<amalg> (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c , (successor  \<circ>\<^sub>c n)  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>)) \<circ>\<^sub>c (f \<circ>\<^sub>c u \<circ>\<^sub>c n) ,  (successor  \<circ>\<^sub>c n)\<rangle>"
          by (typecheck_cfuncs, simp add: comp_associative2 u_successor)
        also have "... = \<langle>(\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<Omega>\<^esub>) \<amalg> (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,(successor \<circ>\<^sub>c n) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c
            (left_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<Omega>\<^esub>) \<amalg>
            (((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c one\<^esub>) \<bowtie>\<^sub>f left_cart_proj \<nat>\<^sub>c one) \<circ>\<^sub>c dist_prod_coprod_inv \<nat>\<^sub>c one one \<circ>\<^sub>c \<langle>successor,case_bool \<circ>\<^sub>c \<chi>\<^sub>A \<circ>\<^sub>c successor\<rangle>) \<circ>\<^sub>c
              u \<circ>\<^sub>c n,successor \<circ>\<^sub>c n\<rangle>"
          unfolding f_def by simp
        also have "... = undefined"
        proof (cases "u \<circ>\<^sub>c n = right_coproj")
        (*The above follows from the newly proved lemma!*)
        thm f_def f'_def v2_def u_successor f_type \<chi>\<^sub>A_type









(*
        have "(f' \<circ>\<^sub>c v2) \<circ>\<^sub>c n = f' \<circ>\<^sub>c (v2 \<circ>\<^sub>c n)"
          by (typecheck_cfuncs, simp add: comp_associative2)
        also have "... = f' \<circ>\<^sub>c \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u, right_coproj \<Omega> \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c n , id \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>"
          unfolding v2_def by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2)
        also have "... = f' \<circ>\<^sub>c \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u \<circ>\<^sub>c n, right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>  , n\<rangle>"
          by (typecheck_cfuncs, simp add: cfunc_prod_comp id_left_unit2)
        also have "... =  \<langle>AND \<circ>\<^sub>c \<langle>left_cart_proj \<Omega> \<nat>\<^sub>c, \<chi>\<^sub>A \<circ>\<^sub>c successor \<circ>\<^sub>c right_cart_proj \<Omega> \<nat>\<^sub>c\<rangle>, 
        successor \<circ>\<^sub>c right_cart_proj \<Omega> \<nat>\<^sub>c \<rangle> \<circ>\<^sub>c \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u \<circ>\<^sub>c n, right_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>  , n\<rangle>"
          using f'_def by force
        also have "... =  \<langle>AND \<circ>\<^sub>c \<langle>left_cart_proj \<Omega> \<nat>\<^sub>c, \<chi>\<^sub>A \<circ>\<^sub>c successor \<circ>\<^sub>c right_cart_proj \<Omega> \<nat>\<^sub>c\<rangle>, 
        successor \<circ>\<^sub>c right_cart_proj \<Omega> \<nat>\<^sub>c \<rangle> \<circ>\<^sub>c \<langle>((\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<Omega>\<^esub>) \<amalg> (eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>id \<nat>\<^sub>c , n \<circ>\<^sub>c \<beta>\<^bsub> \<nat>\<^sub>c\<^esub>\<rangle>)) \<circ>\<^sub>c (u \<circ>\<^sub>c n)   , n\<rangle>"
          using eq_pred_right_coproj by (typecheck_cfuncs, presburger)
        (*The above follows from the newly proved lemma!*)
*)





  qed
  then have "\<And> n. n \<in>\<^sub>c \<nat>\<^sub>c \<Longrightarrow> u \<circ>\<^sub>c n = left_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c n \<equiv> (\<forall>n'. n' \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> n' \<le>\<^sub>\<nat> n \<longrightarrow> \<not> n' \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (A, m))"
  proof -
    fix n
    assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"

    have "\<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u,right_coproj \<Omega> \<nat>\<^sub>c\<rangle>,id\<^sub>c \<nat>\<^sub>c\<rangle> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<equiv> u \<circ>\<^sub>c n = left_coproj \<Omega> \<nat>\<^sub>c \<circ>\<^sub>c n"
      sorry

    have "\<langle>FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>leq,NOT \<circ>\<^sub>c \<chi>\<^sub>A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>,id\<^sub>c \<nat>\<^sub>c\<rangle> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> 
          \<equiv> 
        (\<forall>n'. n' \<in>\<^sub>c \<nat>\<^sub>c \<longrightarrow> n' \<le>\<^sub>\<nat> n \<longrightarrow> \<not> n' \<in>\<^bsub>\<nat>\<^sub>c\<^esub> (A, m))"
      sorry

    assume "v1 = v2"
    then have "\<langle>FORALL \<nat>\<^sub>c \<circ>\<^sub>c (IMPLIES \<circ>\<^sub>c \<langle>leq,NOT \<circ>\<^sub>c \<chi>\<^sub>A \<circ>\<^sub>c right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c\<rangle>)\<^sup>\<sharp>,id\<^sub>c \<nat>\<^sub>c\<rangle> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> 
          \<equiv>
        \<langle>eq_pred (\<Omega> \<Coprod> \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>u,right_coproj \<Omega> \<nat>\<^sub>c\<rangle>,id\<^sub>c \<nat>\<^sub>c\<rangle> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
      unfolding v1_def v2_def by auto
    
end