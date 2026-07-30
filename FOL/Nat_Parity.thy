section \<open>Natural Number Parity and Halving\<close>

theory Nat_Parity
  imports Nats Quant_Logic
begin

subsection \<open>Nth Even Number\<close>

text \<open>HOL's @{text "THE u. ..."} definition is replaced by axiomatizing @{text nth_even} directly
  off the defining spec, whose existence-and-uniqueness follows from
  @{thm natural_number_object_property2} -- the same conservative-extension technique used for
  @{text ITER_curried} in @{text Nats.thy}.\<close>
axiomatization nth_even :: "cfunc" where
  nth_even_spec: "nth_even : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<and> nth_even \<circ>\<^sub>c zero = zero \<and>
    (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even = nth_even \<circ>\<^sub>c successor"

lemma nth_even_def2:
  "nth_even: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<and> nth_even \<circ>\<^sub>c zero = zero \<and> (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even = nth_even \<circ>\<^sub>c successor"
  using nth_even_spec .

lemma nth_even_type[type_rule]:
  "nth_even: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
  using nth_even_def2 by auto

lemma nth_even_zero:
  "nth_even \<circ>\<^sub>c zero = zero"
  using nth_even_def2 by auto

lemma nth_even_successor:
  "nth_even \<circ>\<^sub>c successor = (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even"
  using nth_even_def2 by auto

lemma nth_even_successor2:
  "nth_even \<circ>\<^sub>c successor = successor \<circ>\<^sub>c successor \<circ>\<^sub>c nth_even"
proof -
  have "nth_even \<circ>\<^sub>c successor = (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even"
    by (rule nth_even_successor)
  also have "... = successor \<circ>\<^sub>c successor \<circ>\<^sub>c nth_even"
    by (rule sym[OF comp_associative2[OF nth_even_type successor_type successor_type]])
  finally show ?thesis .
qed

subsection \<open>Nth Odd Number\<close>

axiomatization nth_odd :: "cfunc" where
  nth_odd_spec: "nth_odd : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<and> nth_odd \<circ>\<^sub>c zero = successor \<circ>\<^sub>c zero \<and>
    (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_odd = nth_odd \<circ>\<^sub>c successor"

lemma nth_odd_def2:
  "nth_odd: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<and> nth_odd \<circ>\<^sub>c zero = successor \<circ>\<^sub>c zero \<and> (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_odd = nth_odd \<circ>\<^sub>c successor"
  using nth_odd_spec .

lemma nth_odd_type[type_rule]:
  "nth_odd: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
  using nth_odd_def2 by auto

lemma nth_odd_zero:
  "nth_odd \<circ>\<^sub>c zero = successor \<circ>\<^sub>c zero"
  using nth_odd_def2 by auto

lemma nth_odd_successor:
  "nth_odd \<circ>\<^sub>c successor = (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_odd"
  using nth_odd_def2 by auto

lemma nth_odd_successor2:
  "nth_odd \<circ>\<^sub>c successor = successor \<circ>\<^sub>c successor \<circ>\<^sub>c nth_odd"
proof -
  have "nth_odd \<circ>\<^sub>c successor = (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_odd"
    by (rule nth_odd_successor)
  also have "... = successor \<circ>\<^sub>c successor \<circ>\<^sub>c nth_odd"
    by (rule sym[OF comp_associative2[OF nth_odd_type successor_type successor_type]])
  finally show ?thesis .
qed

lemma nth_odd_is_succ_nth_even:
  "nth_odd = successor \<circ>\<^sub>c nth_even"
proof (etcs_rule natural_number_object_func_unique[where X="\<nat>\<^sub>c", where f="successor \<circ>\<^sub>c successor"])
  show "nth_odd \<circ>\<^sub>c zero = (successor \<circ>\<^sub>c nth_even) \<circ>\<^sub>c zero"
  proof -
    have s1: "nth_odd \<circ>\<^sub>c zero = successor \<circ>\<^sub>c zero" by (rule nth_odd_zero)
    have s2: "(successor \<circ>\<^sub>c nth_even) \<circ>\<^sub>c zero = successor \<circ>\<^sub>c (nth_even \<circ>\<^sub>c zero)"
      by (rule sym[OF comp_associative2[OF zero_type nth_even_type successor_type]])
    have s3: "successor \<circ>\<^sub>c (nth_even \<circ>\<^sub>c zero) = successor \<circ>\<^sub>c zero"
      using nth_even_zero by simp
    show ?thesis using s1 s2 s3 by simp
  qed

  show "nth_odd \<circ>\<^sub>c successor = (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_odd"
    by (rule nth_odd_successor)

  show "(successor \<circ>\<^sub>c nth_even) \<circ>\<^sub>c successor = (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c successor \<circ>\<^sub>c nth_even"
  proof -
    have succ_nth_even_type[type_rule]: "successor \<circ>\<^sub>c nth_even : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" by typecheck_cfuncs
    have t1: "(successor \<circ>\<^sub>c nth_even) \<circ>\<^sub>c successor = successor \<circ>\<^sub>c (nth_even \<circ>\<^sub>c successor)"
      by (rule sym[OF comp_associative2[OF successor_type nth_even_type successor_type]])
    have t2: "successor \<circ>\<^sub>c (nth_even \<circ>\<^sub>c successor) = successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c nth_even"
      using nth_even_successor2 by simp
    have t3: "successor \<circ>\<^sub>c successor \<circ>\<^sub>c successor \<circ>\<^sub>c nth_even = (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c successor \<circ>\<^sub>c nth_even"
      by (rule comp_associative2[OF succ_nth_even_type successor_type successor_type])
    show ?thesis using t1 t2 t3 by simp
  qed
qed

text \<open>HOL derives this by induction; here it follows directly from
  @{thm nth_odd_is_succ_nth_even} and @{thm nth_even_successor}, with no induction needed.\<close>
lemma succ_nth_odd_is_nth_even_succ:
  "successor \<circ>\<^sub>c nth_odd = nth_even \<circ>\<^sub>c successor"
proof -
  have s1: "successor \<circ>\<^sub>c nth_odd = successor \<circ>\<^sub>c successor \<circ>\<^sub>c nth_even"
    using nth_odd_is_succ_nth_even by simp
  have s2: "successor \<circ>\<^sub>c successor \<circ>\<^sub>c nth_even = (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even"
    by (rule comp_associative2[OF nth_even_type successor_type successor_type])
  have s3: "nth_even \<circ>\<^sub>c successor = (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even"
    by (rule nth_even_successor)
  show ?thesis using s1 s2 s3 by simp
qed

subsection \<open>Checking if a Number is Even\<close>

axiomatization is_even :: "cfunc" where
  is_even_spec: "is_even : \<nat>\<^sub>c \<rightarrow> \<Omega> \<and> is_even \<circ>\<^sub>c zero = \<t> \<and> NOT \<circ>\<^sub>c is_even = is_even \<circ>\<^sub>c successor"

lemma is_even_def2:
  "is_even : \<nat>\<^sub>c \<rightarrow> \<Omega> \<and> is_even \<circ>\<^sub>c zero = \<t> \<and> NOT \<circ>\<^sub>c is_even = is_even \<circ>\<^sub>c successor"
  using is_even_spec .

lemma is_even_type[type_rule]:
  "is_even : \<nat>\<^sub>c \<rightarrow> \<Omega>"
  using is_even_def2 by auto

lemma is_even_zero:
  "is_even \<circ>\<^sub>c zero = \<t>"
  using is_even_def2 by auto

lemma is_even_successor:
  "is_even \<circ>\<^sub>c successor = NOT \<circ>\<^sub>c is_even"
  using is_even_def2 by auto

subsection \<open>Checking if a Number is Odd\<close>

axiomatization is_odd :: "cfunc" where
  is_odd_spec: "is_odd : \<nat>\<^sub>c \<rightarrow> \<Omega> \<and> is_odd \<circ>\<^sub>c zero = \<f> \<and> NOT \<circ>\<^sub>c is_odd = is_odd \<circ>\<^sub>c successor"

lemma is_odd_def2:
  "is_odd : \<nat>\<^sub>c \<rightarrow> \<Omega> \<and> is_odd \<circ>\<^sub>c zero = \<f> \<and> NOT \<circ>\<^sub>c is_odd = is_odd \<circ>\<^sub>c successor"
  using is_odd_spec .

lemma is_odd_type[type_rule]:
  "is_odd : \<nat>\<^sub>c \<rightarrow> \<Omega>"
  using is_odd_def2 by auto

lemma is_odd_zero:
  "is_odd \<circ>\<^sub>c zero = \<f>"
  using is_odd_def2 by auto

lemma is_odd_successor:
  "is_odd \<circ>\<^sub>c successor = NOT \<circ>\<^sub>c is_odd"
  using is_odd_def2 by auto

lemma is_even_not_is_odd:
  "is_even = NOT \<circ>\<^sub>c is_odd"
proof (etcs_rule natural_number_object_func_unique[where X="\<Omega>", where f="NOT"])
  show "is_even \<circ>\<^sub>c zero = (NOT \<circ>\<^sub>c is_odd) \<circ>\<^sub>c zero"
  proof -
    have s1: "(NOT \<circ>\<^sub>c is_odd) \<circ>\<^sub>c zero = NOT \<circ>\<^sub>c (is_odd \<circ>\<^sub>c zero)"
      by (rule sym[OF comp_associative2[OF zero_type is_odd_type NOT_type]])
    have s2: "is_odd \<circ>\<^sub>c zero = \<f>" by (rule is_odd_zero)
    have s3: "NOT \<circ>\<^sub>c \<f> = \<t>" by (rule NOT_false_is_true)
    have s4: "is_even \<circ>\<^sub>c zero = \<t>" by (rule is_even_zero)
    show ?thesis using s1 s2 s3 s4 by simp
  qed

  show "is_even \<circ>\<^sub>c successor = NOT \<circ>\<^sub>c is_even"
    by (rule is_even_successor)

  show "(NOT \<circ>\<^sub>c is_odd) \<circ>\<^sub>c successor = NOT \<circ>\<^sub>c NOT \<circ>\<^sub>c is_odd"
  proof -
    have s1: "(NOT \<circ>\<^sub>c is_odd) \<circ>\<^sub>c successor = NOT \<circ>\<^sub>c (is_odd \<circ>\<^sub>c successor)"
      by (rule sym[OF comp_associative2[OF successor_type is_odd_type NOT_type]])
    have s2: "is_odd \<circ>\<^sub>c successor = NOT \<circ>\<^sub>c is_odd" by (rule is_odd_successor)
    show ?thesis using s1 s2 by simp
  qed
qed

lemma is_odd_not_is_even:
  "is_odd = NOT \<circ>\<^sub>c is_even"
proof (etcs_rule natural_number_object_func_unique[where X="\<Omega>", where f="NOT"])
  show "is_odd \<circ>\<^sub>c zero = (NOT \<circ>\<^sub>c is_even) \<circ>\<^sub>c zero"
  proof -
    have s1: "(NOT \<circ>\<^sub>c is_even) \<circ>\<^sub>c zero = NOT \<circ>\<^sub>c (is_even \<circ>\<^sub>c zero)"
      by (rule sym[OF comp_associative2[OF zero_type is_even_type NOT_type]])
    have s2: "is_even \<circ>\<^sub>c zero = \<t>" by (rule is_even_zero)
    have s3: "NOT \<circ>\<^sub>c \<t> = \<f>" by (rule NOT_true_is_false)
    have s4: "is_odd \<circ>\<^sub>c zero = \<f>" by (rule is_odd_zero)
    show ?thesis using s1 s2 s3 s4 by simp
  qed

  show "is_odd \<circ>\<^sub>c successor = NOT \<circ>\<^sub>c is_odd"
    by (rule is_odd_successor)

  show "(NOT \<circ>\<^sub>c is_even) \<circ>\<^sub>c successor = NOT \<circ>\<^sub>c NOT \<circ>\<^sub>c is_even"
  proof -
    have s1: "(NOT \<circ>\<^sub>c is_even) \<circ>\<^sub>c successor = NOT \<circ>\<^sub>c (is_even \<circ>\<^sub>c successor)"
      by (rule sym[OF comp_associative2[OF successor_type is_even_type NOT_type]])
    have s2: "is_even \<circ>\<^sub>c successor = NOT \<circ>\<^sub>c is_even" by (rule is_even_successor)
    show ?thesis using s1 s2 by simp
  qed
qed

text \<open>Reusable double-negation-cancellation facts, replacing HOL's ad hoc re-derivations of the
  same content at each call site.\<close>
lemma NOT_NOT_is_even: "NOT \<circ>\<^sub>c NOT \<circ>\<^sub>c is_even = is_even"
proof -
  have h1: "NOT \<circ>\<^sub>c is_even = is_odd" by (rule sym[OF is_odd_not_is_even])
  have h2: "NOT \<circ>\<^sub>c is_odd = is_even" by (rule sym[OF is_even_not_is_odd])
  show ?thesis using h1 h2 by simp
qed

lemma NOT_NOT_is_odd: "NOT \<circ>\<^sub>c NOT \<circ>\<^sub>c is_odd = is_odd"
proof -
  have h1: "NOT \<circ>\<^sub>c is_odd = is_even" by (rule sym[OF is_even_not_is_odd])
  have h2: "NOT \<circ>\<^sub>c is_even = is_odd" by (rule sym[OF is_odd_not_is_even])
  show ?thesis using h1 h2 by simp
qed

lemma not_even_and_odd:
  assumes m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c"
  shows "\<not>(is_even \<circ>\<^sub>c m = \<t> \<and> is_odd \<circ>\<^sub>c m = \<t>)"
proof
  assume contra: "is_even \<circ>\<^sub>c m = \<t> \<and> is_odd \<circ>\<^sub>c m = \<t>"
  have iem: "is_even \<circ>\<^sub>c m = \<t>" using contra by simp
  have iom: "is_odd \<circ>\<^sub>c m = \<t>" using contra by simp
  have s1: "(NOT \<circ>\<^sub>c is_odd) \<circ>\<^sub>c m = NOT \<circ>\<^sub>c (is_odd \<circ>\<^sub>c m)"
    by (rule sym[OF comp_associative2[OF m_type is_odd_type NOT_type]])
  have s2: "NOT \<circ>\<^sub>c (is_odd \<circ>\<^sub>c m) = NOT \<circ>\<^sub>c \<t>" using iom by simp
  have s3: "NOT \<circ>\<^sub>c \<t> = \<f>" by (rule NOT_true_is_false)
  have s4: "is_even \<circ>\<^sub>c m = (NOT \<circ>\<^sub>c is_odd) \<circ>\<^sub>c m" using is_even_not_is_odd by simp
  have "\<t> = \<f>" using iem s4 s1 s2 s3 by simp
  then show False using true_false_distinct by simp
qed

lemma even_or_odd:
  assumes n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "is_even \<circ>\<^sub>c n = \<t> \<or> is_odd \<circ>\<^sub>c n = \<t>"
proof (rule ccontr)
  assume contra: "\<not> (is_even \<circ>\<^sub>c n = \<t> \<or> is_odd \<circ>\<^sub>c n = \<t>)"
  have ien_type[type_rule]: "is_even \<circ>\<^sub>c n \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
  have ion_type[type_rule]: "is_odd \<circ>\<^sub>c n \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
  have ien_ne: "is_even \<circ>\<^sub>c n \<noteq> \<t>" using contra by auto
  have ion_ne: "is_odd \<circ>\<^sub>c n \<noteq> \<t>" using contra by auto
  have ien_f: "is_even \<circ>\<^sub>c n = \<f>" using true_false_only_truth_values[OF ien_type] ien_ne by auto
  have ion_f: "is_odd \<circ>\<^sub>c n = \<f>" using true_false_only_truth_values[OF ion_type] ion_ne by auto
  have s1: "(NOT \<circ>\<^sub>c is_odd) \<circ>\<^sub>c n = NOT \<circ>\<^sub>c (is_odd \<circ>\<^sub>c n)"
    by (rule sym[OF comp_associative2[OF n_type is_odd_type NOT_type]])
  have s2: "NOT \<circ>\<^sub>c (is_odd \<circ>\<^sub>c n) = NOT \<circ>\<^sub>c \<f>" using ion_f by simp
  have s3: "NOT \<circ>\<^sub>c \<f> = \<t>" by (rule NOT_false_is_true)
  have s4: "is_even \<circ>\<^sub>c n = (NOT \<circ>\<^sub>c is_odd) \<circ>\<^sub>c n" using is_even_not_is_odd by simp
  have "\<f> = \<t>" using ien_f s4 s1 s2 s3 by simp
  then show False using true_false_distinct by simp
qed

text \<open>Reusable facts about @{text "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"}/@{text "\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"} composed with @{text zero}/
  @{text successor}, factored out since several downstream lemmas need the same fact.\<close>
lemma t_beta_N_zero: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero = \<t>"
proof -
  have s1: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero = \<t> \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c zero)"
    by (rule sym[OF comp_associative2[OF zero_type terminal_func_type true_func_type]])
  have s2: "\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c zero = id(\<one>)" by (rule terminal_func_comp_elem[OF zero_type])
  have s3: "\<t> \<circ>\<^sub>c id(\<one>) = \<t>" by (rule id_right_unit2[OF true_func_type])
  show ?thesis using s1 s2 s3 by simp
qed

lemma t_beta_N_succ: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor = id(\<Omega>) \<circ>\<^sub>c \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
proof -
  have s1: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor = \<t> \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor)"
    by (rule sym[OF comp_associative2[OF successor_type terminal_func_type true_func_type]])
  have s2: "\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor = \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>" by (rule terminal_func_comp[OF successor_type])
  have tb_type[type_rule]: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> : \<nat>\<^sub>c \<rightarrow> \<Omega>" by typecheck_cfuncs
  have s3: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> = id(\<Omega>) \<circ>\<^sub>c (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>)" by (rule sym[OF id_left_unit2[OF tb_type]])
  show ?thesis using s1 s2 s3 by simp
qed

lemma is_even_nth_even_true:
  "is_even \<circ>\<^sub>c nth_even = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
proof (etcs_rule natural_number_object_func_unique[where f="id(\<Omega>)", where X="\<Omega>"])
  show "(is_even \<circ>\<^sub>c nth_even) \<circ>\<^sub>c zero = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero"
  proof -
    have "(is_even \<circ>\<^sub>c nth_even) \<circ>\<^sub>c zero = is_even \<circ>\<^sub>c (nth_even \<circ>\<^sub>c zero)"
      by (rule sym[OF comp_associative2[OF zero_type nth_even_type is_even_type]])
    also have "... = is_even \<circ>\<^sub>c zero" using nth_even_zero by simp
    also have "... = \<t>" using is_even_zero by simp
    also have "... = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero" using t_beta_N_zero by simp
    finally show ?thesis .
  qed

  show "(is_even \<circ>\<^sub>c nth_even) \<circ>\<^sub>c successor = id(\<Omega>) \<circ>\<^sub>c is_even \<circ>\<^sub>c nth_even"
  proof -
    have succ_succ_type[type_rule]: "successor \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" by typecheck_cfuncs
    have "(is_even \<circ>\<^sub>c nth_even) \<circ>\<^sub>c successor = is_even \<circ>\<^sub>c (nth_even \<circ>\<^sub>c successor)"
      by (rule sym[OF comp_associative2[OF successor_type nth_even_type is_even_type]])
    also have "... = is_even \<circ>\<^sub>c ((successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even)"
      using nth_even_successor by simp
    also have "... = (is_even \<circ>\<^sub>c (successor \<circ>\<^sub>c successor)) \<circ>\<^sub>c nth_even"
      using comp_associative2[OF nth_even_type succ_succ_type is_even_type] by simp
    also have "... = ((is_even \<circ>\<^sub>c successor) \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even"
      using comp_associative2[OF successor_type successor_type is_even_type] by simp
    also have "... = ((NOT \<circ>\<^sub>c is_even) \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even"
      using is_even_successor by simp
    also have "... = (NOT \<circ>\<^sub>c (is_even \<circ>\<^sub>c successor)) \<circ>\<^sub>c nth_even"
      using comp_associative2[OF successor_type is_even_type NOT_type] by simp
    also have "... = (NOT \<circ>\<^sub>c (NOT \<circ>\<^sub>c is_even)) \<circ>\<^sub>c nth_even"
      using is_even_successor by simp
    also have "... = is_even \<circ>\<^sub>c nth_even"
      using NOT_NOT_is_even by simp
    also have "... = id(\<Omega>) \<circ>\<^sub>c (is_even \<circ>\<^sub>c nth_even)"
    proof -
      have ien_nte_type[type_rule]: "is_even \<circ>\<^sub>c nth_even : \<nat>\<^sub>c \<rightarrow> \<Omega>" by typecheck_cfuncs
      show ?thesis by (rule sym[OF id_left_unit2[OF ien_nte_type]])
    qed
    finally show ?thesis .
  qed

  show "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor = id(\<Omega>) \<circ>\<^sub>c \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
    by (rule t_beta_N_succ)
qed

lemma is_odd_nth_odd_true:
  "is_odd \<circ>\<^sub>c nth_odd = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
proof (etcs_rule natural_number_object_func_unique[where f="id(\<Omega>)", where X="\<Omega>"])
  show "(is_odd \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c zero = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero"
  proof -
    have "(is_odd \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c zero = is_odd \<circ>\<^sub>c (nth_odd \<circ>\<^sub>c zero)"
      by (rule sym[OF comp_associative2[OF zero_type nth_odd_type is_odd_type]])
    also have "... = is_odd \<circ>\<^sub>c (successor \<circ>\<^sub>c zero)" using nth_odd_zero by simp
    also have "... = (is_odd \<circ>\<^sub>c successor) \<circ>\<^sub>c zero"
      by (rule comp_associative2[OF zero_type successor_type is_odd_type])
    also have "... = (NOT \<circ>\<^sub>c is_odd) \<circ>\<^sub>c zero" using is_odd_successor by simp
    also have "... = NOT \<circ>\<^sub>c (is_odd \<circ>\<^sub>c zero)"
      by (rule sym[OF comp_associative2[OF zero_type is_odd_type NOT_type]])
    also have "... = NOT \<circ>\<^sub>c \<f>" using is_odd_zero by simp
    also have "... = \<t>" by (rule NOT_false_is_true)
    also have "... = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero" using t_beta_N_zero by simp
    finally show ?thesis .
  qed

  show "(is_odd \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c successor = id(\<Omega>) \<circ>\<^sub>c is_odd \<circ>\<^sub>c nth_odd"
  proof -
    have succ_succ_type[type_rule]: "successor \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" by typecheck_cfuncs
    have "(is_odd \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c successor = is_odd \<circ>\<^sub>c (nth_odd \<circ>\<^sub>c successor)"
      by (rule sym[OF comp_associative2[OF successor_type nth_odd_type is_odd_type]])
    also have "... = is_odd \<circ>\<^sub>c ((successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_odd)"
      using nth_odd_successor by simp
    also have "... = (is_odd \<circ>\<^sub>c (successor \<circ>\<^sub>c successor)) \<circ>\<^sub>c nth_odd"
      using comp_associative2[OF nth_odd_type succ_succ_type is_odd_type] by simp
    also have "... = ((is_odd \<circ>\<^sub>c successor) \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_odd"
      using comp_associative2[OF successor_type successor_type is_odd_type] by simp
    also have "... = ((NOT \<circ>\<^sub>c is_odd) \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_odd"
      using is_odd_successor by simp
    also have "... = (NOT \<circ>\<^sub>c (is_odd \<circ>\<^sub>c successor)) \<circ>\<^sub>c nth_odd"
      using comp_associative2[OF successor_type is_odd_type NOT_type] by simp
    also have "... = (NOT \<circ>\<^sub>c (NOT \<circ>\<^sub>c is_odd)) \<circ>\<^sub>c nth_odd"
      using is_odd_successor by simp
    also have "... = is_odd \<circ>\<^sub>c nth_odd"
      using NOT_NOT_is_odd by simp
    also have "... = id(\<Omega>) \<circ>\<^sub>c (is_odd \<circ>\<^sub>c nth_odd)"
    proof -
      have iod_nto_type[type_rule]: "is_odd \<circ>\<^sub>c nth_odd : \<nat>\<^sub>c \<rightarrow> \<Omega>" by typecheck_cfuncs
      show ?thesis by (rule sym[OF id_left_unit2[OF iod_nto_type]])
    qed
    finally show ?thesis .
  qed

  show "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c successor = id(\<Omega>) \<circ>\<^sub>c \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
    by (rule t_beta_N_succ)
qed

lemma is_odd_nth_even_false:
  "is_odd \<circ>\<^sub>c nth_even = \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
proof -
  have s1: "is_odd \<circ>\<^sub>c nth_even = (NOT \<circ>\<^sub>c is_even) \<circ>\<^sub>c nth_even"
    using is_odd_not_is_even by simp
  have s2: "(NOT \<circ>\<^sub>c is_even) \<circ>\<^sub>c nth_even = NOT \<circ>\<^sub>c (is_even \<circ>\<^sub>c nth_even)"
    by (rule sym[OF comp_associative2[OF nth_even_type is_even_type NOT_type]])
  have s3: "is_even \<circ>\<^sub>c nth_even = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>" by (rule is_even_nth_even_true)
  have s4: "NOT \<circ>\<^sub>c (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) = (NOT \<circ>\<^sub>c \<t>) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
    by (rule comp_associative2[OF terminal_func_type true_func_type NOT_type])
  have s5: "NOT \<circ>\<^sub>c \<t> = \<f>" by (rule NOT_true_is_false)
  show ?thesis using s1 s2 s3 s4 s5 by simp
qed

lemma is_even_nth_odd_false:
  "is_even \<circ>\<^sub>c nth_odd = \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
proof -
  have s1: "is_even \<circ>\<^sub>c nth_odd = (NOT \<circ>\<^sub>c is_odd) \<circ>\<^sub>c nth_odd"
    using is_even_not_is_odd by simp
  have s2: "(NOT \<circ>\<^sub>c is_odd) \<circ>\<^sub>c nth_odd = NOT \<circ>\<^sub>c (is_odd \<circ>\<^sub>c nth_odd)"
    by (rule sym[OF comp_associative2[OF nth_odd_type is_odd_type NOT_type]])
  have s3: "is_odd \<circ>\<^sub>c nth_odd = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>" by (rule is_odd_nth_odd_true)
  have s4: "NOT \<circ>\<^sub>c (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) = (NOT \<circ>\<^sub>c \<t>) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
    by (rule comp_associative2[OF terminal_func_type true_func_type NOT_type])
  have s5: "NOT \<circ>\<^sub>c \<t> = \<f>" by (rule NOT_true_is_false)
  show ?thesis using s1 s2 s3 s4 s5 by simp
qed

lemma EXISTS_zero_nth_even:
  "(EXISTS(\<nat>\<^sub>c) \<circ>\<^sub>c (eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c nth_even \<times>\<^sub>f id(\<nat>\<^sub>c))\<^sup>\<sharp>) \<circ>\<^sub>c zero = \<t>"
proof -
  have zb_type[type_rule]: "zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" by typecheck_cfuncs
  have lcp_type[type_rule]: "left_cart_proj(\<nat>\<^sub>c, \<one>) : \<nat>\<^sub>c \<times>\<^sub>c \<one> \<rightarrow> \<nat>\<^sub>c" by typecheck_cfuncs
  have rcp_type[type_rule]: "right_cart_proj(\<nat>\<^sub>c, \<one>) : \<nat>\<^sub>c \<times>\<^sub>c \<one> \<rightarrow> \<one>" by typecheck_cfuncs
  have pair_type[type_rule]: "\<langle>nth_even, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c" by typecheck_cfuncs

  have "(EXISTS(\<nat>\<^sub>c) \<circ>\<^sub>c (eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c nth_even \<times>\<^sub>f id(\<nat>\<^sub>c))\<^sup>\<sharp>) \<circ>\<^sub>c zero
      = EXISTS(\<nat>\<^sub>c) \<circ>\<^sub>c ((eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c nth_even \<times>\<^sub>f id(\<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c zero)"
    by (typecheck_cfuncs, simp add: comp_associative2)
  also have "... = EXISTS(\<nat>\<^sub>c) \<circ>\<^sub>c (eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c (nth_even \<times>\<^sub>f id(\<nat>\<^sub>c)) \<circ>\<^sub>c (id(\<nat>\<^sub>c) \<times>\<^sub>f zero))\<^sup>\<sharp>"
    by (typecheck_cfuncs, simp add: comp_associative2 sharp_comp)
  also have "... = EXISTS(\<nat>\<^sub>c) \<circ>\<^sub>c (eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c (nth_even \<times>\<^sub>f zero))\<^sup>\<sharp>"
    by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_cross_prod id_left_unit2 id_right_unit2)
  also have "... = EXISTS(\<nat>\<^sub>c) \<circ>\<^sub>c (eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>nth_even \<circ>\<^sub>c left_cart_proj(\<nat>\<^sub>c, \<one>), zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<one>\<^esub>\<rangle>)\<^sup>\<sharp>"
  proof -
    have s1: "nth_even \<times>\<^sub>f zero = \<langle>nth_even \<circ>\<^sub>c left_cart_proj(\<nat>\<^sub>c, \<one>), zero \<circ>\<^sub>c right_cart_proj(\<nat>\<^sub>c, \<one>)\<rangle>"
      by (rule cfunc_cross_prod_def2[OF nth_even_type zero_type])
    have s2: "right_cart_proj(\<nat>\<^sub>c, \<one>) = \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<one>\<^esub>" by (rule terminal_func_unique[OF rcp_type])
    show ?thesis using s1 s2 by simp
  qed
  also have "... = EXISTS(\<nat>\<^sub>c) \<circ>\<^sub>c (eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>nth_even \<circ>\<^sub>c left_cart_proj(\<nat>\<^sub>c, \<one>), (zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c left_cart_proj(\<nat>\<^sub>c, \<one>)\<rangle>)\<^sup>\<sharp>"
  proof -
    have s1: "\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c left_cart_proj(\<nat>\<^sub>c, \<one>) = \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<one>\<^esub>" by (rule terminal_func_comp[OF lcp_type])
    have s2: "(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c left_cart_proj(\<nat>\<^sub>c, \<one>) = zero \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c left_cart_proj(\<nat>\<^sub>c, \<one>))"
      by (rule sym[OF comp_associative2[OF lcp_type terminal_func_type zero_type]])
    show ?thesis using s1 s2 by simp
  qed
  also have "... = EXISTS(\<nat>\<^sub>c) \<circ>\<^sub>c ((eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>nth_even, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj(\<nat>\<^sub>c, \<one>))\<^sup>\<sharp>"
  proof -
    have s1: "\<langle>nth_even, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj(\<nat>\<^sub>c, \<one>) = \<langle>nth_even \<circ>\<^sub>c left_cart_proj(\<nat>\<^sub>c, \<one>), (zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c left_cart_proj(\<nat>\<^sub>c, \<one>)\<rangle>"
      by (rule cfunc_prod_comp[OF lcp_type nth_even_type zb_type])
    have s2: "eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c (\<langle>nth_even, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj(\<nat>\<^sub>c, \<one>))
        = (eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>nth_even, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj(\<nat>\<^sub>c, \<one>)"
      by (rule comp_associative2[OF lcp_type pair_type eq_pred_type])
    show ?thesis using s1 s2 by simp
  qed
  also have "... = \<t>"
  proof (rule exists_true_implies_EXISTS_true)
    show p_type: "eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>nth_even, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
      by typecheck_cfuncs
    show "\<exists>x. x \<in>\<^sub>c \<nat>\<^sub>c \<and> (eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>nth_even, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c x = \<t>"
    proof (intro exI[where x=zero], intro conjI[OF zero_type])
      have s1: "\<langle>nth_even,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c zero = \<langle>nth_even \<circ>\<^sub>c zero, (zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero\<rangle>"
        by (rule cfunc_prod_comp[OF zero_type nth_even_type zb_type])
      have s2: "(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero = zero \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c zero)"
        by (rule sym[OF comp_associative2[OF zero_type terminal_func_type zero_type]])
      have s3: "\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c zero = id(\<one>)" by (rule terminal_func_comp_elem[OF zero_type])
      have s4: "zero \<circ>\<^sub>c id(\<one>) = zero" by (rule id_right_unit2[OF zero_type])
      have s5: "(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero = zero" using s2 s3 s4 by simp
      have s6: "\<langle>nth_even,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c zero = \<langle>nth_even \<circ>\<^sub>c zero, zero\<rangle>"
        using s1 s5 by simp
      have s7: "(eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>nth_even,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c zero = eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>nth_even \<circ>\<^sub>c zero, zero\<rangle>"
        using comp_associative2[OF zero_type pair_type eq_pred_type] s6 by simp
      have nez_type[type_rule]: "nth_even \<circ>\<^sub>c zero \<in>\<^sub>c \<nat>\<^sub>c" by typecheck_cfuncs
      have s8: "(nth_even \<circ>\<^sub>c zero = zero) \<longleftrightarrow> (eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>nth_even \<circ>\<^sub>c zero, zero\<rangle> = \<t>)"
        by (rule eq_pred_iff_eq[OF nez_type zero_type])
      show "(eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>nth_even,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c zero = \<t>"
        using s7 s8 nth_even_zero by auto
    qed
  qed
  finally show ?thesis .
qed

lemma not_EXISTS_zero_nth_odd:
  "(EXISTS(\<nat>\<^sub>c) \<circ>\<^sub>c (eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c nth_odd \<times>\<^sub>f id(\<nat>\<^sub>c))\<^sup>\<sharp>) \<circ>\<^sub>c zero = \<f>"
proof -
  have zb_type[type_rule]: "zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" by typecheck_cfuncs
  have lcp_type[type_rule]: "left_cart_proj(\<nat>\<^sub>c, \<one>) : \<nat>\<^sub>c \<times>\<^sub>c \<one> \<rightarrow> \<nat>\<^sub>c" by typecheck_cfuncs
  have rcp_type[type_rule]: "right_cart_proj(\<nat>\<^sub>c, \<one>) : \<nat>\<^sub>c \<times>\<^sub>c \<one> \<rightarrow> \<one>" by typecheck_cfuncs
  have pair_type[type_rule]: "\<langle>nth_odd, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c" by typecheck_cfuncs

  have "(EXISTS(\<nat>\<^sub>c) \<circ>\<^sub>c (eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c nth_odd \<times>\<^sub>f id(\<nat>\<^sub>c))\<^sup>\<sharp>) \<circ>\<^sub>c zero
      = EXISTS(\<nat>\<^sub>c) \<circ>\<^sub>c ((eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c nth_odd \<times>\<^sub>f id(\<nat>\<^sub>c))\<^sup>\<sharp> \<circ>\<^sub>c zero)"
    by (typecheck_cfuncs, simp add: comp_associative2)
  also have "... = EXISTS(\<nat>\<^sub>c) \<circ>\<^sub>c (eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c (nth_odd \<times>\<^sub>f id(\<nat>\<^sub>c)) \<circ>\<^sub>c (id(\<nat>\<^sub>c) \<times>\<^sub>f zero))\<^sup>\<sharp>"
    by (typecheck_cfuncs, simp add: comp_associative2 sharp_comp)
  also have "... = EXISTS(\<nat>\<^sub>c) \<circ>\<^sub>c (eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c (nth_odd \<times>\<^sub>f zero))\<^sup>\<sharp>"
    by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_cross_prod id_left_unit2 id_right_unit2)
  also have "... = EXISTS(\<nat>\<^sub>c) \<circ>\<^sub>c (eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>nth_odd \<circ>\<^sub>c left_cart_proj(\<nat>\<^sub>c, \<one>), zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<one>\<^esub>\<rangle>)\<^sup>\<sharp>"
  proof -
    have s1: "nth_odd \<times>\<^sub>f zero = \<langle>nth_odd \<circ>\<^sub>c left_cart_proj(\<nat>\<^sub>c, \<one>), zero \<circ>\<^sub>c right_cart_proj(\<nat>\<^sub>c, \<one>)\<rangle>"
      by (rule cfunc_cross_prod_def2[OF nth_odd_type zero_type])
    have s2: "right_cart_proj(\<nat>\<^sub>c, \<one>) = \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<one>\<^esub>" by (rule terminal_func_unique[OF rcp_type])
    show ?thesis using s1 s2 by simp
  qed
  also have "... = EXISTS(\<nat>\<^sub>c) \<circ>\<^sub>c (eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>nth_odd \<circ>\<^sub>c left_cart_proj(\<nat>\<^sub>c, \<one>), (zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c left_cart_proj(\<nat>\<^sub>c, \<one>)\<rangle>)\<^sup>\<sharp>"
  proof -
    have s1: "\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c left_cart_proj(\<nat>\<^sub>c, \<one>) = \<beta>\<^bsub>\<nat>\<^sub>c \<times>\<^sub>c \<one>\<^esub>" by (rule terminal_func_comp[OF lcp_type])
    have s2: "(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c left_cart_proj(\<nat>\<^sub>c, \<one>) = zero \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c left_cart_proj(\<nat>\<^sub>c, \<one>))"
      by (rule sym[OF comp_associative2[OF lcp_type terminal_func_type zero_type]])
    show ?thesis using s1 s2 by simp
  qed
  also have "... = EXISTS(\<nat>\<^sub>c) \<circ>\<^sub>c ((eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>nth_odd, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj(\<nat>\<^sub>c, \<one>))\<^sup>\<sharp>"
  proof -
    have s1: "\<langle>nth_odd, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj(\<nat>\<^sub>c, \<one>) = \<langle>nth_odd \<circ>\<^sub>c left_cart_proj(\<nat>\<^sub>c, \<one>), (zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c left_cart_proj(\<nat>\<^sub>c, \<one>)\<rangle>"
      by (rule cfunc_prod_comp[OF lcp_type nth_odd_type zb_type])
    have s2: "eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c (\<langle>nth_odd, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c left_cart_proj(\<nat>\<^sub>c, \<one>))
        = (eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>nth_odd, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj(\<nat>\<^sub>c, \<one>)"
      by (rule comp_associative2[OF lcp_type pair_type eq_pred_type])
    show ?thesis using s1 s2 by simp
  qed
  also have "... = \<f>"
  proof -
    have p_type[type_rule]: "eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>nth_odd, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<Omega>" by typecheck_cfuncs
    have no_witness: "\<not> (\<exists> x. x \<in>\<^sub>c \<nat>\<^sub>c \<and> (eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>nth_odd, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c x = \<t>)"
    proof clarify
      fix x
      assume x_type[type_rule]: "x \<in>\<^sub>c \<nat>\<^sub>c"
      assume assump: "(eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>nth_odd,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c x = \<t>"
      have h1: "(eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>nth_odd,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c x = eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c (\<langle>nth_odd, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c x)"
        by (rule sym[OF comp_associative2[OF x_type pair_type eq_pred_type]])
      have h2: "\<langle>nth_odd, zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> \<circ>\<^sub>c x = \<langle>nth_odd \<circ>\<^sub>c x, (zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c x\<rangle>"
        by (rule cfunc_prod_comp[OF x_type nth_odd_type zb_type])
      have h3: "(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c x = zero \<circ>\<^sub>c (\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c x)"
        by (rule sym[OF comp_associative2[OF x_type terminal_func_type zero_type]])
      have h4: "\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c x = id(\<one>)" by (rule terminal_func_comp_elem[OF x_type])
      have h5: "zero \<circ>\<^sub>c id(\<one>) = zero" by (rule id_right_unit2[OF zero_type])
      have h6: "(zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c x = zero" using h3 h4 h5 by simp
      have h7: "eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>nth_odd \<circ>\<^sub>c x, zero\<rangle> = \<t>" using assump h1 h2 h6 by simp
      have nox_type[type_rule]: "nth_odd \<circ>\<^sub>c x \<in>\<^sub>c \<nat>\<^sub>c" by typecheck_cfuncs
      have h8: "(nth_odd \<circ>\<^sub>c x = zero) \<longleftrightarrow> (eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>nth_odd \<circ>\<^sub>c x, zero\<rangle> = \<t>)"
        by (rule eq_pred_iff_eq[OF nox_type zero_type])
      have h9: "nth_odd \<circ>\<^sub>c x = zero" using h7 h8 by auto
      have h10: "nth_odd \<circ>\<^sub>c x = successor \<circ>\<^sub>c (nth_even \<circ>\<^sub>c x)"
      proof -
        have "nth_odd \<circ>\<^sub>c x = (successor \<circ>\<^sub>c nth_even) \<circ>\<^sub>c x" using nth_odd_is_succ_nth_even by simp
        also have "... = successor \<circ>\<^sub>c (nth_even \<circ>\<^sub>c x)"
          by (rule sym[OF comp_associative2[OF x_type nth_even_type successor_type]])
        finally show ?thesis .
      qed
      have h11: "zero = successor \<circ>\<^sub>c (nth_even \<circ>\<^sub>c x)" using h9 h10 by simp
      have nex_type[type_rule]: "nth_even \<circ>\<^sub>c x \<in>\<^sub>c \<nat>\<^sub>c" by typecheck_cfuncs
      show False using h11 zero_is_not_successor[OF nex_type] by simp
    qed
    have not_eq_t: "EXISTS(\<nat>\<^sub>c) \<circ>\<^sub>c ((eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>nth_odd,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj(\<nat>\<^sub>c, \<one>))\<^sup>\<sharp> \<noteq> \<t>"
    proof
      assume eq_t: "EXISTS(\<nat>\<^sub>c) \<circ>\<^sub>c ((eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>nth_odd,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj(\<nat>\<^sub>c, \<one>))\<^sup>\<sharp> = \<t>"
      obtain x where x_type: "x \<in>\<^sub>c \<nat>\<^sub>c" and px_true: "(eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>nth_odd,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c x = \<t>"
        using EXISTS_true_implies_exists_true[OF p_type eq_t] by auto
      then show False using no_witness by auto
    qed
    have goal_type[type_rule]: "EXISTS(\<nat>\<^sub>c) \<circ>\<^sub>c ((eq_pred(\<nat>\<^sub>c) \<circ>\<^sub>c \<langle>nth_odd,zero \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c left_cart_proj(\<nat>\<^sub>c, \<one>))\<^sup>\<sharp> \<in>\<^sub>c \<Omega>"
      by typecheck_cfuncs
    show ?thesis using not_eq_t true_false_only_truth_values[OF goal_type] by auto
  qed
  finally show ?thesis .
qed

subsection \<open>Natural Number Halving\<close>

axiomatization halve_with_parity :: "cfunc" where
  halve_with_parity_spec: "halve_with_parity : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c \<and>
    halve_with_parity \<circ>\<^sub>c zero = left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c zero \<and>
    (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity = halve_with_parity \<circ>\<^sub>c successor"

lemma halve_with_parity_def2:
  "halve_with_parity : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c \<and>
    halve_with_parity \<circ>\<^sub>c zero = left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c zero \<and>
    (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity = halve_with_parity \<circ>\<^sub>c successor"
  using halve_with_parity_spec .

lemma halve_with_parity_type[type_rule]:
  "halve_with_parity : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c"
  using halve_with_parity_def2 by auto

lemma halve_with_parity_zero:
  "halve_with_parity \<circ>\<^sub>c zero = left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c zero"
  using halve_with_parity_def2 by auto

lemma halve_with_parity_successor:
  "(right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity = halve_with_parity \<circ>\<^sub>c successor"
  using halve_with_parity_def2 by auto

lemma halve_with_parity_nth_even:
  "halve_with_parity \<circ>\<^sub>c nth_even = left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c)"
proof (etcs_rule natural_number_object_func_unique[where X="\<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c",
    where f="(left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor) \<amalg> (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)"])
  show "(halve_with_parity \<circ>\<^sub>c nth_even) \<circ>\<^sub>c zero = left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c zero"
  proof -
    have "(halve_with_parity \<circ>\<^sub>c nth_even) \<circ>\<^sub>c zero = halve_with_parity \<circ>\<^sub>c nth_even \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = halve_with_parity \<circ>\<^sub>c zero" by (simp add: nth_even_zero)
    also have "... = left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c zero" by (simp add: halve_with_parity_zero)
    finally show ?thesis .
  qed

  show "(halve_with_parity \<circ>\<^sub>c nth_even) \<circ>\<^sub>c successor =
      ((left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor) \<amalg> (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity \<circ>\<^sub>c nth_even"
  proof -
    have "(halve_with_parity \<circ>\<^sub>c nth_even) \<circ>\<^sub>c successor = halve_with_parity \<circ>\<^sub>c nth_even \<circ>\<^sub>c successor"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = halve_with_parity \<circ>\<^sub>c (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even"
      by (simp add: nth_even_successor)
    also have "... = ((halve_with_parity \<circ>\<^sub>c successor) \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = (((right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even"
      by (simp add: halve_with_parity_def2)
    also have "... = (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor))
        \<circ>\<^sub>c (halve_with_parity \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor))
        \<circ>\<^sub>c ((right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c nth_even"
      by (simp add: halve_with_parity_def2)
    also have "... = ((right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor))
        \<circ>\<^sub>c (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)))
        \<circ>\<^sub>c halve_with_parity \<circ>\<^sub>c nth_even"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = ((left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor) \<amalg> (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor))
        \<circ>\<^sub>c halve_with_parity \<circ>\<^sub>c nth_even"
    proof -
      have rc_type[type_rule]: "right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c" by typecheck_cfuncs
      have lc_type[type_rule]: "left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c" by typecheck_cfuncs
      have lcs_type[type_rule]: "left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c" by typecheck_cfuncs
      have rcs_type[type_rule]: "right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c" by typecheck_cfuncs
      have h_type[type_rule]: "right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor) : \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c"
        by typecheck_cfuncs
      have h_left: "(right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) = right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c)"
        by (rule left_coproj_cfunc_coprod[OF rc_type lcs_type])
      have h_right: "(right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) = left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor"
        by (rule right_coproj_cfunc_coprod[OF rc_type lcs_type])
      have hh_left: "((right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)))
          \<circ>\<^sub>c left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) = left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor"
      proof -
        have s1: "((right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)))
            \<circ>\<^sub>c left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) = (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c
            ((right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c))"
          by (rule sym[OF comp_associative2[OF lc_type h_type h_type]])
        show ?thesis using s1 h_left h_right by simp
      qed
      have hh_right: "((right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)))
          \<circ>\<^sub>c right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) = right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor"
      proof -
        have s1: "((right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)))
            \<circ>\<^sub>c right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) = (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c
            ((right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c))"
          by (rule sym[OF comp_associative2[OF rc_type h_type h_type]])
        have s2: "(right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c
            ((right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c))
            = (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)"
          using h_right by simp
        have s3: "(right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)
            = ((right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c)) \<circ>\<^sub>c successor"
          by (rule comp_associative2[OF successor_type lc_type h_type])
        have s4: "((right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c)) \<circ>\<^sub>c successor
            = right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor"
          using h_left by simp
        show ?thesis using s1 s2 s3 s4 by simp
      qed
      have hh_type[type_rule]: "(right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor))
          : \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c" by typecheck_cfuncs
      have comb: "(right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor))
          = (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor) \<amalg> (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)"
        using cfunc_coprod_unique[OF lcs_type rcs_type hh_type hh_left hh_right] by simp
      show ?thesis using comb by simp
    qed
    finally show ?thesis .
  qed

  show "left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor =
    ((left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor) \<amalg> (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c)"
    by (typecheck_cfuncs, simp add: left_coproj_cfunc_coprod)
qed

lemma halve_with_parity_nth_odd:
  "halve_with_parity \<circ>\<^sub>c nth_odd = right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c)"
proof (etcs_rule natural_number_object_func_unique[where X="\<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c",
    where f="(left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor) \<amalg> (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)"])
  show "(halve_with_parity \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c zero = right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c zero"
  proof -
    have "(halve_with_parity \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c zero = halve_with_parity \<circ>\<^sub>c nth_odd \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = halve_with_parity \<circ>\<^sub>c successor \<circ>\<^sub>c zero" by (simp add: nth_odd_def2)
    also have "... = (halve_with_parity \<circ>\<^sub>c successor) \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c zero"
      by (simp add: halve_with_parity_def2)
    also have "... = right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor) \<circ>\<^sub>c halve_with_parity \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor) \<circ>\<^sub>c left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c zero"
      by (simp add: halve_with_parity_def2)
    also have "... = (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor) \<circ>\<^sub>c left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c)) \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: left_coproj_cfunc_coprod)
    finally show ?thesis .
  qed

  show "(halve_with_parity \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c successor =
      (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor) \<amalg> (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor) \<circ>\<^sub>c halve_with_parity \<circ>\<^sub>c nth_odd"
  proof -
    have "(halve_with_parity \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c successor = halve_with_parity \<circ>\<^sub>c nth_odd \<circ>\<^sub>c successor"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = halve_with_parity \<circ>\<^sub>c (successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_odd"
      by (simp add: nth_odd_successor)
    also have "... = ((halve_with_parity \<circ>\<^sub>c successor) \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_odd"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = ((right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor) \<circ>\<^sub>c halve_with_parity)
        \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_odd"
      by (simp add: halve_with_parity_successor)
    also have "... = (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)
        \<circ>\<^sub>c (halve_with_parity \<circ>\<^sub>c successor)) \<circ>\<^sub>c nth_odd"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)
        \<circ>\<^sub>c (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor) \<circ>\<^sub>c halve_with_parity)) \<circ>\<^sub>c nth_odd"
      by (simp add: halve_with_parity_successor)
    also have "... = (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)
        \<circ>\<^sub>c right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity \<circ>\<^sub>c nth_odd"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = ((left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor) \<amalg> (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity \<circ>\<^sub>c nth_odd"
    proof -
      have rc_type[type_rule]: "right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c" by typecheck_cfuncs
      have lc_type[type_rule]: "left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c" by typecheck_cfuncs
      have lcs_type[type_rule]: "left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c" by typecheck_cfuncs
      have rcs_type[type_rule]: "right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c" by typecheck_cfuncs
      have h_type[type_rule]: "right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor) : \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c"
        by typecheck_cfuncs
      have h_left: "(right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) = right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c)"
        by (rule left_coproj_cfunc_coprod[OF rc_type lcs_type])
      have h_right: "(right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) = left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor"
        by (rule right_coproj_cfunc_coprod[OF rc_type lcs_type])
      have hh_left: "((right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)))
          \<circ>\<^sub>c left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) = left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor"
      proof -
        have s1: "((right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)))
            \<circ>\<^sub>c left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) = (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c
            ((right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c))"
          by (rule sym[OF comp_associative2[OF lc_type h_type h_type]])
        show ?thesis using s1 h_left h_right by simp
      qed
      have hh_right: "((right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)))
          \<circ>\<^sub>c right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) = right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor"
      proof -
        have s1: "((right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)))
            \<circ>\<^sub>c right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) = (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c
            ((right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c))"
          by (rule sym[OF comp_associative2[OF rc_type h_type h_type]])
        have s2: "(right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c
            ((right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c))
            = (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)"
          using h_right by simp
        have s3: "(right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)
            = ((right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c)) \<circ>\<^sub>c successor"
          by (rule comp_associative2[OF successor_type lc_type h_type])
        have s4: "((right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c)) \<circ>\<^sub>c successor
            = right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor"
          using h_left by simp
        show ?thesis using s1 s2 s3 s4 by simp
      qed
      have hh_type[type_rule]: "(right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor))
          : \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c" by typecheck_cfuncs
      have comb: "(right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor))
          = (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor) \<amalg> (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)"
        using cfunc_coprod_unique[OF lcs_type rcs_type hh_type hh_left hh_right] by simp
      show ?thesis using comb by simp
    qed
    finally show ?thesis .
  qed

  show "right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor =
      (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor) \<amalg> (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor) \<circ>\<^sub>c right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c)"
    by (typecheck_cfuncs, simp add: right_coproj_cfunc_coprod)
qed

lemma nth_even_nth_odd_halve_with_parity:
  "(nth_even \<amalg> nth_odd) \<circ>\<^sub>c halve_with_parity = id(\<nat>\<^sub>c)"
proof (etcs_rule natural_number_object_func_unique[where X="\<nat>\<^sub>c", where f="successor"])
  show "(nth_even \<amalg> nth_odd \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c zero = id(\<nat>\<^sub>c) \<circ>\<^sub>c zero"
  proof -
    have "(nth_even \<amalg> nth_odd \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c zero = nth_even \<amalg> nth_odd \<circ>\<^sub>c halve_with_parity \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = nth_even \<amalg> nth_odd \<circ>\<^sub>c left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c zero"
      by (simp add: halve_with_parity_zero)
    also have "... = (nth_even \<amalg> nth_odd \<circ>\<^sub>c left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c)) \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = nth_even \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: left_coproj_cfunc_coprod)
    also have "... = id(\<nat>\<^sub>c) \<circ>\<^sub>c zero"
      using id_left_unit2[OF zero_type] nth_even_zero by simp
    finally show ?thesis .
  qed

  show "(nth_even \<amalg> nth_odd \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c successor =
    successor \<circ>\<^sub>c nth_even \<amalg> nth_odd \<circ>\<^sub>c halve_with_parity"
  proof -
    have "(nth_even \<amalg> nth_odd \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c successor = nth_even \<amalg> nth_odd \<circ>\<^sub>c halve_with_parity \<circ>\<^sub>c successor"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = nth_even \<amalg> nth_odd \<circ>\<^sub>c right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor) \<circ>\<^sub>c halve_with_parity"
      by (simp add: halve_with_parity_successor)
    also have "... = (nth_even \<amalg> nth_odd \<circ>\<^sub>c right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = nth_odd \<amalg> (nth_even \<circ>\<^sub>c successor) \<circ>\<^sub>c halve_with_parity"
    proof -
      have ne_type[type_rule]: "nth_even : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" by typecheck_cfuncs
      have no_type[type_rule]: "nth_odd : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" by typecheck_cfuncs
      have rc_type[type_rule]: "right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c" by typecheck_cfuncs
      have lcs_type[type_rule]: "left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c" by typecheck_cfuncs
      have neno_type[type_rule]: "nth_even \<amalg> nth_odd : \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" by typecheck_cfuncs
      have e1: "(nth_even \<amalg> nth_odd) \<circ>\<^sub>c right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) = nth_odd"
        by (rule right_coproj_cfunc_coprod[OF ne_type no_type])
      have e2: "(nth_even \<amalg> nth_odd) \<circ>\<^sub>c (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor) = nth_even \<circ>\<^sub>c successor"
      proof -
        have "(nth_even \<amalg> nth_odd) \<circ>\<^sub>c (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor) = ((nth_even \<amalg> nth_odd) \<circ>\<^sub>c left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c)) \<circ>\<^sub>c successor"
          by (typecheck_cfuncs, simp add: comp_associative2)
        also have "... = nth_even \<circ>\<^sub>c successor"
          by (typecheck_cfuncs, simp add: left_coproj_cfunc_coprod)
        finally show ?thesis .
      qed
      show ?thesis using cfunc_coprod_comp[OF neno_type rc_type lcs_type] e1 e2 by simp
    qed
    also have "... = (successor \<circ>\<^sub>c nth_even) \<amalg> ((successor \<circ>\<^sub>c successor) \<circ>\<^sub>c nth_even) \<circ>\<^sub>c halve_with_parity"
      by (simp add: nth_even_successor nth_odd_is_succ_nth_even)
    also have "... = (successor \<circ>\<^sub>c nth_even) \<amalg> (successor \<circ>\<^sub>c successor \<circ>\<^sub>c nth_even) \<circ>\<^sub>c halve_with_parity"
      by (typecheck_cfuncs, simp add: comp_associative2)
    also have "... = (successor \<circ>\<^sub>c nth_even) \<amalg> (successor \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c halve_with_parity"
      by (simp add: nth_odd_is_succ_nth_even)
    also have "... = successor \<circ>\<^sub>c nth_even \<amalg> nth_odd \<circ>\<^sub>c halve_with_parity"
      by (typecheck_cfuncs, simp add: cfunc_coprod_comp comp_associative2)
    finally show ?thesis .
  qed

  show "id(\<nat>\<^sub>c) \<circ>\<^sub>c successor = successor \<circ>\<^sub>c id(\<nat>\<^sub>c)"
    using id_left_unit2[OF successor_type] id_right_unit2[OF successor_type] by simp
qed

lemma halve_with_parity_nth_even_nth_odd:
  "halve_with_parity \<circ>\<^sub>c (nth_even \<amalg> nth_odd) = id(\<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c)"
proof -
  have ne_type[type_rule]: "nth_even : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" by typecheck_cfuncs
  have no_type[type_rule]: "nth_odd : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" by typecheck_cfuncs
  have s1: "halve_with_parity \<circ>\<^sub>c (nth_even \<amalg> nth_odd) = (halve_with_parity \<circ>\<^sub>c nth_even) \<amalg> (halve_with_parity \<circ>\<^sub>c nth_odd)"
    by (rule sym[OF cfunc_coprod_comp[OF halve_with_parity_type ne_type no_type]])
  have s2: "(halve_with_parity \<circ>\<^sub>c nth_even) \<amalg> (halve_with_parity \<circ>\<^sub>c nth_odd) = left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c)"
    using halve_with_parity_nth_even halve_with_parity_nth_odd by simp
  have s3: "left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) = id(\<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c)"
    by (rule sym[OF id_coprod])
  show ?thesis using s1 s2 s3 by simp
qed

lemma even_odd_iso:
  "isomorphism(nth_even \<amalg> nth_odd)"
proof -
  have neno_type[type_rule]: "nth_even \<amalg> nth_odd : \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" by typecheck_cfuncs
  show ?thesis
    unfolding isomorphism_def3[OF neno_type]
  proof (intro exI[where x=halve_with_parity], intro conjI)
    show "halve_with_parity : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c" by (rule halve_with_parity_type)
    show "halve_with_parity \<circ>\<^sub>c nth_even \<amalg> nth_odd = id(\<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c)"
      by (rule halve_with_parity_nth_even_nth_odd)
    show "nth_even \<amalg> nth_odd \<circ>\<^sub>c halve_with_parity = id(\<nat>\<^sub>c)"
      by (rule nth_even_nth_odd_halve_with_parity)
  qed
qed

lemma halve_with_parity_iso:
  "isomorphism(halve_with_parity)"
proof -
  show ?thesis
    unfolding isomorphism_def3[OF halve_with_parity_type]
  proof (intro exI[where x="nth_even \<amalg> nth_odd"], intro conjI)
    have neno_type[type_rule]: "nth_even \<amalg> nth_odd : \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" by typecheck_cfuncs
    show "nth_even \<amalg> nth_odd : \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" by (rule neno_type)
    show "nth_even \<amalg> nth_odd \<circ>\<^sub>c halve_with_parity = id(\<nat>\<^sub>c)"
      by (rule nth_even_nth_odd_halve_with_parity)
    show "halve_with_parity \<circ>\<^sub>c nth_even \<amalg> nth_odd = id(\<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c)"
      by (rule halve_with_parity_nth_even_nth_odd)
  qed
qed

definition halve :: "cfunc" where
  "halve = (id(\<nat>\<^sub>c) \<amalg> id(\<nat>\<^sub>c)) \<circ>\<^sub>c halve_with_parity"

lemma halve_type[type_rule]:
  "halve : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
  unfolding halve_def by typecheck_cfuncs

lemma halve_nth_even:
  "halve \<circ>\<^sub>c nth_even = id(\<nat>\<^sub>c)"
proof -
  have idid_type[type_rule]: "id(\<nat>\<^sub>c) \<amalg> id(\<nat>\<^sub>c) : \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" by typecheck_cfuncs
  have s1: "halve \<circ>\<^sub>c nth_even = (id(\<nat>\<^sub>c) \<amalg> id(\<nat>\<^sub>c)) \<circ>\<^sub>c (halve_with_parity \<circ>\<^sub>c nth_even)"
    unfolding halve_def by (typecheck_cfuncs, simp add: comp_associative2)
  have s2: "halve_with_parity \<circ>\<^sub>c nth_even = left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c)" by (rule halve_with_parity_nth_even)
  have s3: "(id(\<nat>\<^sub>c) \<amalg> id(\<nat>\<^sub>c)) \<circ>\<^sub>c left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) = id(\<nat>\<^sub>c)"
    by (rule left_coproj_cfunc_coprod[OF id_type id_type])
  show ?thesis using s1 s2 s3 by simp
qed

lemma halve_nth_odd:
  "halve \<circ>\<^sub>c nth_odd = id(\<nat>\<^sub>c)"
proof -
  have idid_type[type_rule]: "id(\<nat>\<^sub>c) \<amalg> id(\<nat>\<^sub>c) : \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" by typecheck_cfuncs
  have s1: "halve \<circ>\<^sub>c nth_odd = (id(\<nat>\<^sub>c) \<amalg> id(\<nat>\<^sub>c)) \<circ>\<^sub>c (halve_with_parity \<circ>\<^sub>c nth_odd)"
    unfolding halve_def by (typecheck_cfuncs, simp add: comp_associative2)
  have s2: "halve_with_parity \<circ>\<^sub>c nth_odd = right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c)" by (rule halve_with_parity_nth_odd)
  have s3: "(id(\<nat>\<^sub>c) \<amalg> id(\<nat>\<^sub>c)) \<circ>\<^sub>c right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) = id(\<nat>\<^sub>c)"
    by (rule right_coproj_cfunc_coprod[OF id_type id_type])
  show ?thesis using s1 s2 s3 by simp
qed

lemma is_even_def3:
  "is_even = ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>)) \<circ>\<^sub>c halve_with_parity"
proof (etcs_rule natural_number_object_func_unique[where X="\<Omega>", where f="NOT"])
  show "is_even \<circ>\<^sub>c zero = ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c zero"
  proof -
    have amalg_type[type_rule]: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) : \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c \<rightarrow> \<Omega>" by typecheck_cfuncs
    have step1: "((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c zero
        = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c (halve_with_parity \<circ>\<^sub>c zero)"
      by (rule sym[OF comp_associative2[OF zero_type halve_with_parity_type amalg_type]])
    have step2: "halve_with_parity \<circ>\<^sub>c zero = left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c zero" by (rule halve_with_parity_zero)
    have "((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c zero
      = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c zero"
      using step1 step2 by simp
    also have "... = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, simp add: comp_associative2 left_coproj_cfunc_coprod)
    also have "... = \<t>" using t_beta_N_zero by simp
    also have "... = is_even \<circ>\<^sub>c zero" using is_even_zero by simp
    finally show ?thesis by simp
  qed

  show "is_even \<circ>\<^sub>c successor = NOT \<circ>\<^sub>c is_even"
    by (simp add: is_even_successor)

  show "((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c successor =
    NOT \<circ>\<^sub>c (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c halve_with_parity"
  proof -
    have "((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c successor
      = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity"
      by (typecheck_cfuncs, simp add: comp_associative2 halve_with_parity_successor)
    also have "... =
        (((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c))
          \<amalg>
        ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor))
          \<circ>\<^sub>c halve_with_parity"
    proof -
      have tb_type[type_rule]: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> : \<nat>\<^sub>c \<rightarrow> \<Omega>" by typecheck_cfuncs
      have fb_type[type_rule]: "\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> : \<nat>\<^sub>c \<rightarrow> \<Omega>" by typecheck_cfuncs
      have amalg_type[type_rule]: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) : \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c \<rightarrow> \<Omega>" by typecheck_cfuncs
      have rc_type[type_rule]: "right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c" by typecheck_cfuncs
      have lcs_type[type_rule]: "left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c" by typecheck_cfuncs
      have s1: "((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c))
          \<amalg> ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)
          = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor))"
        by (rule cfunc_coprod_comp[OF amalg_type rc_type lcs_type])
      have coprod_type[type_rule]: "right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor) : \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c"
        by typecheck_cfuncs
      have s2: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity
          = ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<amalg> (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c successor))) \<circ>\<^sub>c halve_with_parity"
        by (rule comp_associative2[OF halve_with_parity_type coprod_type amalg_type])
      show ?thesis using s1 s2 by simp
    qed
    also have "... = ((\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity"
      by (typecheck_cfuncs, simp add: comp_associative2 left_coproj_cfunc_coprod right_coproj_cfunc_coprod)
    also have "... = ((NOT \<circ>\<^sub>c \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (NOT \<circ>\<^sub>c \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor)) \<circ>\<^sub>c halve_with_parity"
      by (typecheck_cfuncs, simp add: NOT_false_is_true NOT_true_is_false comp_associative2)
    also have "... = NOT \<circ>\<^sub>c (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c halve_with_parity"
    proof -
      have tb_type[type_rule]: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> : \<nat>\<^sub>c \<rightarrow> \<Omega>" by typecheck_cfuncs
      have fb_type[type_rule]: "\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> : \<nat>\<^sub>c \<rightarrow> \<Omega>" by typecheck_cfuncs
      have amalg_type[type_rule]: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) : \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c \<rightarrow> \<Omega>" by typecheck_cfuncs
      have b0: "\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor = \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>" by (rule terminal_func_comp[OF successor_type])
      have b1: "\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor = \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>" using b0 by simp
      have s1: "NOT \<circ>\<^sub>c ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>))
          = (NOT \<circ>\<^sub>c \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (NOT \<circ>\<^sub>c \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>)"
        by (rule sym[OF cfunc_coprod_comp[OF NOT_type tb_type fb_type]])
      have amalg_type2[type_rule]: "NOT \<circ>\<^sub>c (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) : \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c \<rightarrow> \<Omega>" by typecheck_cfuncs
      have s2: "NOT \<circ>\<^sub>c ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>)) \<circ>\<^sub>c halve_with_parity
          = (NOT \<circ>\<^sub>c (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>)) \<circ>\<^sub>c halve_with_parity"
        by (typecheck_cfuncs, simp add: comp_associative2)
      show ?thesis using b1 s1 s2 by simp
    qed
    finally show ?thesis .
  qed
qed

lemma is_odd_def3:
  "is_odd = ((\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>)) \<circ>\<^sub>c halve_with_parity"
proof -
  have tb_type[type_rule]: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> : \<nat>\<^sub>c \<rightarrow> \<Omega>" by typecheck_cfuncs
  have fb_type[type_rule]: "\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> : \<nat>\<^sub>c \<rightarrow> \<Omega>" by typecheck_cfuncs
  have amalg_type[type_rule]: "(\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) : \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c \<rightarrow> \<Omega>" by typecheck_cfuncs
  have s1: "is_odd = NOT \<circ>\<^sub>c is_even" by (rule is_odd_not_is_even)
  have s2: "is_even = ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>)) \<circ>\<^sub>c halve_with_parity" by (rule is_even_def3)
  have s3: "NOT \<circ>\<^sub>c (((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>)) \<circ>\<^sub>c halve_with_parity)
      = (NOT \<circ>\<^sub>c (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>)) \<circ>\<^sub>c halve_with_parity"
    by (typecheck_cfuncs, simp add: comp_associative2)
  have s4: "NOT \<circ>\<^sub>c ((\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (\<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>)) = (NOT \<circ>\<^sub>c \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<amalg> (NOT \<circ>\<^sub>c \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>)"
    by (rule sym[OF cfunc_coprod_comp[OF NOT_type tb_type fb_type]])
  have s5: "NOT \<circ>\<^sub>c \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> = \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
  proof -
    have "NOT \<circ>\<^sub>c \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> = (NOT \<circ>\<^sub>c \<t>) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>" by (rule comp_associative2[OF terminal_func_type true_func_type NOT_type])
    also have "... = \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>" using NOT_true_is_false by simp
    finally show ?thesis .
  qed
  have s6: "NOT \<circ>\<^sub>c \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>"
  proof -
    have "NOT \<circ>\<^sub>c \<f> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> = (NOT \<circ>\<^sub>c \<f>) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>" by (rule comp_associative2[OF terminal_func_type false_func_type NOT_type])
    also have "... = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>" using NOT_false_is_true by simp
    finally show ?thesis .
  qed
  show ?thesis using s1 s2 s3 s4 s5 s6 by simp
qed

lemma nth_even_or_nth_odd:
  assumes n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(\<exists> m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> nth_even \<circ>\<^sub>c m = n) \<or> (\<exists> m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> nth_odd \<circ>\<^sub>c m = n)"
proof -
  have hwp_type[type_rule]: "halve_with_parity \<circ>\<^sub>c n \<in>\<^sub>c \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c" by typecheck_cfuncs
  have neno_type[type_rule]: "nth_even \<amalg> nth_odd : \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" by typecheck_cfuncs
  have lc_type[type_rule]: "left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c" by typecheck_cfuncs
  have rc_type[type_rule]: "right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c" by typecheck_cfuncs
  have ne_type[type_rule]: "nth_even : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" by typecheck_cfuncs
  have no_type[type_rule]: "nth_odd : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" by typecheck_cfuncs
  have "(\<exists>m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> halve_with_parity \<circ>\<^sub>c n = left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c m)
      \<or> (\<exists>m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> halve_with_parity \<circ>\<^sub>c n = right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c m)"
    by (rule coprojs_jointly_surj[OF hwp_type])
  then show ?thesis
  proof
    assume "\<exists>m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> halve_with_parity \<circ>\<^sub>c n = left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c m"
    then obtain m where m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c" and m_def: "halve_with_parity \<circ>\<^sub>c n = left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c m"
      by auto
    have s1: "((nth_even \<amalg> nth_odd) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c n = (nth_even \<amalg> nth_odd) \<circ>\<^sub>c (halve_with_parity \<circ>\<^sub>c n)"
      by (rule sym[OF comp_associative2[OF n_type halve_with_parity_type neno_type]])
    have s2: "(nth_even \<amalg> nth_odd) \<circ>\<^sub>c (halve_with_parity \<circ>\<^sub>c n) = (nth_even \<amalg> nth_odd) \<circ>\<^sub>c (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c m)"
      using m_def by simp
    have s3: "(nth_even \<amalg> nth_odd) \<circ>\<^sub>c (left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c m) = ((nth_even \<amalg> nth_odd) \<circ>\<^sub>c left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c)) \<circ>\<^sub>c m"
      by (rule comp_associative2[OF m_type lc_type neno_type])
    have s4: "(nth_even \<amalg> nth_odd) \<circ>\<^sub>c left_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) = nth_even"
      by (rule left_coproj_cfunc_coprod[OF ne_type no_type])
    have s5: "((nth_even \<amalg> nth_odd) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c n = n"
      using nth_even_nth_odd_halve_with_parity id_left_unit2[OF n_type] by simp
    have "n = nth_even \<circ>\<^sub>c m" using s1 s2 s3 s4 s5 by simp
    then show ?thesis using m_type by auto
  next
    assume "\<exists>m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> halve_with_parity \<circ>\<^sub>c n = right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c m"
    then obtain m where m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c" and m_def: "halve_with_parity \<circ>\<^sub>c n = right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c m"
      by auto
    have s1: "((nth_even \<amalg> nth_odd) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c n = (nth_even \<amalg> nth_odd) \<circ>\<^sub>c (halve_with_parity \<circ>\<^sub>c n)"
      by (rule sym[OF comp_associative2[OF n_type halve_with_parity_type neno_type]])
    have s2: "(nth_even \<amalg> nth_odd) \<circ>\<^sub>c (halve_with_parity \<circ>\<^sub>c n) = (nth_even \<amalg> nth_odd) \<circ>\<^sub>c (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c m)"
      using m_def by simp
    have s3: "(nth_even \<amalg> nth_odd) \<circ>\<^sub>c (right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) \<circ>\<^sub>c m) = ((nth_even \<amalg> nth_odd) \<circ>\<^sub>c right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c)) \<circ>\<^sub>c m"
      by (rule comp_associative2[OF m_type rc_type neno_type])
    have s4: "(nth_even \<amalg> nth_odd) \<circ>\<^sub>c right_coproj(\<nat>\<^sub>c, \<nat>\<^sub>c) = nth_odd"
      by (rule right_coproj_cfunc_coprod[OF ne_type no_type])
    have s5: "((nth_even \<amalg> nth_odd) \<circ>\<^sub>c halve_with_parity) \<circ>\<^sub>c n = n"
      using nth_even_nth_odd_halve_with_parity id_left_unit2[OF n_type] by simp
    have "n = nth_odd \<circ>\<^sub>c m" using s1 s2 s3 s4 s5 by simp
    then show ?thesis using m_type by auto
  qed
qed

lemma is_even_exists_nth_even:
  assumes ie_true: "is_even \<circ>\<^sub>c n = \<t>" and n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "\<exists>m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> n = nth_even \<circ>\<^sub>c m"
proof (rule ccontr)
  assume "\<not> (\<exists>m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> n = nth_even \<circ>\<^sub>c m)"
  then obtain m where m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c" and n_def: "n = nth_odd \<circ>\<^sub>c m"
    using n_type nth_even_or_nth_odd by blast
  have s1: "is_even \<circ>\<^sub>c nth_odd \<circ>\<^sub>c m = \<t>" using ie_true n_def by simp
  have s2: "is_even \<circ>\<^sub>c nth_odd = (NOT \<circ>\<^sub>c is_odd) \<circ>\<^sub>c nth_odd" using is_even_not_is_odd by simp
  have s3: "(NOT \<circ>\<^sub>c is_odd) \<circ>\<^sub>c nth_odd = NOT \<circ>\<^sub>c (is_odd \<circ>\<^sub>c nth_odd)"
    by (rule sym[OF comp_associative2[OF nth_odd_type is_odd_type NOT_type]])
  have s4: "is_even \<circ>\<^sub>c (nth_odd \<circ>\<^sub>c m) = (is_even \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c m"
    by (rule comp_associative2[OF m_type nth_odd_type is_even_type])
  have s5: "(is_even \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c m = \<t>" using s1 s4 by simp
  have s6: "(NOT \<circ>\<^sub>c (is_odd \<circ>\<^sub>c nth_odd)) \<circ>\<^sub>c m = \<t>" using s2 s3 s5 by simp
  have is_odd_nth_odd_type[type_rule]: "is_odd \<circ>\<^sub>c nth_odd : \<nat>\<^sub>c \<rightarrow> \<Omega>" by typecheck_cfuncs
  have notio_type[type_rule]: "NOT \<circ>\<^sub>c (is_odd \<circ>\<^sub>c nth_odd) : \<nat>\<^sub>c \<rightarrow> \<Omega>" by typecheck_cfuncs
  have s7: "(NOT \<circ>\<^sub>c (is_odd \<circ>\<^sub>c nth_odd)) \<circ>\<^sub>c m = NOT \<circ>\<^sub>c ((is_odd \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c m)"
    by (rule sym[OF comp_associative2[OF m_type is_odd_nth_odd_type NOT_type]])
  have s8: "(is_odd \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c m = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m"
  proof -
    have "(is_odd \<circ>\<^sub>c nth_odd) \<circ>\<^sub>c m = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c m" using is_odd_nth_odd_true by simp
    also have "... = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m"
      by (rule sym[OF comp_associative2[OF m_type terminal_func_type true_func_type]])
    finally show ?thesis .
  qed
  have s9: "NOT \<circ>\<^sub>c (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m) = \<t>" using s6 s7 s8 by simp
  have s10: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m = \<f>"
  proof -
    have tbm_type[type_rule]: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
    show ?thesis
    proof (rule ccontr)
      assume "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m \<noteq> \<f>"
      then have "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m = \<t>" using true_false_only_truth_values[OF tbm_type] by auto
      then have "NOT \<circ>\<^sub>c \<t> = \<t>" using s9 by simp
      then have "\<f> = \<t>" using NOT_true_is_false by simp
      then show False using true_false_distinct by simp
    qed
  qed
  have s11: "\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m = id(\<one>)" by (rule terminal_func_comp_elem[OF m_type])
  have s12: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m = \<t>" using s11 id_right_unit2[OF true_func_type] by simp
  have "\<t> = \<f>" using s10 s12 by simp
  then show False using true_false_distinct by auto
qed

lemma is_odd_exists_nth_odd:
  assumes io_true: "is_odd \<circ>\<^sub>c n = \<t>" and n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "\<exists>m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> n = nth_odd \<circ>\<^sub>c m"
proof (rule ccontr)
  assume "\<not> (\<exists>m. m \<in>\<^sub>c \<nat>\<^sub>c \<and> n = nth_odd \<circ>\<^sub>c m)"
  then obtain m where m_type[type_rule]: "m \<in>\<^sub>c \<nat>\<^sub>c" and n_def: "n = nth_even \<circ>\<^sub>c m"
    using n_type nth_even_or_nth_odd by blast
  have s1: "is_odd \<circ>\<^sub>c nth_even \<circ>\<^sub>c m = \<t>" using io_true n_def by simp
  have s2: "is_odd \<circ>\<^sub>c nth_even = (NOT \<circ>\<^sub>c is_even) \<circ>\<^sub>c nth_even" using is_odd_not_is_even by simp
  have s3: "(NOT \<circ>\<^sub>c is_even) \<circ>\<^sub>c nth_even = NOT \<circ>\<^sub>c (is_even \<circ>\<^sub>c nth_even)"
    by (rule sym[OF comp_associative2[OF nth_even_type is_even_type NOT_type]])
  have s4: "is_odd \<circ>\<^sub>c (nth_even \<circ>\<^sub>c m) = (is_odd \<circ>\<^sub>c nth_even) \<circ>\<^sub>c m"
    by (rule comp_associative2[OF m_type nth_even_type is_odd_type])
  have s5: "(is_odd \<circ>\<^sub>c nth_even) \<circ>\<^sub>c m = \<t>" using s1 s4 by simp
  have s6: "(NOT \<circ>\<^sub>c (is_even \<circ>\<^sub>c nth_even)) \<circ>\<^sub>c m = \<t>" using s2 s3 s5 by simp
  have is_even_nth_even_type[type_rule]: "is_even \<circ>\<^sub>c nth_even : \<nat>\<^sub>c \<rightarrow> \<Omega>" by typecheck_cfuncs
  have notie_type[type_rule]: "NOT \<circ>\<^sub>c (is_even \<circ>\<^sub>c nth_even) : \<nat>\<^sub>c \<rightarrow> \<Omega>" by typecheck_cfuncs
  have s7: "(NOT \<circ>\<^sub>c (is_even \<circ>\<^sub>c nth_even)) \<circ>\<^sub>c m = NOT \<circ>\<^sub>c ((is_even \<circ>\<^sub>c nth_even) \<circ>\<^sub>c m)"
    by (rule sym[OF comp_associative2[OF m_type is_even_nth_even_type NOT_type]])
  have s8: "(is_even \<circ>\<^sub>c nth_even) \<circ>\<^sub>c m = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m"
  proof -
    have "(is_even \<circ>\<^sub>c nth_even) \<circ>\<^sub>c m = (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>) \<circ>\<^sub>c m" using is_even_nth_even_true by simp
    also have "... = \<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m"
      by (rule sym[OF comp_associative2[OF m_type terminal_func_type true_func_type]])
    finally show ?thesis .
  qed
  have s9: "NOT \<circ>\<^sub>c (\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m) = \<t>" using s6 s7 s8 by simp
  have s10: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m = \<f>"
  proof -
    have tbm_type[type_rule]: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m \<in>\<^sub>c \<Omega>" by typecheck_cfuncs
    show ?thesis
    proof (rule ccontr)
      assume "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m \<noteq> \<f>"
      then have "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m = \<t>" using true_false_only_truth_values[OF tbm_type] by auto
      then have "NOT \<circ>\<^sub>c \<t> = \<t>" using s9 by simp
      then have "\<f> = \<t>" using NOT_true_is_false by simp
      then show False using true_false_distinct by simp
    qed
  qed
  have s11: "\<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m = id(\<one>)" by (rule terminal_func_comp_elem[OF m_type])
  have s12: "\<t> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c m = \<t>" using s11 id_right_unit2[OF true_func_type] by simp
  have "\<t> = \<f>" using s10 s12 by simp
  then show False using true_false_distinct by auto
qed

end
