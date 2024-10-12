theory Primitive_Recursive
  imports Category_Set.ETCS
begin

lemma primitive_recursion:
  assumes f0_type[type_rule]: "f0 : A \<rightarrow> B"
  assumes u_type[type_rule]: "u : (\<nat>\<^sub>c \<times>\<^sub>c A) \<times>\<^sub>c B \<rightarrow> B"
  shows "\<exists>!f. f : \<nat>\<^sub>c \<times>\<^sub>c A \<rightarrow> B \<and> (\<forall> a n. (a \<in>\<^sub>c A \<and> n \<in>\<^sub>c \<nat>\<^sub>c) \<longrightarrow>
    f \<circ>\<^sub>c \<langle>zero, a\<rangle> = f0 \<circ>\<^sub>c a \<and>
    f \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c n, a\<rangle> = u \<circ>\<^sub>c \<langle>\<langle>n, a\<rangle>, f \<circ>\<^sub>c \<langle>n, a\<rangle>\<rangle>)"
proof -

  obtain y where y_type[type_rule]: "y : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c B\<^bsup>A\<^esup>"
    and "y \<circ>\<^sub>c zero = \<langle>zero, metafunc f0\<rangle>"
    and "eval_func B A \<circ>\<^sub>c \<langle>a, y \<circ>\<^sub>c successor \<circ>\<^sub>c n\<rangle> = u \<circ>\<^sub>c \<langle>\<langle>n, a\<rangle>, eval_func B A \<circ>\<^sub>c \<langle>a, y \<circ>\<^sub>c n\<rangle>\<rangle>"
    apply typecheck_cfuncs

(* \<langle>successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c B\<^bsup>A\<^esup>, ()\<^sup>\<sharp> \<circ>\<^sub>c \<rangle> : (\<nat>\<^sub>c \<times>\<^sub>c B)\<^bsup>A\<^esup> \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c B\<^bsup>A\<^esup> *)
    oops

  