theory Monus
  imports Add
begin

definition monus1 :: "cfunc" 
  where "monus1 = (THE u. u : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup> \<and> u \<circ>\<^sub>c zero = ((left_coproj \<nat>\<^sub>c \<one>) \<circ>\<^sub>c (left_cart_proj \<nat>\<^sub>c \<one>))\<^sup>\<sharp> \<and> 
  u \<circ>\<^sub>c successor = predecessor\<^bsup>\<nat>\<^sub>c\<^esup>\<^sub>f \<circ>\<^sub>c u)"




definition monus2 :: "cfunc" 
  where "monus2   = eval_func  \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f monus1)"


definition monus :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" (infixl "\<midarrow>\<^sub>\<nat>" 65)
  where "m \<midarrow>\<^sub>\<nat> n = monus2 \<circ>\<^sub>c \<langle>m, n\<rangle>"


end