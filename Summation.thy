theory Summation
  imports Add Mult Pred_Logic
begin

definition indexed_sum1 :: cfunc where
  "indexed_sum1  = (THE u. u : \<nat>\<^sub>c \<rightarrow> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) 
      \<and> u \<circ>\<^sub>c zero = \<langle>zero, (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) one)\<^sup>\<sharp>\<rangle>
      \<and> u \<circ>\<^sub>c successor = \<langle>successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
        (add2 \<circ>\<^sub>c \<langle>eval_func  \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) 
              \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
                    right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)  \<circ>\<^sub>c 
                    right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>,
                  eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c 
                  left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
                    left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c 
                    right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>,
                  right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
        (successor \<times>\<^sub>f id(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>))\<rangle> \<circ>\<^sub>c u)"

lemma indexed_sum1_def2:
  "indexed_sum1 : \<nat>\<^sub>c \<rightarrow> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)
    \<and> indexed_sum1 \<circ>\<^sub>c zero = \<langle>zero, (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) one)\<^sup>\<sharp>\<rangle>
    \<and> indexed_sum1 \<circ>\<^sub>c successor = \<langle>successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
        (add2 \<circ>\<^sub>c \<langle>eval_func  \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) 
              \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
                    right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)  \<circ>\<^sub>c 
                    right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>,
                  eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c 
                  left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
                    left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c 
                    right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>,
                  right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
        (successor \<times>\<^sub>f id(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>))\<rangle> \<circ>\<^sub>c indexed_sum1"
proof(unfold indexed_sum1_def, rule theI', auto)
  show "\<exists>x. x : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup> \<and>
        x \<circ>\<^sub>c zero = \<langle>zero,(eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) one)\<^sup>\<sharp>\<rangle> \<and>
        x \<circ>\<^sub>c successor = \<langle>successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),(add2 \<circ>\<^sub>c
        \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
        right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>,
        eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>cleft_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
        left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>,
        right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>cleft_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c 
        successor \<times>\<^sub>f id\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle> \<circ>\<^sub>c x"
    by (typecheck_cfuncs, smt (verit, best) natural_number_object_property)
next
  show "\<And>x y. x : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup> \<Longrightarrow>
           y : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup> \<Longrightarrow>
           x \<circ>\<^sub>c zero = \<langle>zero,(eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) one)\<^sup>\<sharp>\<rangle> \<Longrightarrow>
           x \<circ>\<^sub>c successor = \<langle>successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),(add2 \<circ>\<^sub>c
        \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
        right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>,
        eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>cleft_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
        left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>,
        right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>cleft_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c 
        successor \<times>\<^sub>f id\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle> \<circ>\<^sub>c x \<Longrightarrow>
        y \<circ>\<^sub>c zero = \<langle>zero,(eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) one)\<^sup>\<sharp>\<rangle> \<Longrightarrow>
           y \<circ>\<^sub>c successor = \<langle>successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),(add2 \<circ>\<^sub>c
        \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
        right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>,
        eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>cleft_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
        left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>,
        right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>cleft_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c 
        successor \<times>\<^sub>f id\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle> \<circ>\<^sub>c y \<Longrightarrow>
           x = y"
by (typecheck_cfuncs, metis natural_number_object_func_unique)

(*  Because I know you might prefer this structure below
  fix x y
  assume x_type[type_rule]: "x: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>"
  assume y_type[type_rule]: "y: \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>"
  assume "x \<circ>\<^sub>c zero = \<langle>zero,(eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) one)\<^sup>\<sharp>\<rangle>"
  assume "x \<circ>\<^sub>c successor = \<langle>successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),(add2 \<circ>\<^sub>c
        \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
        right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>,
        eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>cleft_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
        left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>,
        right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>cleft_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c 
        successor \<times>\<^sub>f id\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle> \<circ>\<^sub>c x"
  assume "y \<circ>\<^sub>c zero = \<langle>zero,(eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) one)\<^sup>\<sharp>\<rangle>"
  assume "y \<circ>\<^sub>c successor = \<langle>successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),(add2 \<circ>\<^sub>c
        \<langle>eval_func \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
        right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>,
        eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c\<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>cleft_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
        left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>,
        right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>cleft_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c 
        successor \<times>\<^sub>f id\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle> \<circ>\<^sub>c y"
  show  "x = y"
*)
qed

lemma indexed_sum1_type[type_rule]:
  "indexed_sum1 : \<nat>\<^sub>c \<rightarrow> (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)"
   by (typecheck_cfuncs, smt indexed_sum1_def2)

lemma indexed_sum1_zero:  
 "indexed_sum1 \<circ>\<^sub>c zero = \<langle>zero, (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) one)\<^sup>\<sharp>\<rangle>"
  by (typecheck_cfuncs, smt indexed_sum1_def2)

lemma indexed_sum1_succ:  
  "indexed_sum1 \<circ>\<^sub>c successor = \<langle>successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
        (add2 \<circ>\<^sub>c \<langle>eval_func  \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) 
              \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
                    right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)  \<circ>\<^sub>c 
                    right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>,
                  eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c 
                  left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
                    left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c 
                    right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>,
                  right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
        (successor \<times>\<^sub>f id(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>))\<rangle> \<circ>\<^sub>c indexed_sum1"
by (typecheck_cfuncs, smt indexed_sum1_def2)

lemma left_proj_index_sum1_id:
  "left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c indexed_sum1 = id \<nat>\<^sub>c"
proof(etcs_rule natural_number_object_func_unique[where f = successor])
  show "(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c indexed_sum1) \<circ>\<^sub>c zero = id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c zero"
    by(etcs_assocr, typecheck_cfuncs, smt (verit, best) comp_type eval_func_type id_left_unit2
           indexed_sum1_zero left_cart_proj_cfunc_prod left_cart_proj_type transpose_func_type)
  show "id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor = successor \<circ>\<^sub>c id\<^sub>c \<nat>\<^sub>c"
    by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2)
  show "(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c indexed_sum1) \<circ>\<^sub>c successor =
    successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c indexed_sum1"
  proof -
    have "(left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c indexed_sum1) \<circ>\<^sub>c successor = 
           left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c indexed_sum1  \<circ>\<^sub>c successor"
      by (etcs_assocl, simp)
    also have "... = left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c \<langle>successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
        (add2 \<circ>\<^sub>c \<langle>eval_func  \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) 
              \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
                    right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)  \<circ>\<^sub>c 
                    right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>,
                  eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c 
                  left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
                    left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c 
                    right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>,
                  right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>\<rangle>)\<^sup>\<sharp> \<circ>\<^sub>c
        (successor \<times>\<^sub>f id(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>))\<rangle> \<circ>\<^sub>c indexed_sum1"
      using indexed_sum1_succ by argo
    also have "... = successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)  \<circ>\<^sub>c indexed_sum1"
      using left_cart_proj_cfunc_prod by(etcs_assocl,typecheck_cfuncs, auto)
    then show ?thesis 
      using calculation by auto
  qed
qed

definition indexed_sum :: cfunc where
  "indexed_sum  = (right_cart_proj \<nat>\<^sub>c  (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c indexed_sum1)\<^sup>\<flat>"

lemma indexed_sum_type[type_rule]: 
  "indexed_sum : ((\<nat>\<^sub>c \<times>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)) \<times>\<^sub>c \<nat>\<^sub>c) \<rightarrow> \<nat>\<^sub>c"
  unfolding  indexed_sum_def by typecheck_cfuncs

lemma indexed_sum_uppr_eq_lwr:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"  
  assumes "f \<in>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
  shows "indexed_sum \<circ>\<^sub>c \<langle>\<langle>n, f\<rangle>, zero\<rangle> =  cnufatem f \<circ>\<^sub>c n"
proof (unfold indexed_sum_def)
  have "(right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c indexed_sum1)\<^sup>\<flat> \<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>,zero\<rangle> = 
         right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<^sup>\<flat>  \<circ>\<^sub>c (id(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<times>\<^sub>f indexed_sum1) \<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>,zero\<rangle>"
    using assms by (typecheck_cfuncs, simp add: comp_associative2 inv_transpose_of_composition)
  also have "... = right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<^sup>\<flat>  \<circ>\<^sub>c  \<langle>\<langle>n,f\<rangle>,indexed_sum1 \<circ>\<^sub>c zero\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
  also have "... = right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<^sup>\<flat>  \<circ>\<^sub>c  \<langle>\<langle>n,f\<rangle>,\<langle>zero, (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) one)\<^sup>\<sharp>\<rangle>\<rangle>"
    by (simp add: indexed_sum1_zero)
  also have "... = eval_func  \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>))  \<circ>\<^sub>c (id(\<nat>\<^sub>c \<times>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)) \<times>\<^sub>f  right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>))\<circ>\<^sub>c
      \<langle>\<langle>n,f\<rangle>,\<langle>zero, (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) one)\<^sup>\<sharp>\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_type_def comp_associative inv_transpose_func_def3)
  also have "... = eval_func  \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)) \<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>,(eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) one)\<^sup>\<sharp>\<rangle>"
    using assms cfunc_cross_prod_comp_cfunc_prod id_left_unit2 right_cart_proj_cfunc_prod by (typecheck_cfuncs, force)
  also have "... = eval_func  \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)) \<circ>\<^sub>c (id (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<times>\<^sub>f (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) one)\<^sup>\<sharp>)\<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>, id one\<rangle>"
    using assms cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2 by (typecheck_cfuncs, force)
  also have "... = (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) one) \<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>, id one\<rangle>"
    using assms comp_associative2 transpose_func_def by (typecheck_cfuncs, force)
  also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>n,f\<rangle>"
    by (typecheck_cfuncs, metis comp_associative2 left_cart_proj_cfunc_prod assms)
  also have "... = cnufatem f \<circ>\<^sub>c n"
    by (typecheck_cfuncs, metis eval_lemma metafunc_cnufatem assms)
  then show "(right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c indexed_sum1)\<^sup>\<flat> \<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>,zero\<rangle> = cnufatem f \<circ>\<^sub>c n" 
    using calculation by auto
qed

lemma indexed_sum_tail_term:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "f \<in>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
  shows "indexed_sum \<circ>\<^sub>c \<langle>\<langle>n, f\<rangle>, successor \<circ>\<^sub>c m\<rangle> = (indexed_sum \<circ>\<^sub>c \<langle>\<langle>n, f\<rangle>, m\<rangle>) +\<^sub>\<nat> (cnufatem f \<circ>\<^sub>c (n +\<^sub>\<nat> (successor \<circ>\<^sub>c m)))"
proof (unfold indexed_sum_def)
  define \<phi> where "\<phi> = add2 \<circ>\<^sub>c \<langle>eval_func  \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) 
              \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
                    right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)  \<circ>\<^sub>c 
                    right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>,
                  eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c 
                  left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
                    left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c 
                    right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>,
                  right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>\<rangle>"
  then have \<phi>_type[type_rule]: "\<phi> : (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<times>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<rightarrow> \<nat>\<^sub>c"
    unfolding \<phi>_def by typecheck_cfuncs
  have "(right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c indexed_sum1)\<^sup>\<flat> \<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>,successor \<circ>\<^sub>c m\<rangle> = 
        right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<^sup>\<flat>  \<circ>\<^sub>c (id(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<times>\<^sub>f indexed_sum1) \<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>,successor \<circ>\<^sub>c m\<rangle>"
    using assms comp_associative2 inv_transpose_of_composition by (typecheck_cfuncs, force)
  also have "... = right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<^sup>\<flat>  \<circ>\<^sub>c  \<langle>\<langle>n,f\<rangle>, (indexed_sum1  \<circ>\<^sub>c successor) \<circ>\<^sub>c m\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod cfunc_type_def comp_associative id_left_unit2)
  also have "... = right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<^sup>\<flat>  \<circ>\<^sub>c  
                    \<langle>\<langle>n,f\<rangle>, (\<langle>successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),  \<phi>\<^sup>\<sharp> \<circ>\<^sub>c
                    (successor \<times>\<^sub>f id(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>))\<rangle> \<circ>\<^sub>c indexed_sum1) \<circ>\<^sub>c m\<rangle>"
    using assms \<phi>_def indexed_sum1_succ by argo
  also have "... = right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<^sup>\<flat>  \<circ>\<^sub>c  
                    \<langle>\<langle>n,f\<rangle>, \<langle>successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>), \<phi>\<^sup>\<sharp> \<circ>\<^sub>c 
                    (successor \<times>\<^sub>f id(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>))\<rangle> \<circ>\<^sub>c indexed_sum1 \<circ>\<^sub>c m\<rangle>"
    using assms comp_associative2 by (typecheck_cfuncs, auto)
  also have "... = (right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>))\<^sup>\<flat>  \<circ>\<^sub>c  
                    \<langle>\<langle>n,f\<rangle>, \<langle>successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c indexed_sum1 \<circ>\<^sub>c m, \<phi>\<^sup>\<sharp> \<circ>\<^sub>c 
                    (successor \<times>\<^sub>f id(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)) \<circ>\<^sub>c indexed_sum1 \<circ>\<^sub>c m\<rangle> \<rangle>"
    using assms by (typecheck_cfuncs, smt (verit, best) cfunc_prod_comp comp_associative2)
  also have "... = eval_func \<nat>\<^sub>c  (\<nat>\<^sub>c \<times>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)) \<circ>\<^sub>c (id  (\<nat>\<^sub>c \<times>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)) \<times>\<^sub>f (right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)))  \<circ>\<^sub>c  
                    \<langle>\<langle>n,f\<rangle>, \<langle>successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c indexed_sum1 \<circ>\<^sub>c m, \<phi>\<^sup>\<sharp> \<circ>\<^sub>c 
                    (successor \<times>\<^sub>f id(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)) \<circ>\<^sub>c indexed_sum1 \<circ>\<^sub>c m\<rangle> \<rangle>"
    using assms comp_associative2 inv_transpose_func_def3 by (typecheck_cfuncs, auto)
  also have "... = eval_func \<nat>\<^sub>c  (\<nat>\<^sub>c \<times>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)) \<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>,  \<phi>\<^sup>\<sharp> \<circ>\<^sub>c (successor \<times>\<^sub>f id(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)) \<circ>\<^sub>c indexed_sum1 \<circ>\<^sub>c m\<rangle>"
    using assms cfunc_cross_prod_comp_cfunc_prod id_left_unit2 right_cart_proj_cfunc_prod by (typecheck_cfuncs, force)
  also have "... = eval_func \<nat>\<^sub>c  (\<nat>\<^sub>c \<times>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)) \<circ>\<^sub>c (id (\<nat>\<^sub>c\<times>\<^sub>c(\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)) \<times>\<^sub>f \<phi>\<^sup>\<sharp>)\<circ>\<^sub>c\<langle>\<langle>n,f\<rangle>,(successor \<times>\<^sub>f id(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)) \<circ>\<^sub>c indexed_sum1 \<circ>\<^sub>c m\<rangle>"
    using assms cfunc_cross_prod_comp_cfunc_prod id_left_unit2 by (typecheck_cfuncs, force)
  also have "... = \<phi> \<circ>\<^sub>c\<langle>\<langle>n,f\<rangle>,(successor \<times>\<^sub>f id(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)) \<circ>\<^sub>c indexed_sum1 \<circ>\<^sub>c m\<rangle>"
    using assms comp_associative2 transpose_func_def by (typecheck_cfuncs, force)
  also have "... = add2 \<circ>\<^sub>c \<langle>eval_func  \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) 
              \<circ>\<^sub>c \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
                    right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)  \<circ>\<^sub>c 
                    right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>,
                  eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c 
                  left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
                    left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c 
                    right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>,
                  right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>\<rangle>
                  \<circ>\<^sub>c\<langle>\<langle>n,f\<rangle>,(successor \<times>\<^sub>f id(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)) \<circ>\<^sub>c indexed_sum1 \<circ>\<^sub>c m\<rangle>"
    using assms  \<phi>_def comp_associative2 by (typecheck_cfuncs, auto)
  also have "... = add2 \<circ>\<^sub>c 
        \<langle>eval_func  \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) 
              \<circ>\<^sub>c    \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
                    right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)  \<circ>\<^sub>c 
                    right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>
        \<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>,(successor \<times>\<^sub>f id(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)) \<circ>\<^sub>c indexed_sum1 \<circ>\<^sub>c m\<rangle>,
        eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c 
                          \<langle>add2 \<circ>\<^sub>c 
                    \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
                    left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>,
              right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>
        \<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>,(successor \<times>\<^sub>f id(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)) \<circ>\<^sub>c indexed_sum1 \<circ>\<^sub>c m\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, smt (verit, best) cfunc_prod_comp comp_associative2)
  also have "... = (eval_func  \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) 
              \<circ>\<^sub>c    \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
                    right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)  \<circ>\<^sub>c 
                    right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>
        \<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>,(successor \<times>\<^sub>f id(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)) \<circ>\<^sub>c indexed_sum1 \<circ>\<^sub>c m\<rangle>)  +\<^sub>\<nat>
       (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c 
                          \<langle>add2 \<circ>\<^sub>c 
                    \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
                    left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>,
              right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>
        \<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>,(successor \<times>\<^sub>f id(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)) \<circ>\<^sub>c indexed_sum1 \<circ>\<^sub>c m\<rangle>)"
    using assms add_def by presburger
  also have "... = (eval_func  \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) 
              \<circ>\<^sub>c    \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
                    right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)  \<circ>\<^sub>c 
                    right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>
        \<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>,(successor \<times>\<^sub>f id(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)) \<circ>\<^sub>c indexed_sum1 \<circ>\<^sub>c m\<rangle>)  +\<^sub>\<nat>
                   (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c 
                        \<langle>add2 \<circ>\<^sub>c
                        \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
                         left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>
                \<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>,(successor \<times>\<^sub>f id(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)) \<circ>\<^sub>c indexed_sum1 \<circ>\<^sub>c m\<rangle>,
                          right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)
                \<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>,(successor \<times>\<^sub>f id(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)) \<circ>\<^sub>c indexed_sum1 \<circ>\<^sub>c m\<rangle>\<rangle>)"
    using assms by (etcs_assocl, typecheck_cfuncs, smt (verit, best) cfunc_prod_comp comp_associative2)
  also have "... = (eval_func  \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) 
              \<circ>\<^sub>c    \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
                    right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)  \<circ>\<^sub>c 
                    right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>
        \<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>,(successor \<times>\<^sub>f id(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)) \<circ>\<^sub>c indexed_sum1 \<circ>\<^sub>c m\<rangle>) 
  +\<^sub>\<nat>
       (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c 
                          \<langle>add2 \<circ>\<^sub>c 
                   \<langle>left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>,
                   (successor \<times>\<^sub>f id(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)) \<circ>\<^sub>c indexed_sum1 \<circ>\<^sub>c m\<rangle>,
                    left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)
\<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>,(successor \<times>\<^sub>f id(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)) \<circ>\<^sub>c indexed_sum1 \<circ>\<^sub>c m\<rangle>\<rangle>,f\<rangle>)"
    using assms by (etcs_assocl, typecheck_cfuncs, smt (verit, best) cfunc_prod_comp comp_associative2 left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  also have "... = (eval_func  \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) 
              \<circ>\<^sub>c    \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
                    right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)  \<circ>\<^sub>c 
                    right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>
        \<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>,(successor \<times>\<^sub>f id(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)) \<circ>\<^sub>c indexed_sum1 \<circ>\<^sub>c m\<rangle>) 
  +\<^sub>\<nat>
       (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c 
                    \<langle>n,left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c (successor \<times>\<^sub>f id(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)) \<circ>\<^sub>c indexed_sum1 \<circ>\<^sub>c m\<rangle>,f \<rangle>)"
    using left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod assms by (typecheck_cfuncs, auto)
  also have "... = (eval_func  \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) 
              \<circ>\<^sub>c    \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
                    right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)  \<circ>\<^sub>c 
                    right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>
        \<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>,(successor \<times>\<^sub>f id(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)) \<circ>\<^sub>c indexed_sum1 \<circ>\<^sub>c m\<rangle>) 
  +\<^sub>\<nat>
       (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c 
                          \<langle>add2 \<circ>\<^sub>c 
                    \<langle>n,  successor \<circ>\<^sub>c  left_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c indexed_sum1 \<circ>\<^sub>c m\<rangle>, f\<rangle>)"
    using assms by (etcs_assocl, typecheck_cfuncs, smt (verit, best) left_cart_proj_cfunc_cross_prod)
  also have "... = (eval_func  \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) 
              \<circ>\<^sub>c    \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
                    right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)  \<circ>\<^sub>c 
                    right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>
        \<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>,(successor \<times>\<^sub>f id(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)) \<circ>\<^sub>c indexed_sum1 \<circ>\<^sub>c m\<rangle>) 
  +\<^sub>\<nat>
       (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>n,  successor  \<circ>\<^sub>c m\<rangle>, f\<rangle>)"
    using assms  by (etcs_assocl,etcs_assocr, typecheck_cfuncs, simp add: cfunc_type_def comp_associative id_left_unit2 left_proj_index_sum1_id)
  also have "... = (eval_func  \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) 
              \<circ>\<^sub>c    \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>),
                    right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)  \<circ>\<^sub>c 
                    right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<rangle>
        \<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>,(successor \<times>\<^sub>f id(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)) \<circ>\<^sub>c indexed_sum1 \<circ>\<^sub>c m\<rangle>) 
  +\<^sub>\<nat>
       (cnufatem f \<circ>\<^sub>c (n +\<^sub>\<nat> (successor \<circ>\<^sub>c m)))"
    by (typecheck_cfuncs, metis add_def assms eval_lemma metafunc_cnufatem)
  also have "... = (eval_func  \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) 
              \<circ>\<^sub>c    \<langle>left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)
    \<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>,(successor \<times>\<^sub>f id(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)) \<circ>\<^sub>c indexed_sum1 \<circ>\<^sub>c m\<rangle>,
                    right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)  \<circ>\<^sub>c 
                    right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) 
    \<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>,(successor \<times>\<^sub>f id(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)) \<circ>\<^sub>c indexed_sum1 \<circ>\<^sub>c m\<rangle>\<rangle>) 
  +\<^sub>\<nat>
       (cnufatem f \<circ>\<^sub>c (n +\<^sub>\<nat> (successor \<circ>\<^sub>c m)))"
    using assms cfunc_prod_comp comp_associative2 by (typecheck_cfuncs, force)
  also have "... = (eval_func  \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) 
              \<circ>\<^sub>c    \<langle>\<langle>n,f\<rangle>,
                    right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)  \<circ>\<^sub>c 
                    right_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) 
    \<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>,(successor \<times>\<^sub>f id(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)) \<circ>\<^sub>c indexed_sum1 \<circ>\<^sub>c m\<rangle>\<rangle>) 
  +\<^sub>\<nat>
       (cnufatem f \<circ>\<^sub>c (n +\<^sub>\<nat> (successor \<circ>\<^sub>c m)))"
    using assms left_cart_proj_cfunc_prod by (typecheck_cfuncs, auto)
  also have "... = (eval_func  \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>,  right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)  \<circ>\<^sub>c              
           (successor \<times>\<^sub>f id(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)) \<circ>\<^sub>c indexed_sum1 \<circ>\<^sub>c m\<rangle>) +\<^sub>\<nat>  (cnufatem f \<circ>\<^sub>c (n +\<^sub>\<nat> (successor \<circ>\<^sub>c m)))"
    using assms right_cart_proj_cfunc_prod by (typecheck_cfuncs, auto)
  also have "... = (eval_func  \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c \<langle> \<langle>n,f\<rangle>,  id(\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c
                     right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c indexed_sum1 \<circ>\<^sub>c m\<rangle>)   +\<^sub>\<nat>
                           (cnufatem f \<circ>\<^sub>c (n +\<^sub>\<nat> (successor \<circ>\<^sub>c m)))"
    using assms right_cart_proj_cfunc_cross_prod by(etcs_assocl, typecheck_cfuncs, auto)
  also have "... = (eval_func  \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<circ>\<^sub>c (id(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<times>\<^sub>f (right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)   \<circ>\<^sub>c indexed_sum1) ) \<circ>\<^sub>c  \<langle> \<langle>n,f\<rangle>,  m\<rangle>)          
                        +\<^sub>\<nat> (cnufatem f \<circ>\<^sub>c (n +\<^sub>\<nat> (successor \<circ>\<^sub>c m)))"
    using assms by(etcs_assocl, typecheck_cfuncs, smt (verit, best) cfunc_cross_prod_comp_cfunc_prod comp_associative2 id_left_unit2)
  also have "... = ((right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c indexed_sum1)\<^sup>\<flat> \<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>,m\<rangle>) +\<^sub>\<nat> (cnufatem f \<circ>\<^sub>c (n +\<^sub>\<nat> (successor \<circ>\<^sub>c m)))"
    using assms inv_transpose_func_def3 by (etcs_assocl, typecheck_cfuncs, auto)
  then show "(right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c indexed_sum1)\<^sup>\<flat> \<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>,successor \<circ>\<^sub>c m\<rangle> =
                    ((right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c indexed_sum1)\<^sup>\<flat> \<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>,m\<rangle>)  +\<^sub>\<nat> (cnufatem f \<circ>\<^sub>c (n +\<^sub>\<nat> (successor \<circ>\<^sub>c m)))"
    using calculation by auto
qed

lemma sum_indexed_sum:
  assumes "a \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "f \<in>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
  assumes "g \<in>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
  shows "indexed_sum \<circ>\<^sub>c \<langle>\<langle>a, meta_add \<nat>\<^sub>c \<circ>\<^sub>c \<langle>f,g\<rangle>\<rangle>, n\<rangle> = 
          add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a, f\<rangle>, n\<rangle>, indexed_sum \<circ>\<^sub>c \<langle>\<langle>a, g\<rangle>, n\<rangle>\<rangle>"
proof -
  have "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a, meta_add \<nat>\<^sub>c \<circ>\<^sub>c \<langle>f,g\<rangle>\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle> ,    
                         add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a, f \<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c \<rangle>, indexed_sum \<circ>\<^sub>c \<langle>\<langle>a, g\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>) \<circ>\<^sub>c n = \<t>"
  proof(rule nat_induction)
    show "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,meta_add \<nat>\<^sub>c \<circ>\<^sub>c \<langle>f,g\<rangle>\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,
                          add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>, indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,g\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
      using assms by typecheck_cfuncs
    show "n \<in>\<^sub>c \<nat>\<^sub>c"
      using assms(2) by auto
  next
    have "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,meta_add \<nat>\<^sub>c \<circ>\<^sub>c \<langle>f,g\<rangle>\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,
                         add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,g\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>) \<circ>\<^sub>c zero = 
          eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,meta_add \<nat>\<^sub>c \<circ>\<^sub>c \<langle>f,g\<rangle>\<rangle>, zero\<rangle>,
                         add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle>, zero\<rangle>,indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,g\<rangle>, zero\<rangle>\<rangle>\<rangle>"
      using assms by(typecheck_cfuncs, smt (verit, best) cfunc_prod_comp comp_associative2 id_left_unit2 id_right_unit2 terminal_func_comp_elem)
    also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a, metafunc (add2 \<circ>\<^sub>c \<langle>cnufatem  f, cnufatem  g\<rangle>)\<rangle>, zero\<rangle>,
                         add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle>, zero\<rangle>,indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,g\<rangle>, zero\<rangle>\<rangle>\<rangle>"
      by (typecheck_cfuncs, metis meta_add_as_add metafunc_cnufatem assms(3,4))
    also have "... = \<t>"
      by (typecheck_cfuncs, smt (verit, best) cfunc_prod_comp cnufatem_metafunc comp_associative2 eq_pred_iff_eq indexed_sum_uppr_eq_lwr assms)
    then show "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,meta_add \<nat>\<^sub>c \<circ>\<^sub>c \<langle>f,g\<rangle>\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,
                               add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,g\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>) \<circ>\<^sub>c zero = \<t>"
      using calculation by argo
  next
    fix n 
    assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
    assume  "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,meta_add \<nat>\<^sub>c \<circ>\<^sub>c \<langle>f,g\<rangle>\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,
                               add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,g\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>) \<circ>\<^sub>c n = \<t>"
    then have "\<t> = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,meta_add \<nat>\<^sub>c \<circ>\<^sub>c \<langle>f,g\<rangle>\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c n,
                               add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,g\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c n\<rangle>"
      using assms by (etcs_assocl, typecheck_cfuncs, smt (verit, best) cfunc_prod_comp cfunc_prod_type comp_associative2)
    also have "... =  eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,meta_add \<nat>\<^sub>c \<circ>\<^sub>c \<langle>f,g\<rangle>\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c n,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>,
                               add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c n,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>,indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,g\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c n,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c n\<rangle>\<rangle>\<rangle>"
      using assms by (typecheck_cfuncs, smt (verit, best) cfunc_prod_comp comp_associative2)
    then have induction_hypothesis: "indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,meta_add \<nat>\<^sub>c \<circ>\<^sub>c \<langle>f,g\<rangle>\<rangle>,n\<rangle> = 
                add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle>, n\<rangle>,indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,g\<rangle>, n\<rangle>\<rangle>"
      using assms by (typecheck_cfuncs, metis calculation eq_pred_iff_eq_conv id_left_unit2 id_right_unit2 terminal_func_comp_elem true_false_distinct)
    have induction_conclusion: "indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,meta_add \<nat>\<^sub>c \<circ>\<^sub>c \<langle>f,g\<rangle>\<rangle>, successor \<circ>\<^sub>c n\<rangle> = 
                add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle>, successor \<circ>\<^sub>c n\<rangle>,indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,g\<rangle>, successor \<circ>\<^sub>c n\<rangle>\<rangle>"
    proof - 
      have "indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,meta_add \<nat>\<^sub>c \<circ>\<^sub>c \<langle>f,g\<rangle>\<rangle>, successor \<circ>\<^sub>c n\<rangle> =
            add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,meta_add \<nat>\<^sub>c \<circ>\<^sub>c \<langle>f,g\<rangle>\<rangle>, n\<rangle>,  
            (cnufatem (meta_add \<nat>\<^sub>c \<circ>\<^sub>c \<langle>f,g\<rangle>) \<circ>\<^sub>c (a +\<^sub>\<nat> (successor \<circ>\<^sub>c n)))\<rangle>"
        using assms  add_def indexed_sum_tail_term by (typecheck_cfuncs, presburger)
      also have "... = add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,metafunc (add2 \<circ>\<^sub>c \<langle>cnufatem  f, cnufatem  g\<rangle>)\<rangle>, n\<rangle>,  
            (cnufatem (meta_add \<nat>\<^sub>c \<circ>\<^sub>c \<langle>f,g\<rangle>) \<circ>\<^sub>c (a +\<^sub>\<nat> (successor \<circ>\<^sub>c n)))\<rangle>"
        by (typecheck_cfuncs, metis meta_add_as_add metafunc_cnufatem assms(3,4))
      also have "... = add2 \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle>, n\<rangle>,indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,g\<rangle>, n\<rangle>\<rangle> ,
                                add2 \<circ>\<^sub>c \<langle>((cnufatem  f) \<circ>\<^sub>c  (a +\<^sub>\<nat> (successor \<circ>\<^sub>c n))), ((cnufatem  g) \<circ>\<^sub>c  (a +\<^sub>\<nat> (successor \<circ>\<^sub>c n)))\<rangle>\<rangle>"
        using assms(1,3,4) by (typecheck_cfuncs, smt (z3) cfunc_prod_comp cfunc_type_def comp_associative induction_hypothesis meta_add_as_add metafunc_cnufatem)        
      also have "... = add2 \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle>, n\<rangle>,((cnufatem  f) \<circ>\<^sub>c (a +\<^sub>\<nat> (successor \<circ>\<^sub>c n)))\<rangle>,
                                add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,g\<rangle>, n\<rangle>,((cnufatem  g) \<circ>\<^sub>c (a +\<^sub>\<nat> (successor \<circ>\<^sub>c n)))\<rangle>\<rangle>"
        using assms by (typecheck_cfuncs, metis add_associates_mix_commutes add_def)
      also have "... = add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle>, successor \<circ>\<^sub>c n\<rangle>,
                               indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,g\<rangle>, successor \<circ>\<^sub>c n\<rangle>\<rangle>"
        using assms add_def indexed_sum_tail_term by (typecheck_cfuncs, presburger)
      then show ?thesis 
        using calculation by argo
    qed
    then show "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,meta_add \<nat>\<^sub>c \<circ>\<^sub>c \<langle>f,g\<rangle>\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,
                add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,g\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c n = \<t>"
    proof - 
      have "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,meta_add \<nat>\<^sub>c \<circ>\<^sub>c \<langle>f,g\<rangle>\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,
                add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,g\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c n =
             eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,meta_add \<nat>\<^sub>c \<circ>\<^sub>c \<langle>f,g\<rangle>\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c  successor \<circ>\<^sub>c n ,
                add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,g\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c  successor \<circ>\<^sub>c n\<rangle>"
        using assms by (etcs_assocr, typecheck_cfuncs, smt (verit, best) cfunc_prod_comp cfunc_type_def comp_associative)
      also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,meta_add \<nat>\<^sub>c \<circ>\<^sub>c \<langle>f,g\<rangle>\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor \<circ>\<^sub>c n,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor \<circ>\<^sub>c n\<rangle>,
                add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor \<circ>\<^sub>c n,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor \<circ>\<^sub>c n\<rangle>,indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,g\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor \<circ>\<^sub>c n,id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor \<circ>\<^sub>c n\<rangle>\<rangle>\<rangle>"
        using assms by (typecheck_cfuncs, smt (verit, ccfv_SIG) cfunc_prod_comp comp_associative2)
      also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,meta_add \<nat>\<^sub>c \<circ>\<^sub>c \<langle>f,g\<rangle>\<rangle>, successor \<circ>\<^sub>c n\<rangle>,
                add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle>, successor \<circ>\<^sub>c n\<rangle>,indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,g\<rangle>, successor \<circ>\<^sub>c n\<rangle>\<rangle>\<rangle>"
        using assms  by (typecheck_cfuncs, metis id_left_unit2 id_right_unit2 id_type one_unique_element)
      then show ?thesis
        using assms by (typecheck_cfuncs, smt (verit, best) induction_conclusion calculation cart_prod_extract_right comp_associative2 comp_type eq_pred_iff_eq indexed_sum_type)
    qed
  qed
  then have "\<t> = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a, meta_add \<nat>\<^sub>c \<circ>\<^sub>c \<langle>f,g\<rangle>\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c n,    
                         add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a, f \<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c \<rangle>, indexed_sum \<circ>\<^sub>c \<langle>\<langle>a, g \<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c n\<rangle>"
    using assms by (etcs_assocl, typecheck_cfuncs, smt (verit, best) cfunc_prod_comp cfunc_prod_type comp_associative2)
  also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a, meta_add \<nat>\<^sub>c \<circ>\<^sub>c \<langle>f,g\<rangle>\<rangle>, n\<rangle>,    
                         add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a, f \<rangle>, n\<rangle>, indexed_sum \<circ>\<^sub>c \<langle>\<langle>a, g \<rangle>, n\<rangle>\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, smt (verit, ccfv_SIG) cart_prod_extract_right cfunc_prod_comp comp_associative2)
  then show ?thesis
    using assms calculation eq_pred_iff_eq by (typecheck_cfuncs, presburger)
qed

lemma indexed_sum_split:
  assumes "a \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "f \<in>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
  assumes "q \<in>\<^sub>c \<nat>\<^sub>c"
  shows "indexed_sum \<circ>\<^sub>c \<langle>\<langle>a, f\<rangle>, (successor \<circ>\<^sub>c m) +\<^sub>\<nat> q \<rangle> = (indexed_sum \<circ>\<^sub>c \<langle>\<langle>a, f\<rangle>, m\<rangle>) +\<^sub>\<nat> (indexed_sum \<circ>\<^sub>c \<langle>\<langle>a +\<^sub>\<nat> (successor \<circ>\<^sub>c m), f\<rangle>, q\<rangle>)"
proof -
  have "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a, f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, add2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c m) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<rangle>,    
                          add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a, f\<rangle>, m\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> , 
                                  indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>a, (successor \<circ>\<^sub>c m)\<rangle>, f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>) \<circ>\<^sub>c q = \<t>"
  proof(rule nat_induction)
    show " eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,add2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c m) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>,add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle>,m\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c m\<rangle>,f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
      using assms(1-3) by typecheck_cfuncs
    show "q \<in>\<^sub>c \<nat>\<^sub>c"
      using assms(4) by typecheck_cfuncs
  next
    have "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,add2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c m) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>,
                          add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle>,m\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c m\<rangle>,f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>) \<circ>\<^sub>c zero =   
           eq_pred \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle>, add2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c m), zero\<rangle>\<rangle>,
                          add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle>,m\<rangle>, indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c m\<rangle>,f\<rangle>, zero\<rangle>\<rangle>\<rangle>"
      using assms(1-3) by(etcs_assocr, typecheck_cfuncs, smt (verit, best) cfunc_prod_comp comp_associative2 id_left_unit2 id_right_unit2 terminal_func_comp_elem)
    also have "... = \<t>"
      using assms by (typecheck_cfuncs, metis add_def add_respects_zero_on_right eq_pred_iff_eq indexed_sum_tail_term indexed_sum_uppr_eq_lwr)
    then show "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c  \<langle>\<langle>a,f\<rangle> \<circ>\<^sub>c  \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,add2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c m) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>,
                              add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle>,m\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,
                                      indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c m\<rangle>,f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>) \<circ>\<^sub>c zero =  \<t>"
      using calculation by auto
  next
    fix q 
    assume q_type[type_rule]: "q \<in>\<^sub>c \<nat>\<^sub>c"
    assume eq_pred_ind_hyp: "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,add2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c m) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>,
                            add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle>,m\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,
                                    indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c m\<rangle>,f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>) \<circ>\<^sub>c q =  \<t>" 
    have "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,add2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c m) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>,
                            add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle>,m\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,
                                    indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c m\<rangle>,f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>) \<circ>\<^sub>c q =
                eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle>, add2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c m), q\<rangle>\<rangle>,
                            add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle>,m\<rangle>,
                                    indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c m\<rangle>,f\<rangle>, q\<rangle>\<rangle>\<rangle>" 
      using assms(1-3) by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2 id_left_unit2 id_right_unit2 terminal_func_comp_elem)
    then have induction_hypothesis: "indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle>, add2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c m), q\<rangle>\<rangle> = 
                             add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle>,m\<rangle>,
                                     indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c m\<rangle>,f\<rangle>, q\<rangle>\<rangle>"
      by (smt (verit, ccfv_SIG) eq_pred_ind_hyp add_def add_type assms(1-3) cfunc_prod_type comp_type eq_pred_iff_eq indexed_sum_type q_type succ_n_type)  

    have "indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle>, add2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c m), successor \<circ>\<^sub>c q\<rangle>\<rangle> =
          add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle>, m\<rangle>,
                  indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c m\<rangle>,f\<rangle>, successor \<circ>\<^sub>c q\<rangle>\<rangle>"
    proof - 
      have "indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle>, add2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c m), successor \<circ>\<^sub>c q\<rangle>\<rangle> =
              add2 \<circ>\<^sub>c \<langle> (indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle>, add2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c m), q\<rangle>\<rangle>),
              (cnufatem f \<circ>\<^sub>c (a +\<^sub>\<nat>  (add2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c m), successor \<circ>\<^sub>c q\<rangle>)))\<rangle>"
        using assms(1-3) add2_respects_succ_right indexed_sum_tail_term add_def by (typecheck_cfuncs, auto)
      also have "... = add2 \<circ>\<^sub>c \<langle>add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle>,m\<rangle>,
                                     indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c m\<rangle>,f\<rangle>, q\<rangle>\<rangle>,
              (cnufatem f \<circ>\<^sub>c (a +\<^sub>\<nat>  (add2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c m), successor \<circ>\<^sub>c q\<rangle>)))\<rangle>"
        using assms(1-3) induction_hypothesis  by argo
      also have "... = add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle>,m\<rangle>, 
                              add2 \<circ>\<^sub>c \<langle>
                                     indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c m\<rangle>,f\<rangle>, q\<rangle>,
              (cnufatem f \<circ>\<^sub>c (a +\<^sub>\<nat>  (add2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c m), successor \<circ>\<^sub>c q\<rangle>)))\<rangle>\<rangle>"
        using assms(1-3) by (typecheck_cfuncs, metis add_associates add_def)
      also have "... = add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle>,m\<rangle>, 
                             (indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c m\<rangle>,f\<rangle>, q\<rangle>) +\<^sub>\<nat>
              ((cnufatem f \<circ>\<^sub>c (a +\<^sub>\<nat>  ((successor \<circ>\<^sub>c m) +\<^sub>\<nat> (successor \<circ>\<^sub>c q)))))\<rangle>"
        using assms(1-3) add_def by presburger
      also have "... = add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle>, m\<rangle>,
                  indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c m\<rangle>,f\<rangle>, successor \<circ>\<^sub>c q\<rangle>\<rangle>"
        using assms(1-3) add_associates add_def indexed_sum_tail_term by (typecheck_cfuncs, fastforce)
      then show ?thesis
        using calculation by auto
    qed 
    then have "(eq_pred \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle>, add2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c m), successor \<circ>\<^sub>c q\<rangle>\<rangle>,
          add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle>, m\<rangle>,
                  indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c m\<rangle>,f\<rangle>, successor \<circ>\<^sub>c q\<rangle>\<rangle>\<rangle> = \<t>"
      by (metis add_def add_type assms(1-3) cfunc_prod_type comp_type eq_pred_iff_eq indexed_sum_type q_type succ_n_type)
    then show "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,add2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c m) \<circ>\<^sub>c\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>,
                add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a,f\<rangle>,m\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>a,successor \<circ>\<^sub>c m\<rangle>,f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c q = \<t>"
      using assms(1-3) by (typecheck_cfuncs, smt (verit, best)  cfunc_prod_comp comp_associative2
                                               id_left_unit2 id_right_unit2 terminal_func_comp_elem)
  qed
  then have "\<t> = (eq_pred \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a, f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, add2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c m) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<rangle>,    
                          add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a, f\<rangle>, m\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, 
                                  indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>a, (successor \<circ>\<^sub>c m)\<rangle>, f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<rangle>\<rangle> \<circ>\<^sub>c q"
    using assms comp_associative2 by (typecheck_cfuncs, auto)
  also have "... = (eq_pred \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a, f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, add2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c m) \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c q,    
                          add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a, f\<rangle>, m\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, 
                                  indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>a, (successor \<circ>\<^sub>c m)\<rangle>, f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<rangle>  \<circ>\<^sub>c q\<rangle>"
    using assms by (typecheck_cfuncs, smt (verit, ccfv_SIG) cfunc_prod_comp comp_associative2)
  also have "... = (eq_pred \<nat>\<^sub>c) \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a, f\<rangle> , add2 \<circ>\<^sub>c \<langle>(successor \<circ>\<^sub>c m), q\<rangle>\<rangle>,    
                          add2 \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>a, f\<rangle>, m\<rangle>, 
                                  indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>a, (successor \<circ>\<^sub>c m)\<rangle>, f\<rangle>, q\<rangle>\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, smt (verit, best) cfunc_prod_comp comp_associative2 id_left_unit2 id_right_unit2 terminal_func_comp_elem)
  then show ?thesis
    using assms by (typecheck_cfuncs, simp add: add_def calculation eq_pred_iff_eq)
qed

lemma index_sum_index_shift:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "a \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "f \<in>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c"
  shows "indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>m,a\<rangle>, f\<rangle>,n\<rangle> = indexed_sum \<circ>\<^sub>c \<langle>\<langle>m, metafunc(cnufatem(f) \<circ>\<^sub>c (add2 \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, a  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>))\<rangle>, n\<rangle>"
proof -
  have "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>m,a\<rangle>, f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>,
                        indexed_sum \<circ>\<^sub>c \<langle>\<langle>m, metafunc(cnufatem(f) \<circ>\<^sub>c (add2 \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, a  \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>))\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c n = \<t>"
  proof(rule nat_induction)
    show "eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>m,a\<rangle>,f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,indexed_sum \<circ>\<^sub>c \<langle>\<langle>m,metafunc (cnufatem f \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>)\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<Omega>"
      using assms(2-4) by typecheck_cfuncs
    show "n \<in>\<^sub>c \<nat>\<^sub>c"
      using assms(1) by auto
  next
    have "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>m,a\<rangle>,f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,indexed_sum \<circ>\<^sub>c \<langle>\<langle>m,metafunc (cnufatem f \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>)\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c zero =
          eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>m,a\<rangle>,f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c zero, indexed_sum \<circ>\<^sub>c \<langle>\<langle>m,metafunc (cnufatem f \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>)\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c zero\<rangle>"
      using assms(2-4) by (etcs_assocr, typecheck_cfuncs, smt (verit, best) cfunc_prod_comp comp_associative2)
    also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>m,a\<rangle>,f\<rangle>, zero\<rangle>, 
                     indexed_sum \<circ>\<^sub>c \<langle>\<langle>m,metafunc (cnufatem f \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>)\<rangle>,zero\<rangle>\<rangle>"
      using assms(2-4) by (typecheck_cfuncs, metis cart_prod_extract_right)
    also have "... = \<t>"
      using assms(2-4) by (typecheck_cfuncs, smt (verit, best) cart_prod_extract_left cnufatem_metafunc comp_associative2 eq_pred_iff_eq indexed_sum_uppr_eq_lwr)
    then show "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>m,a\<rangle>,f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,
                               indexed_sum \<circ>\<^sub>c \<langle>\<langle>m,metafunc (cnufatem f \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>)\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c zero = \<t>"
      using calculation by auto
  next
    fix n 
    assume n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
    assume eq_pred_ind_hyp: "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>m,a\<rangle>,f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,
             indexed_sum \<circ>\<^sub>c \<langle>\<langle>m,metafunc (cnufatem f \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>)\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c n =  \<t>"
    have induction_hypothesis: "indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>m,a\<rangle>,f\<rangle>, n\<rangle> = 
                                indexed_sum \<circ>\<^sub>c \<langle>\<langle>m,metafunc (cnufatem f \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>)\<rangle>,n\<rangle>"
    proof - 
      have "\<t> = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>m,a\<rangle>,f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c n,
             indexed_sum \<circ>\<^sub>c \<langle>\<langle>m,metafunc (cnufatem f \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>)\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle> \<circ>\<^sub>c n\<rangle>"
        using assms(2-4) eq_pred_ind_hyp by (-, typecheck_cfuncs, smt (verit, ccfv_SIG) cfunc_prod_comp comp_associative2)
      also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>m,a\<rangle>,f\<rangle>, n\<rangle>,
             indexed_sum \<circ>\<^sub>c \<langle>\<langle>m,metafunc (cnufatem f \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>)\<rangle>,n\<rangle>\<rangle>"
        using assms(2-4) by (typecheck_cfuncs, metis cart_prod_extract_right)
      then show ?thesis
        using assms(2-4) by (typecheck_cfuncs, metis calculation eq_pred_iff_eq_conv2)
    qed
    have induction_conclusion: "indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>m,a\<rangle>,f\<rangle>, successor \<circ>\<^sub>c n\<rangle> = 
                                indexed_sum \<circ>\<^sub>c \<langle>\<langle>m,metafunc (cnufatem f \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>)\<rangle>,successor \<circ>\<^sub>c n\<rangle>"
    proof - 
      have "indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>m,a\<rangle>,f\<rangle>, successor \<circ>\<^sub>c n\<rangle> = 
                         (indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>m,a\<rangle>,f\<rangle>, n\<rangle>) +\<^sub>\<nat> (cnufatem f \<circ>\<^sub>c ((add2 \<circ>\<^sub>c \<langle>m,a\<rangle>) +\<^sub>\<nat> (successor \<circ>\<^sub>c n)))"
        using assms indexed_sum_tail_term by (typecheck_cfuncs, presburger)
      also have "... = (indexed_sum \<circ>\<^sub>c \<langle>\<langle>m,metafunc (cnufatem f \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>)\<rangle>,n\<rangle>)
                                           +\<^sub>\<nat> (cnufatem f \<circ>\<^sub>c ((add2 \<circ>\<^sub>c \<langle>m,a\<rangle>) +\<^sub>\<nat> (successor \<circ>\<^sub>c n)))"
        using assms induction_hypothesis by argo
      also have "... = (indexed_sum \<circ>\<^sub>c \<langle>\<langle>m,metafunc (cnufatem f \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>)\<rangle>,n\<rangle>) +\<^sub>\<nat>
            ((cnufatem f \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c (m +\<^sub>\<nat> (successor \<circ>\<^sub>c n)))"
        using assms(2-4) by (etcs_assocr,typecheck_cfuncs, smt (verit, ccfv_threshold) add_associates add_commutes add_def cart_prod_extract_left)
      also have "... =             (indexed_sum \<circ>\<^sub>c \<langle>\<langle>m,metafunc (cnufatem f \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>)\<rangle>,n\<rangle>) +\<^sub>\<nat>
            ((cnufatem (metafunc (cnufatem f \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>))) \<circ>\<^sub>c (m +\<^sub>\<nat> (successor \<circ>\<^sub>c n)))"
        using assms(2-4) by (typecheck_cfuncs, simp add: cnufatem_metafunc)
      also have "... = indexed_sum \<circ>\<^sub>c \<langle>\<langle>m,metafunc (cnufatem f \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>)\<rangle>,successor \<circ>\<^sub>c n\<rangle>"
        using assms(2-4) indexed_sum_tail_term by (typecheck_cfuncs, presburger)
      then show ?thesis
        using calculation by auto
    qed
    show "(eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>m,a\<rangle>,f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>,
               indexed_sum \<circ>\<^sub>c \<langle>\<langle>m,metafunc (cnufatem f \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>)\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>,id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle>) \<circ>\<^sub>c successor \<circ>\<^sub>c n = \<t>"
    proof - 
      have "\<t> = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>m,a\<rangle>,f\<rangle>, successor \<circ>\<^sub>c n\<rangle>,
               indexed_sum \<circ>\<^sub>c \<langle>\<langle>m,metafunc (cnufatem f \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>)\<rangle>,successor \<circ>\<^sub>c n\<rangle>\<rangle>"
        using assms(2-4) by (typecheck_cfuncs, metis eq_pred_iff_eq induction_conclusion)
      also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>m,a\<rangle>,f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor \<circ>\<^sub>c n , id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor \<circ>\<^sub>c n\<rangle>,
               indexed_sum \<circ>\<^sub>c \<langle>\<langle>m,metafunc (cnufatem f \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>)\<rangle>\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub> \<circ>\<^sub>c successor \<circ>\<^sub>c n, id\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c successor \<circ>\<^sub>c n\<rangle>\<rangle>"
        using assms(2-4) by (typecheck_cfuncs, metis id_left_unit2 id_right_unit2 terminal_func_comp_elem)
      also have "... = eq_pred \<nat>\<^sub>c \<circ>\<^sub>c \<langle>indexed_sum \<circ>\<^sub>c \<langle>\<langle>add2 \<circ>\<^sub>c \<langle>m,a\<rangle>,f\<rangle> \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id\<^sub>c \<nat>\<^sub>c\<rangle>,
               indexed_sum \<circ>\<^sub>c \<langle>\<langle>m,metafunc (cnufatem f \<circ>\<^sub>c add2 \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,a \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>)\<rangle>\<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>, id\<^sub>c \<nat>\<^sub>c\<rangle>\<rangle> \<circ>\<^sub>c successor \<circ>\<^sub>c n"
        using assms(2-4) by (typecheck_cfuncs, smt (verit, ccfv_SIG) cfunc_prod_comp comp_associative2)
      then show ?thesis
        using assms(2-4) by (typecheck_cfuncs, metis calculation comp_associative2)
    qed
  qed
  then show ?thesis
    using assms by (-, typecheck_cfuncs, smt (verit, best) cfunc_prod_comp comp_associative2 eq_pred_iff_eq id_left_unit2 id_right_unit2 terminal_func_comp_elem)
qed


lemma mult_index_sum:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "f \<in>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
  assumes "m \<in>\<^sub>c \<nat>\<^sub>c"
  oops







end