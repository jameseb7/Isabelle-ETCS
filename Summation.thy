theory Summation
  imports Add
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




definition indexed_sum :: cfunc where
  "indexed_sum  = (right_cart_proj \<nat>\<^sub>c  (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c indexed_sum1)\<^sup>\<flat>"

lemma indexed_sum_type[type_rule]: 
  "indexed_sum : ((\<nat>\<^sub>c \<times>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)) \<times>\<^sub>c \<nat>\<^sub>c) \<rightarrow> \<nat>\<^sub>c"
  unfolding  indexed_sum_def by typecheck_cfuncs



lemma indexed_sum_uppr_eq_lwr:
  assumes "n \<in>\<^sub>c \<nat>\<^sub>c"
  assumes "f \<in>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>"
  shows "indexed_sum \<circ>\<^sub>c \<langle>\<langle>n, f\<rangle>, zero\<rangle> =   cnufatem f \<circ>\<^sub>c n"
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
    using assms by (typecheck_cfuncs, simp add: cfunc_type_def comp_associative inv_transpose_func_def2)
  also have "... = eval_func  \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)) \<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>,(eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) one)\<^sup>\<sharp>\<rangle>"
    using assms cfunc_cross_prod_comp_cfunc_prod id_left_unit2 right_cart_proj_cfunc_prod by (typecheck_cfuncs, force)
  also have "... = eval_func  \<nat>\<^sub>c (\<nat>\<^sub>c \<times>\<^sub>c (\<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)) \<circ>\<^sub>c (id (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<times>\<^sub>f (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) one)\<^sup>\<sharp>)\<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>, id one\<rangle>"
    using assms cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2 by (typecheck_cfuncs, force)
  also have "... = (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) one) \<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>, id one\<rangle>"
    using assms comp_associative2 transpose_func_def by (typecheck_cfuncs, force)
  also have "... = eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>n,f\<rangle>"
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
  shows "indexed_sum \<circ>\<^sub>c \<langle>\<langle>n, f\<rangle>, successor \<circ>\<^sub>c m\<rangle> =   indexed_sum \<circ>\<^sub>c \<langle>\<langle>n, f\<rangle>, m\<rangle> +\<^sub>\<nat> (cnufatem f \<circ>\<^sub>c successor \<circ>\<^sub>c m)"
proof (unfold indexed_sum_def)
  have "(right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>) \<circ>\<^sub>c indexed_sum1)\<^sup>\<flat> \<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>,successor \<circ>\<^sub>c m\<rangle> = 
        right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<^sup>\<flat>  \<circ>\<^sub>c (id(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) \<times>\<^sub>f indexed_sum1) \<circ>\<^sub>c \<langle>\<langle>n,f\<rangle>,successor \<circ>\<^sub>c m\<rangle>"
    using assms comp_associative2 inv_transpose_of_composition by (typecheck_cfuncs, force)
  also have "... = right_cart_proj \<nat>\<^sub>c (\<nat>\<^sub>c\<^bsup>(\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>)\<^esup>)\<^sup>\<flat>  \<circ>\<^sub>c  \<langle>\<langle>n,f\<rangle>,\<langle>successor \<circ>\<^sub>c m, (eval_func \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c left_cart_proj (\<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c\<^bsup>\<nat>\<^sub>c\<^esup>) one)\<^sup>\<sharp>\<rangle>\<rangle>"
    using assms apply typecheck_cfuncs






(*
definition indexed_sum :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" where
  "indexed_sum f low = (THE u. u : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c 
    \<and> u \<circ>\<^sub>c zero = \<langle>low, f \<circ>\<^sub>c low\<rangle> 
    \<and> \<langle>successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c, add2 \<circ>\<^sub>c (f \<times>\<^sub>f id \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c u = u \<circ>\<^sub>c successor)"

lemma indexed_sum_def2:
  assumes f_type[type_rule]: "f : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" and low_type[type_rule]: "low \<in>\<^sub>c \<nat>\<^sub>c" 
  shows "indexed_sum f low : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c 
    \<and> (indexed_sum f low) \<circ>\<^sub>c zero = \<langle>low, f \<circ>\<^sub>c low\<rangle> 
    \<and> \<langle>successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c, add2 \<circ>\<^sub>c (f \<times>\<^sub>f id \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c indexed_sum f low = (indexed_sum f low) \<circ>\<^sub>c successor"
  unfolding indexed_sum_def
  by (rule theI', typecheck_cfuncs, simp add: natural_number_object_property2)

lemma indexed_sum_type[type_rule]:
  assumes f_type[type_rule]: "f : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" and low_type[type_rule]: "low \<in>\<^sub>c \<nat>\<^sub>c" 
  shows "indexed_sum f low : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<times>\<^sub>c \<nat>\<^sub>c"
  using indexed_sum_def2 assms by auto

lemma indexed_sum_zero:
  assumes f_type[type_rule]: "f : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" and low_type[type_rule]: "low \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(indexed_sum f low) \<circ>\<^sub>c zero = \<langle>low, f \<circ>\<^sub>c low\<rangle>"
  using indexed_sum_def2 assms by auto

lemma indexed_sum_successor:
  assumes f_type[type_rule]: "f : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" and low_type[type_rule]: "low \<in>\<^sub>c \<nat>\<^sub>c"
  shows "indexed_sum f low \<circ>\<^sub>c successor 
    = \<langle>successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c, add2 \<circ>\<^sub>c (f \<times>\<^sub>f id \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c indexed_sum f low"
  using indexed_sum_def2 assms by auto

lemma 
  assumes f_type[type_rule]: "f : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" and low_type[type_rule]: "low \<in>\<^sub>c \<nat>\<^sub>c"
  assumes n_type[type_rule]: "n \<in>\<^sub>c \<nat>\<^sub>c"
  shows "left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c indexed_sum f low = (add1 \<circ>\<^sub>c low)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c, \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
proof (rule natural_number_object_func_unique[where X="\<nat>\<^sub>c", where f=successor])
  show "left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c indexed_sum f low : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by typecheck_cfuncs
  show "(add1 \<circ>\<^sub>c low)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle> : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by typecheck_cfuncs
  show "successor : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c"
    by typecheck_cfuncs

  show "(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c indexed_sum f low) \<circ>\<^sub>c zero = ((add1 \<circ>\<^sub>c low)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c zero"
  proof - 
    have "(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c indexed_sum f low) \<circ>\<^sub>c zero = left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c  \<langle>low, f \<circ>\<^sub>c low\<rangle>"
      using  indexed_sum_zero comp_associative2 by (typecheck_cfuncs, force)
    also have "... = low"
      using comp_type f_type left_cart_proj_cfunc_prod low_type by auto
    also have "... = add2 \<circ>\<^sub>c \<langle>zero, low\<rangle>"
      using add_def add_respects_zero_on_left low_type by presburger
    also have "... = (eval_func \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c  (id \<nat>\<^sub>c \<times>\<^sub>f add1 \<circ>\<^sub>c low) \<circ>\<^sub>c \<langle>zero, id one\<rangle>"
      by (typecheck_cfuncs, simp add: add2_apply cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2)
    also have "... = (add1 \<circ>\<^sub>c low)\<^sup>\<flat>  \<circ>\<^sub>c \<langle>zero, id one\<rangle>"
      using comp_associative2 inv_transpose_func_def2 by (typecheck_cfuncs, auto)
    also have "... = ((add1 \<circ>\<^sub>c low)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c zero"
      by (typecheck_cfuncs, metis id_left_unit2 right_param_def2 right_param_on_el)
    then show ?thesis
      by (simp add: calculation)
  qed

  show "(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c indexed_sum f low) \<circ>\<^sub>c successor = successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c indexed_sum f low"
  proof - 
    have "(left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c indexed_sum f low) \<circ>\<^sub>c successor =  left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (\<langle>successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c, add2 \<circ>\<^sub>c (f \<times>\<^sub>f id \<nat>\<^sub>c)\<rangle> \<circ>\<^sub>c indexed_sum f low)"
      by (typecheck_cfuncs, metis comp_associative2 indexed_sum_successor)
    also have "... = successor \<circ>\<^sub>c left_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c indexed_sum f low"
      using left_cart_proj_cfunc_prod by (etcs_assocl, typecheck_cfuncs, presburger)
    then show ?thesis
      using calculation by presburger
  qed

  show "((add1 \<circ>\<^sub>c low)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c successor = successor \<circ>\<^sub>c (add1 \<circ>\<^sub>c low)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
  proof - 
    have "((add1 \<circ>\<^sub>c low)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c successor = ((eval_func \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c  (id \<nat>\<^sub>c \<times>\<^sub>f add1 \<circ>\<^sub>c low) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c successor"
      by (typecheck_cfuncs, simp add: comp_associative2 inv_transpose_func_def2)
    also have "... =  (((eval_func \<nat>\<^sub>c \<nat>\<^sub>c) \<circ>\<^sub>c  (id \<nat>\<^sub>c \<times>\<^sub>f add1))  \<circ>\<^sub>c ((id \<nat>\<^sub>c \<times>\<^sub>f low) \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>)) \<circ>\<^sub>c successor"
      by (typecheck_cfuncs, smt (z3) comp_associative2 inv_transpose_func_def2 inv_transpose_of_composition)
    also have "... =  (add2   \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c, low \<circ>\<^sub>c  \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>) \<circ>\<^sub>c successor"
      using add2_def cfunc_cross_prod_comp_cfunc_prod id_right_unit2 by (typecheck_cfuncs, force)
    also have "... =  add2   \<circ>\<^sub>c \<langle>successor, low \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
      by (typecheck_cfuncs, smt (verit, best) cfunc_prod_comp comp_associative2 id_left_unit2 terminal_func_comp)
    also have "... = successor \<circ>\<^sub>c (add2   \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c , low \<circ>\<^sub>c \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>)"
      by (typecheck_cfuncs, metis add2_commutes_succ add2_respects_succ_right id_right_unit2)
    also have "... = successor \<circ>\<^sub>c (eval_func \<nat>\<^sub>c \<nat>\<^sub>c  \<circ>\<^sub>c (id \<nat>\<^sub>c \<times>\<^sub>f (add1 \<circ>\<^sub>c low)) \<circ>\<^sub>c \<langle>id \<nat>\<^sub>c ,  \<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>)"
      using add2_apply cfunc_cross_prod_comp_cfunc_prod comp_associative2 id_right_unit2 by (typecheck_cfuncs, force)
    also have "... = successor \<circ>\<^sub>c (add1 \<circ>\<^sub>c low)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id\<^sub>c \<nat>\<^sub>c,\<beta>\<^bsub>\<nat>\<^sub>c\<^esub>\<rangle>"
      using comp_associative2 inv_transpose_func_def2 by (typecheck_cfuncs, force)
    then show ?thesis
      using calculation by presburger
  qed
qed



lemma add_indexed_sum:
  assumes f_type[type_rule]: "f : \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c" and low_type[type_rule]: "low \<in>\<^sub>c \<nat>\<^sub>c"
  assumes n1_type[type_rule]: "n1 \<in>\<^sub>c \<nat>\<^sub>c" and n2_type[type_rule]: "n2 \<in>\<^sub>c \<nat>\<^sub>c"
  shows "(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (indexed_sum f low) \<circ>\<^sub>c n1)
          +\<^sub>\<nat> (right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c(indexed_sum f (successor \<circ>\<^sub>c (low +\<^sub>\<nat> n1))) \<circ>\<^sub>c n2)
      = right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (indexed_sum f low) \<circ>\<^sub>c (n1 +\<^sub>\<nat> n2)"
proof(cases "n1 = zero")
  assume "n1 = zero"
  show ?thesis
  proof(cases "n2 = zero")
    assume "n2 = zero"
    
    have LHS:  "(right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c (indexed_sum f low) \<circ>\<^sub>c n1) +\<^sub>\<nat> (right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c(indexed_sum f (successor \<circ>\<^sub>c (low +\<^sub>\<nat> n1))) \<circ>\<^sub>c n2) =
               (f \<circ>\<^sub>c low) +\<^sub>\<nat> (f \<circ>\<^sub>c (successor \<circ>\<^sub>c low))"
      using \<open>n1 = zero\<close> \<open>n2 = zero\<close> add_respects_zero_on_right indexed_sum_zero right_cart_proj_cfunc_prod by (typecheck_cfuncs, presburger)

    have RHS: "right_cart_proj \<nat>\<^sub>c \<nat>\<^sub>c \<circ>\<^sub>c indexed_sum f low \<circ>\<^sub>c (n1 +\<^sub>\<nat> n2) = (f \<circ>\<^sub>c low)"
      by (typecheck_cfuncs, simp add: \<open>n1 = zero\<close> \<open>n2 = zero\<close> add_respects_zero_on_right indexed_sum_zero right_cart_proj_cfunc_prod)





*)
end