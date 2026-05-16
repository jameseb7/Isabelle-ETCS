theory Cfunc
  imports FOL
begin

typedecl cset
instance cset :: "term" ..
typedecl cfunc
instance cfunc :: "term" ..

axiomatization
  domain :: "cfunc \<Rightarrow> cset" and
  codomain :: "cfunc \<Rightarrow> cset" and
  comp :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" (infixr "\<circ>\<^sub>c" 55) and
  id :: "cset \<Rightarrow> cfunc" ("id\<^sub>c") 
where
  domain_comp: "domain(g) = codomain(f) \<Longrightarrow> domain(g \<circ>\<^sub>c f) = domain(f)" and
  codomain_comp: "domain(g) = codomain(f) \<Longrightarrow> codomain(g \<circ>\<^sub>c f) = codomain(g)" and
  comp_associative: "domain(h) = codomain(g) \<Longrightarrow> domain(g) = codomain(f) \<Longrightarrow> h \<circ>\<^sub>c (g \<circ>\<^sub>c f) = (h \<circ>\<^sub>c g) \<circ>\<^sub>c f" and
  id_domain: "domain(id(X)) = X" and
  id_codomain: "codomain(id(X)) = X" and
  id_right_unit: "f \<circ>\<^sub>c id(domain(f)) = f" and
  id_left_unit: "id (codomain(f)) \<circ>\<^sub>c f = f"

