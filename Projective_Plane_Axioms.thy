theory Projective_Plane_Axioms
  imports Main
begin

(* Author: Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk .*)

text \<open>
Contents:
\<^item> We introduce the types of points and lines and an incidence relation between them.
\<^item> A set of axioms for the projective plane (the models of these axioms are 
n-dimensional with n \<ge> 2). 
\<close>

section \<open>The Axioms of the Projective Plane\<close>


locale projective_plane =
  (* One has a type of points *)
  (* One has a type of lines *)
  (* One has an incidence relation between points and lines *)
  (* which is all expressed in the following line *)
  fixes incid :: "'point \<Rightarrow> 'line \<Rightarrow> bool"

  (* Ax1: Any two (distinct) points lie on a (unique) line *)
  assumes ax1: "\<exists>l. incid P l \<and> incid Q l"

  (* Ax2: Any two (distinct) lines meet in a (unique) point *)
  assumes ax2: "\<exists>P. incid P l \<and> incid P m"

  (* The uniqueness part *)
  assumes ax_uniqueness: "\<lbrakk>incid P l; incid Q l; incid P m; incid Q m\<rbrakk> \<Longrightarrow>  P = Q \<or> l = m"

  (* Ax3: There exists four points such that no three of them are collinear *)
  assumes ax3: "\<exists>A B C D. (A \<noteq> B) \<and> (A \<noteq> C) \<and> (A \<noteq> D) \<and> (B \<noteq> C) \<and> (B \<noteq> D) \<and> (C \<noteq> D) \<and> (\<forall>l. 
              (incid A l \<and> incid B l \<longrightarrow> \<not>(incid C l) \<and> \<not>(incid D l)) \<and>
              (incid A l \<and> incid C l \<longrightarrow> \<not>(incid B l) \<and> \<not>(incid D l)) \<and>
              (incid A l \<and> incid D l \<longrightarrow> \<not>(incid B l) \<and> \<not>(incid C l)) \<and>
              (incid B l \<and> incid C l \<longrightarrow> \<not>(incid A l) \<and> \<not>(incid D l)) \<and>
              (incid B l \<and> incid D l \<longrightarrow> \<not>(incid A l) \<and> \<not>(incid C l)) \<and>
              (incid C l \<and> incid D l \<longrightarrow> \<not>(incid A l) \<and> \<not>(incid B l)))"


end