theory Ceva
imports "Projective_Geometry.Pappus_Desargues"
begin

term col
term inter
term triangle

theorem "\<lbrakk>triangle A B C;
          is_a_proper_intersec D B C A P;
          is_a_proper_intersec E A C B P;
          is_a_proper_intersec F A B C P;
          F \<noteq> B;
          D \<noteq> C;
          E \<noteq> A;
          col A F B; col B D C; col C E A\<rbrakk> \<Longrightarrow> True"

end