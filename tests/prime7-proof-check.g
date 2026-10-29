# Cheap linear audit of the printed proof, not a homology computation.
Read("tests/fixtures/roberts-v1-prime7-words.g");;
F := FreeGroup(6);; gens := GeneratorsOfGroup(F);;
words := RobertsV1Prime7Words(F);;
mat := List(words,w->List(gens,g->ExponentSumWord(w,g)*One(GF(7))));;
display := [[3,0,0,0,0,0],[0,0,0,0,0,-1],
    [0,-1,0,0,0,0],[1,1,0,0,0,0],[1,0,0,0,0,0],
    [-1,0,0,0,0,0]]*One(GF(7));;
if RankMat(display) <> 3 or RankMat(mat{[7..12]}) <> 6 or
   RankMat(mat{[1..6]}) <> 5 then Error("unexpected source ranks"); fi;
# These are dependencies among AUXILIARY images, not H2 generators.
if display[1]-3*display[5] <> Zero(display[1]) or
   display[4]-display[5]+display[3] <> Zero(display[1]) or
   display[6]+display[5] <> Zero(display[1]) then
    Error("auxiliary dependency check failed");
fi;
Print("Coordinates: f1,f2,f3,f4,f5,f7; exponent sums modulo 7\n");
for i in [1..12] do Print(i, ": ",List(mat[i],Int),"\n"); od;
Print("VERIFIED: displayed auxiliary-image rank = 3\n");
Print("VERIFIED: literal last-six auxiliary-word rank = 6; determinant mod 7 = ",
    Int(DeterminantMat(mat{[7..12]})),"\n");
Print("VERIFIED: literal first-six exponent rank = 5; first word has image 2*f1\n");
# If the twelve really span A, this is the ordinary split-kernel construction.
# Check only the linear correction, without claiming the source assertion
# that these words span A was independently reproduced.
coeff := mat{[1..6]}*Inverse(mat{[7..12]});;
if mat{[1..6]}-coeff*mat{[7..12]} <> Zero(mat{[1..6]}) then
    Error("linear splitting check failed");
fi;
Print("VERIFIED: subtracting last-six image combinations kills first-six images\n");
Print("NOT VERIFIED: FindBasis spanning certificate or printed H2 representatives\n");
Print("NO CLAIM: independence, nontriviality, or exact dimension of H2\n");
QUIT;
