# Source-word linear calculation only. No quotient enumeration or KBMAG.
# Coordinates f1,f2,f3,f4,f5,f7 are renamed z,u1,u2,u3,a,b1.
Read("tests/fixtures/roberts-v1-prime7-words.g");;

Prime7CorrectionCalculation := function()
    local F, gens, words, integerImages, first, auxiliary, inverse,
          coefficients, signed, corrected, i, j, exponentSums, printed,
          z, u1, u2, u3, a, b1, originalF, inclusion, originalWords;
    F := FreeGroup("z","u1","u2","u3","a","b1");
    gens := GeneratorsOfGroup(F);
    z:=gens[1]; u1:=gens[2]; u2:=gens[3]; u3:=gens[4];
    a:=gens[5]; b1:=gens[6];
    words := RobertsV1Prime7Words(F);
    integerImages := List(words,w->List(gens,g->ExponentSumWord(w,g)));
    first := integerImages{[1..6]}*One(GF(7));
    auxiliary := integerImages{[7..12]}*One(GF(7));
    inverse := Inverse(auxiliary);
    coefficients := first*inverse;
    signed := List(coefficients,row->List(row,function(x)
        local n;
        n:=Int(x); if n>3 then return n-7; fi; return n;
    end));
    corrected := [];
    for i in [1..6] do
        corrected[i] := words[i];
        for j in [1..6] do
            corrected[i] := corrected[i]*words[j+6]^(-signed[i][j]);
        od;
    od;
    exponentSums := List(corrected,w->List(gens,g->ExponentSumWord(w,g)));

    # Independent literal transcription of the FINAL six-word list, R20 p.10.
    # This fixes the named-generator convention; it is not an inferred
    # historical GAP generator numbering. f7 here is b1, NOT original F14.7=b0.
    printed := [z*a*z*a^-1,
        u1*u2*u1^-1*u2^-1,
        u1*a*u1*a^-1,
        b1*a^-1*b1*a^-1*b1*a,
        u2*b1*z^-2*b1*z*b1^-2*a^-1*u2*z^-1*a^-1*b1^-1,
        u3*b1*z^2*b1^-2*z^2*b1*a^-1*z^-2*u3*z^-1*a^-1*b1^-1];

    # Lift to the original 14-generator free group by the literal inclusion
    # of z,u1,u2,u3,a,b1. No inverse Tietze/relator-module isomorphism asserted.
    originalF := FreeGroup("z","u1","u2","u3","a","b",
        "b0","b1","b2","b3","b4","b5","b6","w");
    inclusion := GroupHomomorphismByImages(F,originalF,gens,
        GeneratorsOfGroup(originalF){[1,2,3,4,5,8]});
    originalWords := List(corrected,w->Image(inclusion,w));
    return rec(F:=F, words:=words, integerImages:=integerImages,
        first:=first, auxiliary:=auxiliary, inverse:=inverse,
        coefficients:=coefficients, signed:=signed, corrected:=corrected,
        exponentSums:=exponentSums, printed:=printed,
        originalF:=originalF, originalWords:=originalWords);
end;
