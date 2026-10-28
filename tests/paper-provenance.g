# Static/free-word and linear checks of uploaded sources. No completion.
# Run under the usual five-second quick-test limit.
Read("Library-of-groups.g");;
Read("tests/fixtures/anton-v1-relators.g");;
if AbelianInvariants(S5) <> [2] or AbelianInvariantsMultiplier(S5) <> [2] then
    Error("independent symmetric-group control check failed");
fi;
Print("VERIFIED Roberts 2009 finite control: Sigma5 has integral H1=C2 and H2=C2, so mod-2 H2 dimension is 2\n");
PaperR3 := AntonPaperR3(F3);; PaperR5 := AntonPaperR5(F5);;
if Length(PaperR3) <> 21 or Length(PaperR5) <> 39 then
    Error("unexpected source transcription size");
fi;
PaperLiteralMatches := 0;; PaperConjugateMatches := 0;;
for i in [1..21] do
    if i in [12,13,14] then
        PaperPair := [[F3.5,F3.6],[F3.5,F3.7],[F3.6,F3.7]][i-11];;
        PaperPrefix := PaperPair[1]*PaperPair[2];;
        if PaperR3[i] <> PaperPrefix*k3[i]*PaperPrefix^-1 then
            Error("commutator-convention comparison failed");
        fi;
        PaperConjugateMatches := PaperConjugateMatches+1;;
    else
        if PaperR3[i] <> k3[i] then Error("Anton case-3 mismatch at ",i); fi;
        PaperLiteralMatches := PaperLiteralMatches+1;;
    fi;
od;
for i in [1..39] do
    if PaperR5[i] <> k5[i] then Error("Anton case-5 mismatch at ",i); fi;
    PaperLiteralMatches := PaperLiteralMatches+1;;
od;
Print("VERIFIED Anton relator comparison: ",PaperLiteralMatches,
      " literal matches and ",PaperConjugateMatches," explicit commutator conjugacies\n");

# Lemma 7.4, p.21: only the cheap image/partition part is checked here.
PaperEIndices := [5,6,15,16,17,30,31,32,33,34,37];;
PaperNIndices := [1,2,3,4,7,8,9,10,11,12,13,14,18,19,20,
                  21,22,23,24,25,26,27,28,29,35,36,39,38];;
if Intersection(PaperEIndices,PaperNIndices) <> [] or
   Set(Concatenation(PaperEIndices,PaperNIndices)) <> [1..39] then
    Error("source e/n lists do not partition the 39 relators");
fi;
PaperGenerators := GeneratorsOfGroup(F5);;
PaperEMatrix := List(k5{PaperEIndices},r->
    List(PaperGenerators,g->ExponentSumWord(r,g)*One(GF(5))));;
if RankMat(PaperEMatrix) <> 11 or AbelianInvariants(G5) <> [] then
    Error("Anton scalar/image-basis check failed");
fi;
Print("VERIFIED Anton Lemma 7.4 linear portion: e has 11 words, complement 28, rank mod 5 = 11\n");
Print("NOT RUN: the 28 complement-word reductions needed to prove e spans the relation quotient\n");

# Roberts 2020 v1 p.10: formal exponent vectors of the displayed six images,
# using f1,f2,f3,f4,f5,f7 as coordinates. Their span in any abelian target
# has dimension at most three; this does not compute the target's homology.
PaperDisplayedImages := [[3,0,0,0,0,0],[0,0,0,0,0,-1],
    [0,-1,0,0,0,0],[1,1,0,0,0,0],[1,0,0,0,0,0],[-1,0,0,0,0,0]]*One(GF(7));;
if RankMat(PaperDisplayedImages) <> 3 then Error("displayed-image rank check failed"); fi;
Print("SOURCE CAUTION: 2020 v1 displayed six images have formal rank 3, so cannot be a six-element basis\n");
if AbelianInvariants(G11) = [] then Error("stored G11 no longer exhibits the audited discrepancy"); fi;
Print("SOURCE CAUTION: stored G11 is not perfect, unlike Anton's SE2 in Lemma 7.2\n");
Print("PASS: source comparisons and cheap linear checks; no arithmetic completion executed\n");
QUIT;
