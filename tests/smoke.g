# Run from the repository root with gap -q -b --quitonbreak tests/smoke.g.
if LoadPackage("kbmag") <> true then Error("KBMAG is required"); fi;
Read("Algorithms.g");;
CheckResearch := function(actual, expected, label)
    if actual <> expected then
        Error(label, ": expected ", expected, ", got ", actual);
    fi;
end;;
Print("GAP ", GAPInfo.Version, "; KBMAG ", PackageInfo("kbmag")[1].Version, "\n");

# Known homology, including a free summand and valuation > 1.
SmokeF := FreeGroup("x", "y");;
SmokeR := [SmokeF.1^9, Comm(SmokeF.1, SmokeF.2)];;
CheckResearch(FirstHomologyCoefficients(SmokeF, SmokeR, 3), 2, "H1(C9 x Z; F3)");
CheckResearch(Tor(SmokeF, SmokeR, 3), 1, "Tor(C9 x Z; F3)");
CheckResearch(PrimePrimaryRank(SmokeF, SmokeR, 3), 2, "3-primary valuation");
CheckResearch(FirstHomologyCoefficients(SmokeF, SmokeR, 2), 1, "H1(C9 x Z; F2)");
CheckResearch(Tor(SmokeF, SmokeR, 2), 0, "Tor(C9 x Z; F2)");

SmokeC := FreeGroup("c");; SmokeCR := [SmokeC.1^3];;
CheckResearch(IsOne(Reduce_Word(SmokeC, SmokeCR, SmokeC.1^9, [], 3)), true,
              "external KBMAG reduction");
CheckResearch(IsOne(Reduce_Word(SmokeC, SmokeCR, SmokeC.1^3, [], 3)), false,
              "nontrivial relator class in C9");
CheckResearch(FindBasis(SmokeC, SmokeCR, 3, SmokeCR)[2], 1, "C3 relation module");
CheckResearch(SecondHomologyCoefficients(SmokeC, SmokeCR, 3, SmokeCR)[2], 1,
              "H2(C3; F3)");
CheckResearch(SecondHomologyCoefficients(SmokeC, SmokeCR, 2, SmokeCR)[2], 0,
              "H2(C3; F2)");
CheckResearch(SecondHomologyCoefficients_large(SmokeC, SmokeCR, 3, SmokeCR)[2], 1,
              "large-parameter path on C3");
SmokeV := FreeGroup("u", "v");;
SmokeVR := [SmokeV.1^2, SmokeV.2^2, Comm(SmokeV.1, SmokeV.2)];;
CheckResearch(SecondHomologyCoefficients(SmokeV, SmokeVR, 2, SmokeVR)[2], 3,
              "H2(C2 x C2; F2)");

# Exercise both presentation helpers without fixing a Tietze output ordering.
SmokeP := PresentationOfFiniteGroup(AlternatingGroup(5));;
CheckResearch(Size(SmokeP[1]), 60, "finite presentation helper");
CheckResearch(AbelianInvariants(SmokeP[1]), [], "A5 abelianization");
SmokeQ := PresentationOfFpGroup(SmokeC/SmokeCR);;
CheckResearch(Size(SmokeQ[2]), 3, "fp presentation helper");
CheckResearch(IsBijective(SmokeQ[1]), true, "simplification isomorphism");
Print("PASS: 16 research smoke checks\n");
QUIT;
