# Invoked by scripts/reproduce-h2.sh; the shell supplies Research* variables.
if LoadPackage("kbmag") <> true then Error("KBMAG is required"); fi;
Read("Algorithms.g");; Read("Library-of-groups.g");;
ResearchCases := rec(
    G3 := [F3,k3], G5 := [F5,k5], G7 := [F7,k7], G11 := [F11,k11],
    GL2Z := [Free6,R6], SL2Z := [S,rels], SL2F2 := [Free0,R0],
    SL2F3 := [Free3,R3], SL2F5 := [Free5,R5], SL2Zi := [Free8,R8],
    SL2w := [Free1,R1], SL2Zneg5 := [Free9,R9], PSL2Z := [Free7,R7]
);;
if not IsPrimeInt(ResearchPrime) then Error("coefficient must be prime"); fi;
ResearchInput := ResearchCases.(ResearchCase);;
Print("GAP ", GAPInfo.Version, "; KBMAG ", PackageInfo("kbmag")[1].Version, "\n");
Print("case=", ResearchCase, "; coefficient_prime=", ResearchPrime,
      "; large=", ResearchLarge, "; candidates=all defining relators\n");
Print("generators=", Length(GeneratorsOfGroup(ResearchInput[1])),
      "; relators=", Length(ResearchInput[2]), "; abelianization=",
      AbelianInvariants(ResearchInput[1]/ResearchInput[2]), "\n");
ResearchStart := Runtime();;
if ResearchLarge then
    ResearchAnswer := SecondHomologyCoefficients_large(
        ResearchInput[1],ResearchInput[2],ResearchPrime,ResearchInput[2]);;
else
    ResearchAnswer := SecondHomologyCoefficients(
        ResearchInput[1],ResearchInput[2],ResearchPrime,ResearchInput[2]);;
fi;
Print("upper_bound=", ResearchAnswer[2], "; GAP_runtime_ms=", Runtime()-ResearchStart,
      "\nremaining_relators=", ResearchAnswer[1],
      "\nreductions_in_candidate_order=", ResearchAnswer[3], "\n");
Print("COMPLETED (upper bound; confluence status is not exposed by the original algorithm)\n");
QUIT;
