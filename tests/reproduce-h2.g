# Invoked by scripts/reproduce-h2.sh; the shell supplies Research* variables.
if LoadPackage("kbmag") <> true then Error("KBMAG is required"); fi;
Read("Algorithms.g");; Read("Library-of-groups.g");;
Read("tests/cases.g");;
if not ResearchCase in ["SL2F2","SL2F3","SL2F5"] then
    Error("Full H2 runs for expensive presentations are deferred; benchmark components instead");
fi;
if not IsPrimeInt(ResearchPrime) then Error("coefficient must be prime"); fi;
ResearchInput := ResearchCases.(ResearchCase);;
Print("GAP ", GAPInfo.Version, "; KBMAG ", PackageInfo("kbmag")[1].Version, "\n");
Print("case=", ResearchCase, "; coefficient_prime=", ResearchPrime,
      "; large=", ResearchLarge, "; candidates=all defining relators\n");
Print("generators=", Length(GeneratorsOfGroup(ResearchInput[1])),
      "; relators=", Length(ResearchInput[2]), "; abelianization=",
      AbelianInvariants(ResearchInput[1]/ResearchInput[2]), "\n");
ResearchStart := Runtime();;
if IsBound(ResearchDiagnostics) and ResearchDiagnostics then
    # Diagnostics only: no function rebinding or mathematical option changes.
    SetInfoLevel(InfoRWS,1);
    ResearchProfiled := [SecondHomologyCoefficients, SecondHomologyCoefficients_large,
        FindBasis, FindBasis2ndHom_large, Reduce_Word, Reduce_Word2ndHom_large,
        Tor, PrimePrimaryRank, KBRWS, WriteRWS, UpdateRWS, ReduceWordRWS];;
    ProfileFunctions(ResearchProfiled);
fi;
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
if IsBound(ResearchDiagnostics) and ResearchDiagnostics then
    UnprofileFunctions(ResearchProfiled);
    Print("PROFILE_COLUMNS=count,self_ms,child_ms,self_bytes,child_bytes,package,function\n");
    ResearchProfile := ProfileInfo(ResearchProfiled,0,0);;
    for row in ResearchProfile.prof do
        Print("PROFILE_ROW=",row,"\n");
    od;
fi;
QUIT;
