# Cheap, separate measurements of the scalar stages in the original H2 formula.
if LoadPackage("kbmag") <> true then Error("KBMAG unavailable"); fi;
Read("Algorithms.g");; Read("Library-of-groups.g");; Read("tests/cases.g");;
if not IsPrimeInt(ResearchPrime) then Error("coefficient must be prime"); fi;
ResearchInput := ResearchCases.(ResearchCase);;
ResearchF := ResearchInput[1];; ResearchR := ResearchInput[2];;
ResearchGenerators := GeneratorsOfGroup(ResearchF);;
ResearchFF := ListX(ResearchGenerators,ResearchGenerators,Comm);;
ResearchPowers := List(ResearchR,x->x^ResearchPrime);;
Print("GAP ",GAPInfo.Version,"; KBMAG ",PackageInfo("kbmag")[1].Version,"\n");
ResearchT := Runtime();;
ResearchA := Tor(ResearchF,ResearchR,ResearchPrime);;
Print("SCALAR a=",ResearchA," cpu_ms=",Runtime()-ResearchT,"\n");
ResearchT := Runtime();;
ResearchB := PrimePrimaryRank(ResearchF,Concatenation(ResearchR,ResearchFF),ResearchPrime);;
Print("SCALAR b=",ResearchB," cpu_ms=",Runtime()-ResearchT,"\n");
ResearchT := Runtime();;
ResearchC := PrimePrimaryRank(ResearchF,Concatenation(ResearchPowers,ResearchFF),ResearchPrime);;
Print("SCALAR c=",ResearchC," cpu_ms=",Runtime()-ResearchT,"\n");
Print("H1=",FirstHomologyCoefficients(ResearchF,ResearchR,ResearchPrime),
      "; exponent_rank=",ResearchC-ResearchB,
      "; generators=",Length(ResearchGenerators),"; relators=",Length(ResearchR),"\n");
Print("COMPLETED abelian stages only (no H2 bound computed)\n");
QUIT;
