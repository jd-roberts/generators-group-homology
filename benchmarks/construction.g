# Build the first candidate's rewriting input; NEVER call completion here.
if LoadPackage("kbmag") <> true then Error("KBMAG unavailable"); fi;
Read("Algorithms.g");; Read("Library-of-groups.g");; Read("tests/cases.g");;
if not IsPrimeInt(ResearchPrime) then Error("coefficient must be prime"); fi;
ResearchInput := ResearchCases.(ResearchCase);;
ResearchF := ResearchInput[1];; ResearchR := ResearchInput[2];;
Print("GAP ",GAPInfo.Version,"; KBMAG ",PackageInfo("kbmag")[1].Version,"\n");
ResearchT := Runtime();;
ResearchPowers := List(ResearchR,x->x^ResearchPrime);;
ResearchComm := ListX(GeneratorsOfGroup(ResearchF),ResearchR,Comm);;
ResearchS := Difference(ResearchR,[ResearchR[1]]);;
ResearchRelations := Concatenation(ResearchComm,ResearchPowers,ResearchS);;
Print("COMPONENT relations cpu_ms=",Runtime()-ResearchT,
      " count=",Length(ResearchRelations)," length=",Sum(List(ResearchRelations,Length)),"\n");
ResearchT := Runtime();;
ResearchQ := ResearchF/ResearchRelations;;
Print("COMPONENT quotient cpu_ms=",Runtime()-ResearchT,"\n");
ResearchT := Runtime();;
ResearchSystem := KBMAGRewritingSystem(ResearchQ);;
Print("COMPONENT rewriting_constructor cpu_ms=",Runtime()-ResearchT,
      " initial_rules=",Length(Rules(ResearchSystem)),"\n");
ResearchOptions := OptionsRecordOfKBMAGRewritingSystem(ResearchSystem);;
if ResearchLarge then
    ResearchOptions.maxeqns := 10000000;; ResearchOptions.tindyint := 1000;;
else
    ResearchOptions.maxeqns := 500000;; ResearchOptions.tindyint := 100;;
fi;
ResearchT := Runtime();;
ResearchFilename := Filename(DirectoryTemporary(),"benchmark-rws");;
WriteRWS(ResearchSystem,ResearchFilename);
Print("COMPONENT serialization cpu_ms=",Runtime()-ResearchT,"\n");
Print("COMPLETED construction only; no MakeConfluent, KnuthBendix, or H2 computation\n");
QUIT;
