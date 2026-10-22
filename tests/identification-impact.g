# A bounded independent check of the finite case-5 identification and impact.
# Uses GAP core's matrix groups / Schur-cover implementation, not KBMAG.
# Run: timeout --kill-after=2 5 gap -q -b --quitonbreak tests/identification-impact.g
Read("Library-of-groups.g");;
if Size(SL_2Z_5) <> 5 or not IsCyclic(SL_2Z_5) or
   AbelianInvariants(SL_2Z_5) <> [5] then
    Error("unexpected change to the stored case-5 presentation");
fi;
ImpactMatrixGroup := SL(2,5);;
ImpactH1 := AbelianInvariants(ImpactMatrixGroup);;
ImpactH2 := AbelianInvariantsMultiplier(ImpactMatrixGroup);;
if Size(ImpactMatrixGroup) <> 120 or ImpactH1 <> [] or ImpactH2 <> [] then
    Error("independent SL(2,5) homology check failed");
fi;
Print("GAP ",GAPInfo.Version,"\n");
Print("stored Free5/R5: order=5, cyclic=true, H1_integral=[5]\n");
Print("matrix SL(2,5): order=120, H1_integral=",ImpactH1,
      ", H2_integral_multiplier=",ImpactH2,"\n");
Print("UCT consequence: matrix H1 and H2 over every prime field vanish\n");
Print("Cyclic-resolution consequence: stored C5 has H1 and H2 dimension 1 at characteristic 5, otherwise 0\n");
Print("PASS: identification-impact checks; original presentation preserved\n");
QUIT;
