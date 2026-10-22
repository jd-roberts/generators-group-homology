# Separate the names in the archive from the groups actually presented.
Read("Library-of-groups.g");;
for pair in [[SL_2Z_2,SL(2,2),6],[SL_2Z_3,SL(2,3),24]] do
    if Size(pair[1]) <> pair[3] then Error("unexpected stored finite-group order"); fi;
    iso := IsomorphismGroups(pair[1],pair[2]);;
    if iso = fail or not IsBijective(iso) then Error("finite matrix-group identification failed"); fi;
    Print("VERIFIED: stored presentation is isomorphic to matrix group of order ",pair[3],"\n");
od;
if Size(SL_2Z_5) <> 5 or not IsCyclic(SL_2Z_5) then
    Error("stored case 5 is no longer the documented cyclic group");
fi;
if Size(SL(2,5)) <> 120 or AbelianInvariants(SL(2,5)) <> [] then
    Error("independent matrix-group sanity check failed");
fi;
Print("KNOWN IDENTIFICATION DEFECT: stored SL_2Z_5 is C5, not SL(2,5); original file preserved\n");
Print("PASS: presentation sanity checks (the known label defect remains unresolved)\n");
QUIT;
