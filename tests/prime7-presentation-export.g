# Export source free words and check a generated artifact. No KBMAG or search.
Read("Library-of-groups.g");;
Read("tests/fixtures/roberts-v1-proposition32.g");;
Read("scripts/prime7-correction.g");;
Read("docs/evidence/prime7-b0-corrected-words.g");;
(function()
    local c,phi,psi,rows,out,letters,i,entry,tau,alternative;
    c:=Prime7CorrectionCalculation();
    phi:=GroupHomomorphismByImages(F7,c.F,GeneratorsOfGroup(F7),
        RobertsV1Proposition32Map(c.F));
    psi:=GroupHomomorphismByImages(c.F,F7,GeneratorsOfGroup(c.F),
        GeneratorsOfGroup(F7){[1,2,3,4,5,8]});
    tau:=w->MappedWord(w,GeneratorsOfGroup(c.F),
        [c.F.1,c.F.2,c.F.3,c.F.4,c.F.5,c.F.1^-3*c.F.6*c.F.1^3]);
    alternative:=List(c.corrected,tau);
    if Prime7B0CorrectedWordsOriginalFreeGroup(F7) <>
       List(alternative,w->Image(psi,w)) then
        Error("new expanded artifact differs from the certified b0 variant");
    fi;
    letters:=function(w)
        local e,j,l;
        e:=ExtRepOfObj(w); l:=[];
        for j in [1,3..Length(e)-1] do
            Append(l,List([1..AbsInt(e[j+1])],k->SignInt(e[j+1])*e[j]));
        od;
        return l;
    end;
    rows:=[
        ["forward_generator_images",RobertsV1Proposition32Map(c.F)],
        ["backward_generator_images",GeneratorsOfGroup(F7){[1,2,3,4,5,8]}],
        ["inverse_composites",List(GeneratorsOfGroup(c.F),
            g->g*Image(phi,Image(psi,g))^-1)],
        ["b0_corrected",alternative],
        ["original_relators",k7],
        ["reduced_relators",RobertsV1Proposition32(c.F)],
        ["forward_relators",List(k7,r->Image(phi,r))],
        ["backward_relators",List(RobertsV1Proposition32(c.F),r->Image(psi,r))],
        ["composites",List(GeneratorsOfGroup(F7),g->g*Image(psi,Image(phi,g))^-1)],
        ["twelve",c.words],
        ["corrected",c.corrected],
        ["b0_twelve",List(c.words,tau)]
    ];
    out:=OutputTextUser(); SetPrintFormattingStatus(out,false);
    PrintTo(out,"BEGIN_PRIME7_PRESENTATION_JSON\n{");
    for i in [1..Length(rows)] do
        if i>1 then PrintTo(out,","); fi;
        entry:=rows[i];
        PrintTo(out,"\"",entry[1],"\":",List(entry[2],letters));
    od;
    PrintTo(out,"}\nEND_PRIME7_PRESENTATION_JSON\n");
end)();
QUIT;
