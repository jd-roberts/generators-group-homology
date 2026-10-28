# Run from repository root under a five-second external timeout.
# All checks are free-word/linear checks, NOT a relation-module spanning test.
Read("scripts/prime7-correction.g");;
Read("docs/evidence/prime7-corrected-words.g");;

Prime7VerifyCorrections := function()
    local c, expectedD, expectedC, expectedExponents, zero, originalExponents,
          i, output, asIntegers, explicitWord;
    c := Prime7CorrectionCalculation();
    asIntegers := m->List(m,row->List(row,Int));
    explicitWord := function(word)
        local ext, pieces, k, names, piece;
        ext:=ExtRepOfObj(word); pieces:=[];
        names:=["z","u1","u2","u3","a","b1"];
        for k in [1,3..Length(ext)-1] do
            piece:=names[ext[k]];
            if ext[k+1]<>1 then
                piece:=Concatenation(piece,"^",String(ext[k+1]));
            fi;
            Add(pieces,piece);
        od;
        return JoinStringsWithSeparator(pieces,"*");
    end;
    expectedD := [[1,2,0,0,5,6],[0,0,0,0,0,6],[5,0,0,0,5,0],
        [0,0,0,4,4,0],[4,0,3,4,4,0],[5,3,3,3,4,0]];
    expectedC := [[3,4,3,3,2,5],[0,0,0,0,0,0],[0,0,5,6,4,3],
        [5,6,2,5,1,6],[3,5,4,0,5,5],[4,4,6,1,5,2]];
    expectedExponents := [[-35,0,0,21,21,-42],[0,0,0,0,0,0],
        [21,-7,0,-21,-7,14],[-21,7,0,0,-7,-21],
        [49,0,14,0,-14,7],[14,0,0,-7,-7,-21]];
    zero := List([1..6],i->List([1..6],j->Zero(GF(7))));
    if asIntegers(c.auxiliary) <> expectedD or
       Int(DeterminantMat(c.auxiliary)) <> 6 or
       c.auxiliary*c.inverse <> IdentityMat(6,GF(7)) or
       c.inverse*c.auxiliary <> IdentityMat(6,GF(7)) or
       asIntegers(c.coefficients) <> expectedC or
       c.coefficients*c.auxiliary <> c.first or
       c.exponentSums <> expectedExponents or
       c.exponentSums*One(GF(7)) <> zero then
        Error("prime-7 matrix/word correction check failed");
    fi;
    if c.printed <> c.words{[1..6]} then
        Error("named transcription differs from literal first-six words");
    fi;
    if List([1..6],i->c.corrected[i]=c.printed[i]) <>
       [false,true,false,false,false,false] then
        Error("unexpected free-word comparison with the printed list");
    fi;
    originalExponents := List(c.originalWords,w->List(
        GeneratorsOfGroup(c.originalF),g->ExponentSumWord(w,g)));
    if Prime7CorrectedWordsOriginalFreeGroup(c.originalF) <> c.originalWords then
        Error("expanded original-generator artifact differs from constructed words");
    fi;
    if originalExponents*One(GF(7)) <>
       List([1..6],i->List([1..14],j->Zero(GF(7)))) then
        Error("original 14-generator exponent check failed");
    fi;

    output := OutputTextUser();
    SetPrintFormattingStatus(output,false);
    PrintTo(output,"BEGIN_PRIME7_CORRECTION_JSON\n");
    PrintTo(output,"{\"gap_version\":\"",GAPInfo.Version,
        "\",\"auxiliary_matrix\":",asIntegers(c.auxiliary),
        ",\"inverse\":",asIntegers(c.inverse),
        ",\"coefficients\":",asIntegers(c.coefficients),
        ",\"signed_coefficients\":",c.signed,
        ",\"integer_exponent_sums\":",c.exponentSums,
        ",\"original_14_integer_exponent_sums\":",originalExponents,
        ",\"free_word_lengths\":",List(c.corrected,Length),
        ",\"expanded_words\":[");
    for i in [1..6] do
        if i>1 then PrintTo(output,","); fi;
        PrintTo(output,"\"",explicitWord(c.corrected[i]),"\"");
    od;
    PrintTo(output,"]}\nEND_PRIME7_CORRECTION_JSON\n");
    PrintTo(output,"PASS: matrices, corrected free words, named transcription, and all 14 exponent coordinates\n");
    PrintTo(output,"NOT VERIFIED: membership/spanning certificate for the twelve literal words in the intended relation module\n");
end;
Prime7VerifyCorrections();
QUIT;
