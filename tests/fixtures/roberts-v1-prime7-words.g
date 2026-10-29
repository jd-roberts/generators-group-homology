# Source-only fixture: Roberts 2009.04069v1, twelve words, pp.9-10.
# Literal transcription of the uploaded PDF; NOT corrected representatives.
# Six free coordinates are f1,f2,f3,f4,f5,f7 (f6 is absent).
# Does not assert these words are cycles or replay FindBasis.
RobertsV1Prime7Words := function(F)
    local f1,f2,f3,f4,f5,f7;
    f1:=F.1; f2:=F.2; f3:=F.3; f4:=F.4; f5:=F.5; f7:=F.6;
    return [
        f1*f5*f1*f5^-1,
        f2*f3*f2^-1*f3^-1,
        f2*f5*f2*f5^-1,
        f7*f5^-1*f7*f5^-1*f7*f5,
        f3*f7*f1^-2*f7*f1*f7^-2*f5^-1*f3*f1^-1*f5^-1*f7^-1,
        f4*f7*f1^2*f7^-2*f1^2*f7*f5^-1*f1^-2*f4*f1^-1*f5^-1*f7^-1,
        f2*f7*f1*f5^-1*f1^-2*f5*f7^-2*f1^3*f7*f5^-1*f2*f1^-1*f5^-1*f7^-1,
        f1^2*f7^-7*f1^-1*f3^-1*f1^-1*f4^-1*f2^-1*f1^-2*f7^-1*f1^2*f2*f3*f4,
        f7*f1*f7*f1^2*f7*f1*f7*f1^2*f7*f1^3*f7*f1^3*f7*f1*f5^-1*f1^-1*f5^-1,
        f7*f1^2*f7^-1*f1^-1*f4^-1*f1^-1*f5^-1*f7*f1^2*f7^-1*f4^-1*f1^-2*f5^-1*f7*f1^2*f7^-1*f4^-1*f1^-2*f5^-1,
        f1^-1*f7^-1*f1*f7*f1*f7*f1*f7^-1*f4^-1*f5^-1*f3*f1*f7^-1*f1*f7*f1^2*f7^-1*f1^-1*f7*f1^-1*f4^-1*f5^-1*f3*f1^-1*f7^-1*f1*f7*f1^2*f7^-1*f1^-1*f7*f1^-1*f4^-1*f5^-1*f3,
        f7*f1^-2*f7*f1*f7^-1*f1^2*f7*f1^2*f7^-1*f1*f7^-1*f1*f5^-1*f1^-2*f2*f3*f4*f7*f1^-2*f7*f1*f7^-1*f1^2*f7*f1^2*f7^-1*f1*f7^-1*f5^-1*f1^-3*f2*f3*f4*f7*f1^-2*f7*f1*f7^-1*f1^2*f7*f1^2*f7^-1*f1*f7^-1*f5^-1*f1^-3*f2*f3*f4
    ];
end;
