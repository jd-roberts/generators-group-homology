# Reproduce all 36 H1 values in undergrad-research/Capture2.JPG.
# This checks stored presentations, not the table's group identifications.
# In particular, see tests/presentation-sanity.g for the case-5 label defect.
if LoadPackage("kbmag") <> true then Error("KBMAG is required"); fi;
Read("Algorithms.g");; Read("Library-of-groups.g");;
HistoricalRows := [
    ["GL2Z", Free6, R6, [2,0,0,0]],
    ["SL2Z", S, rels, [1,1,0,0]],
    ["SL2F2", Free0, R0, [1,0,0,0]],
    ["SL2F3", Free3, R3, [0,1,0,0]],
    ["SL2F5", Free5, R5, [0,0,1,0]],
    ["SL2Zi", Free8, R8, [1,0,0,0]],
    ["SL2w", Free1, R1, [0,1,0,0]],
    ["SL2Zneg5", Free9, R9, [3,2,1,1]],
    ["PSL2Z", Free7, R7, [1,1,0,0]]
];;
for row in HistoricalRows do
    actual := List([2,3,5,7], p -> FirstHomologyCoefficients(row[2],row[3],p));;
    Print(row[1], " ", actual, "\n");
    if actual <> row[4] then Error("archived H1 mismatch: ", row[1]); fi;
od;
Print("PASS: 36 archived H1 entries (primes 2,3,5,7)\n");
QUIT;
