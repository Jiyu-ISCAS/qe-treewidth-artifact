#!/usr/bin/env wolframscript

(* --- CONFIGURATION --- *)
csvFile = "./tests/CAD_results/Ex9.csv";
TimeLimit = 7200;

(* 1. Define the input expression *)
expr = Rationalize[(0.0 <= ((4.0*x2) + (10.0*x3) + ((7.0*x2)*x2) + ((-8.0*x3)*
       x3) + ((2.0*x2)*x3) + ((7.0*x3)*x1))) && (0.0 <= ((-3.0*
       x2) + ((7.0*x5)*x5) + ((-5.0*x2)*x3) + ((-1.0*x3)*
       x5))) && (0.0 <= ((-10.0*x4) + (6.0*x5) + ((7.0*x2)*
       x2) + ((3.0*x4)*x4) + ((4.0*x5)*x5))) && (0.0 <= ((4.0*
       x6) + ((2.0*x1)*x1) + ((-1.0*x6)*x1))) && (0.0 <= ((-10.0*
       x4) + ((9.0*x7)*x4)))];

(* 2. Initialize CSV File with Headers *)
(* This creates a new file (or overwrites existing) with the header row *)
Export[csvFile, {{"Method", "Time (s)", "Cell Count"}}, "CSV"];
Print["Output will be saved to: ", ExpandFileName[csvFile]];
Print["--------------------------------------------------\n"];

(* 3. Define the Robust Helper to Extract Cell Count *)
GetCellCount[res_] := Module[{data, stats},
  If[Head[Head[res]] =!= CylindricalDecompositionFunction, Return["Not CAD Func"]];
  
  (* Extract internal data block *)
  data = res[[0, 1]];

  (* Try direct extraction from the standard position (-2) *)
  If[ListQ[data] && Length[data] >= 2,
     stats = data[[-2]];
     If[MatchQ[stats, {_Integer, _Integer, _Integer}],
        Return[stats[[3]]]
     ]
  ];

  (* Fallback: Scan top level only *)
  FirstCase[data, {_, _, c_Integer} :> c, "Extraction Failed", {1}]
];

RunAndReport[label_, variables_] := Module[{time, result, cellCount, csvRow, stream},
  Print["Running: ", label, " ..."];
  
  (* Run Timing *)
  {time, result} = Timing[
    TimeConstrained[
      CylindricalDecomposition[expr, variables, "Function"], 
      TimeLimit
    ]
  ];

  (* Extract Count *)
  cellCount = GetCellCount[result];

  (* --- CSV EXPORT LOGIC --- *)
  csvRow = {label, time, cellCount};
  
  (* Open file in Append mode, write the row formatted as CSV, and Close *)
  stream = OpenAppend[csvFile];
  WriteString[stream, ExportString[{csvRow}, "CSV"]];
  Close[stream];

  (* Print to Console *)
  Print["--------------------------------------------------"];
  Print["Method: ", label];
  Print["Time:   ", time, " seconds"];
  Print["Cells:  ", cellCount];
  Print["Saved to CSV."];
  Print["--------------------------------------------------\n"];
];

(* 4. Run the instances *)

(* Case 1: Maple's SuggestVariableOrder *)
RunAndReport["(1) Maple SuggestVariableOrder", {x2, x4, x3, x1, x5, x7, x6}];

(* Case 2: Brown's heuristics *)
RunAndReport["(2) Brown heuristics", {x2, x1, x3, x4, x5, x6, x7}];

(* Case 3: PEO *)
RunAndReport["(3) PEO", {x2, x1, x3, x5, x4, x6, x7}];

(* Case 4: Brown's heuristics + tree decomposition *)
RunAndReport["(4) Brown + Tree Decomp", {x2, x5, x3, x4, x1, x7, x6}];
