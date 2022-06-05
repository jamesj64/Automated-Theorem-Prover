namespace Frosty

open System
open Parser

module FrostyProver =

    type Inference =
        | PRE
        | AIPC
        | AIPL of int
        | DN of int
        | IMPL of int
        | DM of int
        | SIMP of int
        | BICOND of int
        | CCONTRA of int * int
        | DS of int * int
        | MP of int * int
        | IP of int * int

    type Line = Formula * int * Inference * (int * int)

    let isCloser (line: Line) =
        let _, _, inference, _ = line 
        match inference with
        | CCONTRA _ -> true
        | _ -> false

    let listToFunc (s: List<'a * 'b>) (x: 'a) =
        let myList: List<'b> = List.map snd (List.filter (fun y -> fst y = x) s)
        if myList.Length = 1 then myList.Head else failwith "Not a function or input outside of function's domain"

    let rec atomsFromFormula (formula: Formula) =
        match formula with
        | Atom _ as p -> Set.singleton p
        | Not p -> atomsFromFormula p
        | Implies(p, q) | And(p, q) | Or(p, q) | Iff(p, q) ->
            atomsFromFormula p + atomsFromFormula q

    let printLiteralTruth =
        function
        | Atom str -> str + ": true"
        | Not(Atom str) -> str + ": false"
        | _ -> failwith "not a literal"

    let getTypeOfFormula (formula: Formula) =
        match formula with
        | Implies _ -> "Implies"
        | Or _ -> "Or"
        | And _ -> "And"
        | Iff _ -> "Iff"
        | Not _ -> "Not"
        | Atom _ -> "Atom"

    let decompBinaryForm (formula: Formula) =
        match formula with
        | Implies(p, q) | Or(p, q) | And(p, q) | Iff(p, q) -> p, q
        | _ -> failwith "not a binary formula"

    let nonNegatedForm (formula: Formula) =
        match formula with
        | Not p -> p
        | _ -> failwith "not negated"

    let getInfoFromAIPL (infer: Inference) =
        match infer with
        | AIPL n -> n
        | _ -> failwith "not AIPL"

    let stringifyInference (infer: Inference) =
        match infer with
        | PRE -> "[Pre]"
        | AIPC | AIPL _ -> "[AIP]"
        | DN ln -> $"[DN, {ln}]"
        | IMPL ln -> $"[Impl, {ln}]"
        | DM ln -> $"[DM, {ln}]"
        | SIMP ln -> $"[Simp, {ln}]"
        | BICOND ln -> $"[BICOND, {ln}]"
        | CCONTRA(a, b) -> $"[Conj (contra.), {a};{b}]"
        | DS(a, b) -> $"[DS, {a};{b}]"
        | MP(a, b) -> $"[MP, {a};{b}]"
        | IP(a, b) -> $"[IP, {a}-{b}]"

    let rec printNBarSpace n = if n = 0 then "" else "| " + printNBarSpace (n - 1)

    let rec printProof (proof: Line list) =
        match proof with
        | (formula, ln, infer, lvl) :: tail ->
            printfn "%s" <| @"`" + (string ln) + printNBarSpace (fst lvl + 1) + (uglyPrint formula) + " " + (stringifyInference infer) + @"`"
            printProof tail
        | _ -> ()

    let stringifyProof (proof: Line list) =
        let rec mainStringProof (proof: Line list) =
            match proof with
            | (formula, ln, infer, lvl) :: tail ->
                @"`" + (string ln) + printNBarSpace (fst lvl + 1) + (prettyPrint formula) + " " + (stringifyInference infer) + @"`" + "\n" + mainStringProof tail
            | _ -> ""
        mainStringProof proof
    
    (*let removeUnnecessaryLines (proof: Line list) =
        let rec getUsedLines proof =
            match proof with
            | (_,line: int,inference,_) :: tail ->
                match inference with
                | AIPL n | DN n | IMPL n | DM n | SIMP n | BICOND n -> [n] @ getUsedLines tail
                | CCONTRA(n, m) | DS(n, m) | MP(n, m) | IP(n, m) -> [n; m] @ getUsedLines tail
                | _ -> [line]
            | _ -> []
        let usedLines = getUsedLines proof*)

    //TO DO: Implement a function to get rid of all the lines not used after the proof has been generated (numbers will have to be changed in accordance with removals)
    //After that, try to remove entire unecessary subproofs
    //also maybe add some more inferences
    let prove (premises: Formula list) (conclusion: Formula) =
        let premiseLines = List.mapi (fun i x -> Line(x, i + 1, PRE, (0,0))) premises
        let conclusionLine = Line(Not conclusion, List.length premiseLines + 1, AIPC, (1, 0))
        let rec cp (used: List<Line * List<int * int>>) (proof: Line list) (level: int * int) (assumptionsAtLevel: List<(int * int) * Line>) =
            //gets all lines that can be used
            let unusedUnsorted = List.filter (fun x -> 
                let _,_,_,l = x
                let usedLevels = listToFunc used x
                //list not used at current level
                not (List.contains level usedLevels) &&
                //(-1,-1) lines can't be used
                not (List.contains (-1,-1) usedLevels) &&
                //makes sure it isn't on a dead level
                //e.g. if level is (2,1), you can't use lines from (2,0). if level is (2, 0), you can't use lines from (3, 0)
                //there can't be any line in the proof that is on a newer version of the same level
                //btw, for a level (a, b), a is the level "number", and b is the level "version"
                (fst l <> fst level || snd level <= snd l) && fst l <= fst level && not (List.exists (fun (_, _, _, m) -> fst m = fst l && snd m > snd l) proof)) proof

            //puts literals first, non-branching nodes second, and branching nodes last.
            //also, the number of times a line has been used affects its rank
            //this way we never use branching nodes unless that's our only option
            let unused = 
                List.sortBy
                    (fun x -> (listToFunc used x).Length + ((fun (formula, _, _, _) -> formula) >> function
                        | Atom _ | Not (Atom _) -> 0
                        | Or (p, _) ->
                            //sees whether you can do disjunctive syllogism or whether you'll need an indirect proof first
                            let usableLines = List.filter (fun (f, _, _, l) -> fst l <= fst level && not (List.exists (fun (_, _, _, m) -> fst m = fst l && snd m > snd l) proof) && (Not f = p || Not p = f)) proof
                            if usableLines.IsEmpty then 2 else 1
                        | Implies (p, _) ->
                            //sees whether you can do modus ponens or whether you'll need an indirect proof first
                            let usableLines = List.filter (fun (f, _, _, l) -> fst l <= fst level && not (List.exists (fun (_, _, _, m) -> fst m = fst l && snd m > snd l) proof) && f = p) proof
                            if usableLines.IsEmpty then 2 else 1
                        | _ -> 1) x) unusedUnsorted
                        
            match unused with
            | (formula, pln, _, _) as line :: _ ->
                let ln = List.length proof + 1
                match formula with
                //non-literal "non-branching" formula types
                | Not(Not p) ->
                    let newLines = [Line(p, ln, DN pln, level)]
                    let newOriginal = List.filter (fun (frm, _, _, l) -> not (List.exists (fun (frm1, _, _, l1) -> frm = frm1 && (l = l1 || fst l1 < fst l)) proof)) newLines
                    let newUsed = (List.filter (fun (x, _) -> x <> line) used) @ [line, (((listToFunc used) line) @ [level])] @ List.map (fun x -> x, []) newOriginal
                    cp newUsed (proof @ newOriginal) level assumptionsAtLevel
                | And(p, q) ->
                    let newLines = if p <> q then [Line(p, ln, SIMP pln, level); Line(q, ln + 1, SIMP pln, level)] else [Line(p, ln, SIMP pln, level)]
                    let newOriginal = List.filter (fun (frm, _, _, l) -> not (List.exists (fun (frm1, _, _, l1) -> frm = frm1 && (l = l1 || fst l1 < fst l)) proof)) newLines
                    let newOriginal = if newOriginal = [Line(q, ln + 1, SIMP pln, level)] then [Line(q, ln, SIMP pln, level)] else newOriginal
                    let newUsed = (List.filter (fun (x, _) -> x <> line) used) @ [line, (((listToFunc used) line) @ [level])] @ List.map (fun x -> x, []) newOriginal
                    cp newUsed (proof @ newOriginal) level assumptionsAtLevel
                | Not(Or(p, q)) ->
                    let newLines = [Line(And(Not p, Not q), ln, DM pln, level)]
                    let newOriginal = List.filter (fun (frm, _, _, l) -> not (List.exists (fun (frm1, _, _, l1) -> frm = frm1 && (l = l1 || fst l1 < fst l)) proof)) newLines
                    let newUsed = (List.filter (fun (x, _) -> x <> line) used) @ [line, (((listToFunc used) line) @ [level])] @ List.map (fun x -> x, []) newOriginal
                    cp newUsed (proof @ newOriginal) level assumptionsAtLevel
                | Not(Implies(p, q)) ->
                    let newLines = [Line(Not(Or(Not p, q)), ln, IMPL pln, level)]
                    let newOriginal = List.filter (fun (frm, _, _, l) -> not (List.exists (fun (frm1, _, _, l1) -> frm = frm1 && (l = l1 || fst l1 < fst l)) proof)) newLines
                    let newUsed = (List.filter (fun (x, _) -> x <> line) used) @ [line, (((listToFunc used) line) @ [level])] @ List.map (fun x -> x, []) newOriginal
                    cp newUsed (proof @ newOriginal) level assumptionsAtLevel
                | Not(And(p, q)) ->
                    let newLines = [Line(Or(Not p, Not q), ln, DM pln, level)]
                    let newOriginal = List.filter (fun (frm, _, _, l) -> not (List.exists (fun (frm1, _, _, l1) -> frm = frm1 && (l = l1 || fst l1 < fst l)) proof)) newLines
                    let newUsed = (List.filter (fun (x, _) -> x <> line) used) @ [line, (((listToFunc used) line) @ [level])] @ List.map (fun x -> x, []) newOriginal
                    cp newUsed (proof @ newOriginal) level assumptionsAtLevel
                | Iff(p, q) ->
                    let newLines = [Line(And(Implies(p, q), Implies(q, p)), ln, BICOND pln, level)]
                    let newOriginal = List.filter (fun (frm, _, _, l) -> not (List.exists (fun (frm1, _, _, l1) -> frm = frm1 && (l = l1 || fst l1 < fst l)) proof)) newLines
                    let newUsed = (List.filter (fun (x, _) -> x <> line) used) @ [line, (((listToFunc used) line) @ [level])] @ List.map (fun x -> x, []) newOriginal
                    cp newUsed (proof @ newOriginal) level assumptionsAtLevel
                | Not(Iff(p, q)) -> 
                    let newLines = [Line(Not(And(Implies(p, q), Implies(q, p))), ln, BICOND pln, level)]
                    let newOriginal = List.filter (fun (frm, _, _, l) -> not (List.exists (fun (frm1, _, _, l1) -> frm = frm1 && (l = l1 || fst l1 < fst l)) proof)) newLines
                    let newUsed = (List.filter (fun (x, _) -> x <> line) used) @ [line, (((listToFunc used) line) @ [level])] @ List.map (fun x -> x, []) newOriginal
                    cp newUsed (proof @ newOriginal) level assumptionsAtLevel
                //branching formula types
                | Or(p, q) ->
                    //lines usuable for disjunctive syllogism
                    let usableLines = List.filter (fun (f, _, _, l) -> fst l <= fst level && not (List.exists (fun (_, _, _, m) -> fst m = fst l && snd m > snd l) proof) && (Not f = p || Not p = f)) proof
                    if usableLines.IsEmpty then
                        //makes sure that the neither the left nor right disjuncts have been established (on an "active" line), and that 
                        //NOTE: just deleted || Not p = frm1 from first parentheses including "p = frm1 || q = frm1". not sure why it was there
                        let unoriginal = List.exists (fun (frm1, _, _, l1) -> (p = frm1 || q = frm1) && (level = l1 || fst l1 < fst level)) proof
                        if not unoriginal then 
                            //previousLinesLevel is the list of all the versions of the current level # + 1
                            let previousLinesLevel = List.map (fun (_,_,_, l) -> snd l) (List.filter (fun (_,_,_,l) -> fst l = fst level + 1) proof)
                            //if this level hasn't before existed, its version is 0. otherwise, it's one more than the max of ^
                            let newLevel = (fst level + 1, if previousLinesLevel.Length = 0 then 0 else List.max previousLinesLevel + 1)
                            let newLine = Line(p, ln, AIPL pln, newLevel)
                            let newUsed = (List.filter (fun (x, _) -> x <> line) used) @ [line, (((listToFunc used) line) @ [level])] @ [newLine, []]
                            cp newUsed (proof @ [newLine]) newLevel (assumptionsAtLevel @ [(newLevel, newLine)])
                        else
                            //just makes this line unusable at this level and move on
                            let newUsed = (List.filter (fun (x, _) -> x <> line) used) @ [line, (((listToFunc used) line) @ [level])]
                            cp newUsed proof level assumptionsAtLevel
                    else
                        //just adds lines for disjunctive syllogism and stuff
                        let newLines = [Line(q, ln, DS(pln, (fun (_,x,_,_) -> x) usableLines.[0]), level)]
                        let newOriginal = List.filter (fun (frm, _, _, l) -> not (List.exists (fun (frm1, _, _, l1) -> frm = frm1 && (l = l1 || fst l1 < fst l)) proof)) newLines
                        let newUsed = (List.filter (fun (x, _) -> x <> line) used) @ [line, (((listToFunc used) line) @ [level])] @ List.map (fun x -> x, []) newOriginal
                        cp newUsed (proof @ newOriginal) level assumptionsAtLevel
                | Implies(p, q) ->
                    //lines usable for modus ponens
                    let usableLines = List.filter (fun (f, _, _, l) -> fst l <= fst level && not (List.exists (fun (_, _, _, m) -> fst m = fst l && snd m > snd l) proof) && f = p) proof
                    if usableLines.IsEmpty then
                        //makes sure that the neither the negation of the antecedent nor the consequent have been established (on an "active" line)
                        let unoriginal = List.exists (fun (frm1, _, _, l1) -> (Not p = frm1 || q = frm1) && (level = l1 || fst l1 < fst level)) proof
                        if not unoriginal then 
                            //previousLinesLevel is the list of all the versions of the current level # + 1
                            let previousLinesLevel = List.map (fun (_,_,_, l) -> snd l) (List.filter (fun (_,_,_,l) -> fst l = fst level + 1) proof)
                            //if this level hasn't before existed, its version is 0. otherwise, it's one more than the max of ^
                            let newLevel = (fst level + 1, if previousLinesLevel.Length = 0 then 0 else List.max previousLinesLevel + 1)
                            let newLine = Line(Not p, ln, AIPL pln, newLevel)
                            let newUsed = (List.filter (fun (x, _) -> x <> line) used) @ [line, (((listToFunc used) line) @ [level])] @ [newLine, []]
                            cp newUsed (proof @ [newLine]) newLevel (assumptionsAtLevel @ [(newLevel, newLine)])
                        else
                            //just makes this line unusable at this level and move on
                            let newUsed = (List.filter (fun (x, _) -> x <> line) used) @ [line, (((listToFunc used) line) @ [level])]
                            cp newUsed proof level assumptionsAtLevel
                    else
                        //just adds lines for modus ponens and stuff
                        let newLines = [Line(q, ln, MP(pln, (fun (_,x,_,_) -> x) usableLines.[0]), level)]
                        let newOriginal = List.filter (fun (frm, _, _, l) -> not (List.exists (fun (frm1, _, _, l1) -> frm = frm1 && (l = l1 || fst l1 < fst l)) proof)) newLines
                        let newUsed = (List.filter (fun (x, _) -> x <> line) used) @ [line, (((listToFunc used) line) @ [level])] @ List.map (fun x -> x, []) newOriginal
                        cp newUsed (proof @ newOriginal) level assumptionsAtLevel
                //check literals for contradictions - they're otherwise useless
                | Atom str | Not (Atom str) as p ->
                    //list of contradictory literals with p
                    let contraList = List.filter (fun (f, _, _, l) -> fst l <= fst level && not (List.exists (fun (_, _, _, m) -> fst m = fst l && snd m > snd l) proof) && (if p = Atom str then Not p = f else p = Not f)) proof
                    if contraList.Length > 0 && fst level > 0 then
                        //otherconj is a contradictory literal and otherLine is its line number
                        let otherConj, otherLine, _, _ = contraList.[0]
                        //assumption is the formula assumed for indirect proof
                        //al is its line number
                        //infer is its inference rule
                        let (assumption, al, infer, _) = listToFunc assumptionsAtLevel level
                        //prevLinesLevel is list of all the versions of times the level (level - 1) has existed
                        let previousLinesLevel = List.map (fun (_,_,_, l) -> snd l) (List.filter (fun (_,_,_,l) -> fst l = fst level - 1) proof)
                        //say level is (a, b) then newLevel is (a - 1, max prevLinesLevel)
                        let newLevel = (fst level - 1, if previousLinesLevel.Length = 0 then 0 else List.max previousLinesLevel)
                        //gets rid of the assumption for the current level
                        let newAssumptionsAtLevel = List.filter (fun (x, _) -> x <> level) assumptionsAtLevel
                        if infer = AIPC then
                            let newLines =  [Line(And(otherConj, p), ln, CCONTRA(otherLine, pln), level); Line(Not(assumption), ln + 1, IP(al, ln), newLevel); Line(nonNegatedForm assumption, ln + 2, DN(ln + 1), newLevel)]
                            cp (List.map (fun x -> x, [(0,0)]) (proof @ newLines)) (proof @ newLines) newLevel newAssumptionsAtLevel
                        else
                            let inspireAIPLine = proof.[getInfoFromAIPL infer - 1]
                            let inspireForm, inspireLine, _, _ = inspireAIPLine
                            if getTypeOfFormula inspireForm = "Implies" then 
                                let newLines =  [Line(And(otherConj, p), ln, CCONTRA(otherLine, pln), level); Line(Not(assumption), ln + 1, IP(al, ln), newLevel); Line(nonNegatedForm assumption, ln + 2, DN(ln + 1), newLevel); Line(snd(decompBinaryForm inspireForm), ln + 3, MP(inspireLine, ln + 2), newLevel)]
                                let newUsed = (List.filter (fun (x, _) -> x <> line) used) @ [line, (((listToFunc used) line) @ [level])] @ List.map (fun x -> x, []) newLines
                                cp newUsed (proof @ newLines) newLevel newAssumptionsAtLevel
                            else
                                let newLines =  [Line(And(otherConj, p), ln, CCONTRA(otherLine, pln), level); Line(Not(assumption), ln + 1, IP(al, ln), newLevel); Line(snd(decompBinaryForm inspireForm), ln + 2, DS(inspireLine, ln + 1), newLevel)]
                                let newUsed = (List.filter (fun (x, _) -> x <> line) used) @ [line, (((listToFunc used) line) @ [level])] @ List.map (fun x -> x, []) newLines
                                cp newUsed (proof @ newLines) newLevel newAssumptionsAtLevel
                    else
                        let newUsed = (List.filter (fun (x, _) -> x <> line) used) @ [line, (((listToFunc used) line) @ [level])]
                        cp newUsed proof level assumptionsAtLevel
            | [] -> proof
        let initialList = premiseLines @ [conclusionLine]
        //third parameter is (1, 0) cuz we always have an indirect proof after the premises.
        //second member indicates first level hasn't existed before
        //fourth parameter is association of negated conclusion w/ level 1
        let proof = cp (List.map (fun x -> x, []) initialList) initialList (1, 0) [(1, 0), conclusionLine]
        let lastLine = proof.[proof.Length - 1]
        let f,_,_,l = lastLine
        if f = conclusion && l = (0, 0) then
            //removeUnnecessaryLines proof |> ignore
            stringifyProof proof
        else
            let atoms = List.fold (fun x y -> x + atomsFromFormula y) Set.empty (premises @ [conclusion])
            let closers = List.map (fun (_,_,_,l) -> l) (List.filter isCloser proof)
            let provedLiterals =
                Set.ofList
                <| List.map fst
                    (List.filter (function
                        | Atom _, l | Not (Atom _), l -> not (List.contains l closers)
                        | _ -> false) 
                        (List.map (fun (f,_,_,l) -> f, l) proof))
            let irrelevantAtoms = atoms - Set.map (function
                | Atom _ as p -> p
                | Not(Atom str) -> Atom str
                | _ -> failwith "never called") provedLiterals
            let counterModel = provedLiterals + (Set.map Not irrelevantAtoms)
            Set.fold (fun x y -> x + "\n`" + printLiteralTruth y + "`") "`Countermodel:`" counterModel