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

    let listToFunc (s: List<'a * 'b>) (x: 'a) =
        let myList: List<'b> = List.map snd (List.filter (fun y -> fst y = x) s)
        if myList.Length = 1 then myList.Head else failwith "Not a function or input outside of function's domain"

    let getInfoFromLine (line: Line) =
        match line with
        | (p, q, r, s) -> p, q, r, s

    let getTypeOfFormula (formula: Formula) =
        match formula with
        | Implies(_, _) -> "Implies"
        | Or(_, _) -> "Or"
        | And(_, _) -> "And"
        | Iff(_, _) -> "Iff"
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


    let stringInference (infer: Inference) =
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
            //printfn "%s" <| (string ln) + ". " + (uglyPrint formula) + " " + (stringInference infer) + " level: " + (string (fst lvl)) + ", " + (string (snd lvl))
            printfn "%s" <| @"`" + (string ln) + printNBarSpace (fst lvl + 1) + (uglyPrint formula) + " " + (stringInference infer) + @"`"
            printProof tail
        | _ -> ()

    let rec stringifyProof (proof: Line list) =
        if proof = [] then "Invalid" else
        let rec mainStringProof (proof: Line list) =
            match proof with
            | (formula, ln, infer, lvl) :: tail ->
                @"`" + (string ln) + printNBarSpace (fst lvl + 1) + (prettyPrint formula) + " " + (stringInference infer) + @"`" + "\n" + mainStringProof tail
            | _ -> ""
        mainStringProof proof

    let sortNodes (branch: List<Line>) = 
        List.sortBy
            ((fun (x,_,_,_) -> x) >> function
                | Atom _ | Not (Atom _) -> 0
                | Or _ | Implies _ -> 2
                | _ -> 1) branch

    let newSort (branch: List<Line>) (used: List<Line * List<int * int>>) =
        List.sortBy
            (fun x -> (listToFunc used x).Length + ((fun (formula, _, _, _) -> formula) >> function
                | Atom _ | Not (Atom _) -> 0
                | Or _ | Implies _ -> 2
                | _ -> 1)x) branch
            
    //MAKE IT SO IT DOESN'T PROVE SMTH ALREADY PROVED ON THE SAME LEVEL
    //want line to be "used" only once per line. specifically, can be used exactly once at each level at least as high as its.
    //ideas: 1 add new "parameter" to Line type. list of integers. only issue is that it's immutable. 
    //2: add new parameter to cp of type List<Line * List<int * int>>. basically a function from lines to used levels. could actually get rid of the unused thing and just use proof and this.
    let prove (premises: Formula list) (conclusion: Formula) =
        let premiseLines = List.mapi (fun i x -> Line(x, i + 1, PRE, (0,0))) premises
        let conclusionLine = Line(Not conclusion, List.length premiseLines + 1, AIPC, (1, 0))
        let rec cp (used: List<Line * List<int * int>>) (proof: Line list) (level: int * int) (assumptionsAtLevel: List<(int * int) * Line>) =
            //fix later. will improve proof length
            (*let unused = List.sortBy
                            ((fun (x,_,_,lvl) -> x, lvl) >> function
                                | Atom _,_ | Not (Atom _),_ -> 0
                                | Or (p, _), lvl ->
                                    let usableLines = List.filter (fun (f, _, _, l) -> fst l <= fst lvl && not (List.exists (fun (_, _, _, m) -> fst m = fst l && snd m > snd l) proof) && (Not f = p)) proof
                                    if usableLines.Length = 0 then 2 else 1
                                | Implies(p, q), lvl ->
                                    let usableLines = List.filter (fun (f, _, _, l) -> fst l <= fst lvl && not (List.exists (fun (_, _, _, m) -> fst m = fst l && snd m > snd l) proof) && (f = p)) proof
                                    //printfn "%A" (List.filter (fun (f,_,_,l) -> f = p && fst l <= fst lvl) proof)
                                    printfn "%A" (uglyPrint (Implies(p, q)), lvl)
                                    if usableLines.Length = 0 then 2 else 1
                                | _ -> 1) unuseds*)
            //might want to sort by number of levels it has been used at. not sure yet
            //printfn "%A" used
            //let unused = if not (List.exists (fun x -> not (List.contains level ((listToFunc used) x))) proof) then [] else sortNodes <| List.filter (fun x -> not (List.contains level ((listToFunc used) x))) proof
            let unusedr = newSort (List.filter (fun x -> not (List.contains level ((listToFunc used) x) || List.contains (-1,-1) ((listToFunc used) x))) proof) used
            let unused = List.filter (fun (_, _, _, l) -> fst l <= fst level && not (List.exists (fun (_, _, _, m) -> fst m = fst l && snd m > snd l) unusedr)) unusedr
            let unused = List.filter (fun (_,_,_,m) -> fst m <> fst level || snd level <= snd m) unused
            match unused with
            | (formula, pln, _, lvl) as line :: tail ->
                let ln = List.length proof + 1
                match formula with
                //non-literal "non-branching" formula types
                | Not(Not p) ->
                    let newLines = [Line(p, ln, DN pln, level)]
                    let newUsed = (List.filter (fun (x, _) -> x <> line) used) @ [line, (((listToFunc used) line) @ [level])] @ List.map (fun x -> x, []) newLines
                    let newOriginal = List.filter (fun (frm, _, _, l) -> not (List.exists (fun (frm1, _, _, l1) -> frm = frm1 && (l = l1 || fst l1 < fst l)) proof)) newLines
                    cp newUsed (proof @ newOriginal) level assumptionsAtLevel
                | And(p, q) ->
                    let newLines = if p <> q then [Line(p, ln, SIMP pln, level); Line(q, ln + 1, SIMP pln, level)] else [Line(p, ln, SIMP pln, level)]
                    let newUsed = (List.filter (fun (x, _) -> x <> line) used) @ [line, (((listToFunc used) line) @ [level])] @ List.map (fun x -> x, []) newLines
                    let newOriginal = List.filter (fun (frm, _, _, l) -> not (List.exists (fun (frm1, _, _, l1) -> frm = frm1 && (l = l1 || fst l1 < fst l)) proof)) newLines
                    cp newUsed (proof @ newOriginal) level assumptionsAtLevel
                | Not(Or(p, q)) ->
                    let newLines = [Line(And(Not p, Not q), ln, DM pln, level)]
                    let newUsed = (List.filter (fun (x, _) -> x <> line) used) @ [line, (((listToFunc used) line) @ [level])] @ List.map (fun x -> x, []) newLines
                    let newOriginal = List.filter (fun (frm, _, _, l) -> not (List.exists (fun (frm1, _, _, l1) -> frm = frm1 && (l = l1 || fst l1 < fst l)) proof)) newLines
                    cp newUsed (proof @ newOriginal) level assumptionsAtLevel
                | Not(Implies(p, q)) ->
                    let newLines = [Line(Not(Or(Not p, q)), ln, IMPL pln, level)]
                    let newUsed = (List.filter (fun (x, _) -> x <> line) used) @ [line, (((listToFunc used) line) @ [level])] @ List.map (fun x -> x, []) newLines
                    let newOriginal = List.filter (fun (frm, _, _, l) -> not (List.exists (fun (frm1, _, _, l1) -> frm = frm1 && (l = l1 || fst l1 < fst l)) proof)) newLines
                    cp newUsed (proof @ newOriginal) level assumptionsAtLevel
                | Not(And(p, q)) ->
                    let newLines = [Line(Or(Not p, Not q), ln, DM pln, level)]
                    let newUsed = (List.filter (fun (x, _) -> x <> line) used) @ [line, (((listToFunc used) line) @ [level])] @ List.map (fun x -> x, []) newLines
                    let newOriginal = List.filter (fun (frm, _, _, l) -> not (List.exists (fun (frm1, _, _, l1) -> frm = frm1 && (l = l1 || fst l1 < fst l)) proof)) newLines
                    cp newUsed (proof @ newOriginal) level assumptionsAtLevel
                | Iff(p, q) ->
                    let newLines = [Line(And(Implies(p, q), Implies(q, p)), ln, BICOND pln, level)]
                    let newUsed = (List.filter (fun (x, _) -> x <> line) used) @ [line, (((listToFunc used) line) @ [level])] @ List.map (fun x -> x, []) newLines
                    let newOriginal = List.filter (fun (frm, _, _, l) -> not (List.exists (fun (frm1, _, _, l1) -> frm = frm1 && (l = l1 || fst l1 < fst l)) proof)) newLines
                    cp newUsed (proof @ newOriginal) level assumptionsAtLevel
                | Not(Iff(p, q)) -> 
                    let newLines = [Line(Not(And(Implies(p, q), Implies(q, p))), ln, BICOND pln, level)]
                    let newUsed = (List.filter (fun (x, _) -> x <> line) used) @ [line, (((listToFunc used) line) @ [level])] @ List.map (fun x -> x, []) newLines
                    let newOriginal = List.filter (fun (frm, _, _, l) -> not (List.exists (fun (frm1, _, _, l1) -> frm = frm1 && (l = l1 || fst l1 < fst l)) proof)) newLines
                    cp newUsed (proof @ newOriginal) level assumptionsAtLevel
                //branching formula types
                | Or(p, q) ->
                    let usableLines = List.filter (fun (f, _, _, l) -> fst l <= fst level && not (List.exists (fun (_, _, _, m) -> fst m = fst l && snd m > snd l) proof) && (Not f = p || Not p = f)) proof
                    //printfn "%A" line
                    //printfn "%A" usableLines
                    if usableLines.IsEmpty then
                        let unoriginal = List.exists (fun (frm1, _, _, l1) -> (p = frm1 || q = frm1 || Not p = frm1) && (level = l1 || fst l1 < fst level)) proof
                        if not unoriginal then 
                            let previousLinesLevel = List.map (fun (_,_,_, l) -> snd l) (List.filter (fun (_,_,_,l) -> fst l = fst level + 1) proof)
                            let newLevel = (fst level + 1, if previousLinesLevel.Length = 0 then 0 else List.max previousLinesLevel + 1)
                            let newLine = Line(p, ln, AIPL pln, newLevel)
                            let newUsed = (List.filter (fun (x, _) -> x <> line) used) @ [line, (((listToFunc used) line) @ [level])] @ [newLine, []]
                            cp newUsed (proof @ [newLine]) newLevel (assumptionsAtLevel @ [(newLevel, newLine)])
                        else
                            let newUsed = (List.filter (fun (x, _) -> x <> line) used) @ [line, (((listToFunc used) line) @ [level])] @ List.map (fun x -> x, []) []
                            cp newUsed proof level assumptionsAtLevel
                    else
                        let newLines = [Line(q, ln, DS(pln, (fun (_,x,_,_) -> x) usableLines.[0]), level)]
                        let newOriginal = List.filter (fun (frm, _, _, l) -> not (List.exists (fun (frm1, _, _, l1) -> frm = frm1 && (l = l1 || fst l1 < fst l)) proof)) newLines
                        let newUsed = (List.filter (fun (x, _) -> x <> line) used) @ [line, (((listToFunc used) line) @ [level])] @ List.map (fun x -> x, []) newOriginal
                        cp newUsed (proof @ newOriginal) level assumptionsAtLevel
                | Implies(p, q) ->
                    let usableLines = List.filter (fun (f, _, _, l) -> fst l <= fst level && not (List.exists (fun (_, _, _, m) -> fst m = fst l && snd m > snd l) proof) && f = p) proof
                    if usableLines.IsEmpty then
                        let unoriginal = List.exists (fun (frm1, _, _, l1) -> (Not p = frm1 || q = frm1) && (level = l1 || fst l1 < fst level)) proof
                        if not unoriginal then 
                            let previousLinesLevel = List.map (fun (_,_,_, l) -> snd l) (List.filter (fun (_,_,_,l) -> fst l = fst level + 1) proof)
                            let newLevel = (fst level + 1, if previousLinesLevel.Length = 0 then 0 else List.max previousLinesLevel + 1)
                            let newLine = Line(Not p, ln, AIPL pln, newLevel)
                            let newUsed = (List.filter (fun (x, _) -> x <> line) used) @ [line, (((listToFunc used) line) @ [level])] @ [newLine, []]
                            cp newUsed (proof @ [newLine]) newLevel (assumptionsAtLevel @ [(newLevel, newLine)])
                        else
                            let newUsed = (List.filter (fun (x, _) -> x <> line) used) @ [line, (((listToFunc used) line) @ [level])] @ List.map (fun x -> x, []) []
                            cp newUsed proof level assumptionsAtLevel
                    else
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
                        let otherConj, otherLine, _, _ = getInfoFromLine (contraList.[0])
                        //assumption is the formula assumed for indirect proof
                        //al is its line number
                        //infer is its inference rule
                        let (assumption, al, infer, _) = listToFunc assumptionsAtLevel level
                        //printProof proof
                        //prevLinesLevel is list of all the numbers of times the level (level - 1) has existed
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
                            let inspireForm, inspireLine, _, _ = getInfoFromLine inspireAIPLine
                            if getTypeOfFormula inspireForm = "Implies" then 
                                let newLines =  [Line(And(otherConj, p), ln, CCONTRA(otherLine, pln), level); Line(Not(assumption), ln + 1, IP(al, ln), newLevel); Line(nonNegatedForm assumption, ln + 2, DN(ln + 1), newLevel); Line(snd(decompBinaryForm inspireForm), ln + 3, MP(inspireLine, ln + 2), newLevel)]
                                //cp used proof level assumptionsAtLevel
                                //let newUsedLines = [Line(And(otherConj, p), ln, CCONTRA(otherLine, ln - 1), level)]
                                let newUsed = (List.filter (fun (x, _) -> x <> line) used) @ [line, (((listToFunc used) line) @ [level])] @ List.map (fun x -> x, []) newLines
                                cp newUsed (proof @ newLines) newLevel newAssumptionsAtLevel
                            else
                                // printfn "%A" contraList
                                // printfn "%A" line
                                // // printfn "%A" pln
                                // printfn "%A" lvl
                                // printfn "%A" level
                                // printfn "%A" unused
                                // printfn "%A" <| List.filter (fun (_,_,_,m) -> fst m <> fst level || snd level <= snd m) unused
                                let newLines =  [Line(And(otherConj, p), ln, CCONTRA(otherLine, pln), level); Line(Not(assumption), ln + 1, IP(al, ln), newLevel); Line(snd(decompBinaryForm inspireForm), ln + 2, DS(inspireLine, ln + 1), newLevel);]
                                //cp used proof level assumptionsAtLevel
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
        let isValid = (fun (f,_,_,l) -> f = conclusion && l = (0,0)) (List.last proof)
        let result: List<Line> = if isValid then proof else []
        result