## Frosty - A functionally-programmed theorem prover with logic-related functionality

(Run ./frosty in the release directory, or publish the app yourself with dotnet publish) 

## Commands

### `prove`

Writes a natural deduction proof of the inputted formula/argument

### `format`

Formats the supplied formula or list of formulas, each separated by a line.

### `polish`

Converts the supplied formula or list of formulas, each separated by a line, to Polish notation.

### `help`

Lists all commands. Specify a command to see more information about the given command.


## Some examples
An example of a proof of `P ⇒ P`:

`1| | ¬(P ⇒ P) [AIP]`<br/>
`2| | ¬(¬P ∨ P) [Impl, 1]`<br/>
`3| | ¬¬P ∧ ¬P [DM, 2]`<br/>
`4| | ¬¬P [Simp, 3]`<br/>
`5| | ¬P [Simp, 3]`<br/>
`6| | P [DN, 4]`<br/>
`7| | ¬P ∧ P [Conj (contra.), 5;6]`<br/>
`8| ¬¬(P ⇒ P) [IP, 1-7]`<br/>
`9| P ⇒ P [DN, 8]`<br/><br/>

Two examples of proper usage:

`./frosty prove 'P -> Q'`

`./frosty prove 'P ∨ Q' 'P ⇒ Q' 'Q'`

In the first example, it will attempt to write a proof of `P ⇒ Q` or `⊢ P ⇒ Q`. However, since `P ⇒ Q` is invalid, it will instead provide a countermodel.
Frosty always chooses the final formula to be the goal/conclusion of a proof. So, in the second example, it will try to prove the following inference `P ∨ Q, P ⇒ Q ⊢ Q`. Since it is valid, it will send a natural deduction proof of the supplied inference.

An example of a formatted version of `P -> Q || R <-> Q && T`:

`(P ⇒ (Q ∨ R)) ⇔ (Q ∧ T)`

## Information about Syntax

#### The allowed symbols are as follows:

Negation: `¬`, `~`, `!`, `-`<br/>
Conjunction: `∧`, `&`, `&&`<br/>
Disjunction: `∨`, `|`, `||`<br/>
Material Conditional: `⇒`, `→`, `⊃`, `->`, `-->`<br/>
Material Biconditional: `⇔`, `⟷`, `≡`, `<->`, `<-->`<br/>
Parentheses, brackets, spaces, and letters are also allowed.

#### Additional Information about Syntax

1. Formulas should be written in infix notation.
2. The truth-functional operators obey the standard precedence rules. The above operators are listed according to their relative precedence (descending).
3. Each of the above binary operators is right-associative. For example, `P ⇒ Q ⇒ P` will be treated as `P ⇒ (Q ⇒ P)`.
4. You should place each formula in quotes so they are parsed correctly.
