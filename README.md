# lof

A small dependent type theory kernel in Rust, with a named `.lof` language,
file imports, a command-line checker, and a language server.

## Try it

```sh
cargo +nightly test
cargo +nightly run -- check src/defined/arithmetic/tests.lof
cargo +nightly run -- eval src/defined/arithmetic/arithmetic.lof 'add(#2,#3)'
```

The last command prints the inferred type and `5`. Natural-number syntax is
`#0` through `#255`; larger numbers can be built with `Succ(...)`.

## Modules

One file can define and export many terms. For example, `arithmetic.lof`:

```text
let id = λn.n : Nat -> Nat;

export let add = recNat(
    Nat -> Nat, id,
    λn.λrec.λm.Succ(rec(m))
) : Nat -> Nat -> Nat;

export let mul = recNat(
    Nat -> Nat, λm.#0,
    λn.λrec.λm.add(m,rec(m))
) : Nat -> Nat -> Nat;
```

In another `.lof` file:

```text
import "./arithmetic.lof" as Arithmetic;

export let five = Arithmetic::add(#2,#3);
export let add_computes = refl(five) : five=#5;
```

Imports require an explicit alias and a relative file path. Paths resolve from
**the importing file**, independently of the process's current directory.
Imports come before definitions. Every module declaration ends with `;`.
Definitions are private unless introduced with `export let`. Annotations follow
the value: `let name = value : Type;`.

The loader checks all definitions in source order, including private and unused
ones. A definition can use earlier private helpers, as `mul` uses `add` above.
Exports retain constant references; the checked global environment retains
private dependencies needed to type check and unfold those references. Importers
can name only exports. To reexport an imported value, write an exported binding
for it explicitly. Forward references, self references, import cycles, duplicate
module names, and duplicate import aliases are rejected. Local binders can
shadow module names.

There are no packages, manifests, version resolution, or downloads. Canonical
file paths identify modules; repeated and diamond imports share one checked
module per loading session. A `ModuleLoader` owns the module cache and kernel
`Environment`; use a fresh loader after source changes. Failed loads roll back
inserted declarations so a corrected file can be retried. For this initial
implementation rollback clones the environment; incremental checking and
persistent compiled caches can come later. Editor overlays support unsaved files.

See [arithmetic](src/defined/arithmetic/arithmetic.lof) and
[path algebra](src/defined/path_algebra/paths.lof) for working definitions.

## Eval output

`lof eval` prints types and values using LOF notation (`Π`, `Σ`, `λ`, `¬`,
`refl`, and so on), with generated binder names because the kernel discards
source names. Generated names follow `x, y, z, a, b, c, ...`, with numeric suffixes
after the alphabet is exhausted, skipping names that would capture constants.
`A -> 0` prints as `¬A`. Visible constants use their module names;
constants without a visible name retain their full global ID. Natural-number
results still print as decimal numbers. Rust `Debug` formatting remains available
for inspecting the underlying AST; `Display` uses the readable notation.

## Libraries

The `.lof` files include comments explaining the definitions and induction cases.
Import the needed file with an explicit alias, using a path relative to your file.

| File under `src/defined` | Contents |
| --- | --- |
| `arithmetic/arithmetic.lof` | Addition, multiplication, predecessor, truncated subtraction, powers, factorial, zero test; addition unit/successor/associativity/commutativity laws and multiplication zero/unit laws |
| `path_algebra/paths.lof` | `ap`, inverse, concatenation, unit/associativity laws, `transport`, `apd` |
| `helpers/functions.lof` | Identity, constant functions, composition |
| `helpers/sigma.lof` | Dependent projections, constructive Σ-choice, curry/uncurry |
| `helpers/logic.lof` | Negation, `isContractible`, `isProp`, `isSet`, recursive `isNType`, classical assumption types and conditional DNE proof |
| `helpers/option.lof` | `Option`, constructors, recursion, map/bind, default extraction |
| `helpers/bool.lof` | Booleans, conditionals, boolean operations |
| `helpers/equivalence.lof` | Homotopies, `qinv`/`QuasiEquiv`, `isHAE`/`HalfAdjointEquiv`, fibers and `isEquiv`/`Equiv`, identity witnesses for quasi-inverse and half-adjoint structures |

For example, in a file next to `helpers/equivalence.lof`:

```text
import "./equivalence.lof" as Equivalence;
export let identity_equivalence = Equivalence::identity_half_adjoint_equiv(Nat);
```

`isNType(#0,A)` means `isSet(A)`; successor levels recurse on identity types.
The negative levels are named `isProp` and `isContractible`.
`ExcludedMiddle` is the type `Π(A:U0). isProp(A) -> (A + ¬A)`; its inhabitant
is an explicit argument to `dne_from_em`. This proves DNE for propositions under
that assumption. Constructive Σ-choice is separately defined in `sigma.lof`.

## Rust imports and tests

Keep each language library next to its Rust module and tests:

```text
src/defined/arithmetic/
    mod.rs
    arithmetic.lof
    tests.lof
```

Inside that `mod.rs`:

```rust
use crate::{core::{kernel::Context, terms::Term}, import_lof};

const ARITHMETIC_LOF: &str = "./arithmetic.lof";
let arithmetic = import_lof!(ARITHMETIC_LOF; add, mul).unwrap();
let sum = Term::app(Term::app(arithmetic.add.clone(), Term::from(2)), Term::from(3));
arithmetic.environment().check(&Context::new(), &sum, &Term::nat()).unwrap();
assert_eq!(arithmetic.environment().normalize(&sum), Term::from(5));
```

Macro paths resolve relative to the calling Rust source file. Selecting exports
creates named `Term` fields: Rust checks field names and their Rust type. File
loading, export lookup, and LOF type checking happen **when the macro executes**.
The wrapper owns the environment needed to use its constants. Use one
`ModuleLoader` if several imported modules must share an environment.

For a whole proof file, use `import_lof!("./tests.lof")` or
`LoadedModule::load(path)`. Loading succeeds only if all declarations type check;
`refl(...) : expression=expected` can assert a computation in LOF. Rust tests
can additionally inspect normal forms. The arithmetic and path algebra folders
each contain both kinds of tests. Kernel tests live separately under
[`src/core/tests`](src/core/tests) and construct core terms directly.

## Surface syntax

| Meaning | Syntax |
| --- | --- |
| Universe | `U0`, `U1`, ... |
| Dependent function | `Π(x:A). B` |
| Function | `A -> B` or `A → B` |
| Negation | `¬A`, shorthand for `A -> 0` |
| Lambda / application | `λx.body`, `λ(x:A). body`, `f(x,y)` |
| Dependent pair type | `Σ(x:A). B` |
| Product / pair | `A*B` or `A × B`, `(a,b)` |
| Coproduct / injections | `A+B`, `inl(a)`, `inr(b)` |
| Identity / reflexivity | `a=b`, `refl(a)`, `refl_a` |
| Empty type | `0` (also `Empty`) |
| Unit type / value | `1`, `*` (also `Unit`, `tt`) |
| Natural numbers | `Nat`, `#0`, `#42`, `Zero`, `Succ(n)` |
| Annotation | `term : Type` |
| Comment | `// comment` |

`A -> B` and `A*B` lower to anonymous Π and Σ binders; they do not add new
kernel type formers. `*` is a unit value in term position and a product operator
between expressions. For example, `(*,*) : 1*1` is a pair of unit values.
Decimal digits without `#` are reserved for the types `0` and `1`; other bare
numbers are rejected. Universe names and eliminator names such as `ind0` are
unaffected.

`*` binds more tightly than `+`, then `=`, then `->`. Products, coproducts, and
arrows associate to the right. Parenthesize nested identities. Annotations bind
more loosely than binders, so `λx.refl_x : Π(a:A). a=a` annotates the entire
lambda. `f(x,y)` is curried application `f(x)(y)`; arguments are explicit.

Negation binds more tightly than products and includes following applications:
`¬P(x)` means `P(x) -> 0`, while `¬A -> B` means `(A -> 0) -> B`.
Use `¬(A -> B)` to negate a function type; `¬¬A` also works.

### Typed lambda binders

`λ(x:A). body` validates `A`, infers the body under `x:A`, and synthesizes the
dependent function type. This lets polymorphic exports omit their full type:

```text
export let identity = λ(A:U0).λ(x:A).x;

export let inv = λ(A:U0).ind_id(
    A,
    λx.λy.λp.y=x,
    λx.refl(x)
);
```

The annotation is resolved before the binder enters scope: in
`λ(A:U0).λ(A:A).A`, the inner annotation refers to the outer `A`.
Typed and untyped binders can be mixed. Inference still requires an inferable
body; an untyped lambda, pair, or injection in the body can instead be checked
using an expected type or an explicit annotation. Checking a typed lambda
always verifies its written binder type agrees with the expected domain.
Binder annotations are erased during normalization.

### Eliminators

Each eliminator produces a function to apply to a scrutinee. Dependent forms
accept a motive; nondependent forms accept a constant result type `C`.

| Type | Dependent syntax | Constant-result syntax |
| --- | --- | --- |
| Empty | `ind0(P)` | `rec0(C)` |
| Unit | `ind1(P, case)` | `rec1(C, case)` |
| Nat | `ind_nat(P, zero, step)` | `recNat(C, zero, step)` |
| Σ | `ind_Σ(S, P, branch)` | `rec_Σ(S, C, branch)` or `recSigma(...)` |
| Coproduct | `ind_coproduct(S, P, left, right)` | `recCoproduct(S, C, left, right)` |
| Identity | `ind_id(A, P, case)` | `recId(A, C, case)` |

Nondependent syntax generates a constant lambda motive with correct weakening
of surrounding variables. There are no separate primitive recursors. Motives
may return any universe. The checker supplies the known motive binder domains
to infer the result universe, then checks the whole motive against that type.
This permits type-valued recursion, including the `isNType` hierarchy, without
universe annotations on eliminators. General cumulativity is still absent.

Examples:

```text
recNat(Nat,#0,λn.λr.Succ(r))(#3)          // #3
rec_Σ(Nat*Nat,Nat,λa.λb.a)((#2,#3))      // #2
recCoproduct(Nat+Nat,Nat,λa.a,λb.Succ(b))(inr(#2)) // #3
recId(Nat,Nat,λa.Succ(a))(#2,#2,refl(#2)) // #3
rec1(Nat,#7)(*)                         // #7
ind1(λx.x=*,refl(*))(*)                 // refl(*)
λA.rec0(A) : Π(A:U0). 0 -> A           // elimination from Empty
```

Nat's step still takes the predecessor and recursive result: `Nat -> C -> C`.
Identity's reflexivity case takes an endpoint: `A -> C`. Unit's case is a value
of `P(*)`, without an extra argument. Empty has no cases or constructor
computation rule. Eliminators applied to neutral terms remain stuck. There are
no judgmental eta rules, including for Unit.

### Expression scopes

Braces contain sequential local definitions and a final expression:

```text
{
    let id = λx.x : Nat -> Nat;
    id(#2)
}
```

Local `let`s expand hygienically during lowering. Their right-hand sides capture
the preceding scope, and binders or later definitions shadow earlier names.
A local right-hand side cannot refer to itself. Local definitions disappear from
the core, whereas module definitions become named constants. Expression scopes
also accept unambiguous newline separators; use semicolons consistently to avoid
ambiguity with a following application. Module declarations always require them.

`parse(source)` builds a named AST without resolving names. `parse_core(source,
external_names)` resolves local de Bruijn indices; external names must be ordered
oldest to newest, matching the typing context. Neither operation type checks.
The parser is split into [AST](src/parse/ast.rs), [lexer](src/parse/lexer.rs),
[parser](src/parse/parser.rs), [lowering](src/parse/lower.rs), and errors/tests.

## Kernel API

```rust
use lof::core::{kernel::{check, Context}, terms::Term};

let ty = Term::pi(Term::u(0), Term::pi(Term::var(0),
    Term::sigma(Term::var(1), Term::var(2))));
let duplicate = Term::lam(Term::lam(Term::pair(Term::var(0), Term::var(0))));
check(&Context::new(), &duplicate, &ty).unwrap();
```

`Var(0)` is the nearest binder. `Context::assume` validates new assumptions.
Untyped lambdas, pairs, and coproduct injections need an expected type or
annotation to synthesize a type. `Term::typed_lam(domain, body)` infers a Π type
when its body is inferable. Use `Environment` methods or `infer_in` / `check_in` /
`normalize_in` for terms with named constants. The plain functions use an empty
global environment.

Universes are predicative: `Ui : U(i+1)`. Π, Σ, and coproduct formation take the
maximum component universe. General checking is noncumulative. The existing
identity rule separately allows types at different levels to be compared in a
common universe, including `Nat = U0`; this is not general cumulativity.
Conversion unfolds checked definitions and computes beta and eliminator rules,
without eta or univalence. Normalization requires well-typed input and never
calls inference. See the [kernel contracts and normalization audit](docs/kernel-invariants.md)
for every normalization call's justification, expected-type preconditions, and
binder/substitution contracts.

## Language server

```sh
cargo +nightly build --bin lof-lsp
```

The binary speaks LSP over stdio. The local
[VS Code / Code OSS connector](editors/vscode/README.md) provides `.lof` syntax
highlighting, diagnostics, and module/import name completion. In this workspace
it has been linked into Code OSS's extensions directory; run **Developer: Reload
Window**, then open a `.lof` file. Use **LOF: Restart Language Server** after
rebuilding. Set `lof.serverPath` when the binary is outside the open workspace.
Logs are under **Output → LOF Language Server**.

Open imported documents override disk content, and edits revalidate open
importers. Diagnostics currently report the first error in each open module.
Completion covers module declarations and imported exports; local binder
completion, hover, navigation, rename, and embedded Rust strings are not yet
implemented. Checking is synchronous without a resource budget.
