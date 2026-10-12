# lof

`lof` is a small dependent type theory core in Rust. It checks terms with
predicative universes, dependent function types (`Pi`), dependent pair types
(`Sigma`), coproducts, and natural numbers. Functions and dependent eliminators
have computation rules. Type equality is equality of normal forms.

The public API is in [`src/core.rs`](src/core.rs). `Term::var(0)` refers to the
nearest binder; an index increases by one each time a new binder is crossed.
An annotation makes a lambda or pair usable where a type must be inferred.

## Surface syntax

[`src/parse.rs`](src/parse.rs) parses named terms. For example:

```rust
use lof::parse::{parse, parse_core};

let source = "Pi(A: U0). (Sig(x:A). P(x)) -> A*A";
let named = parse(source).unwrap(); // P is allowed to remain free here.
let core = parse_core(source, &["P"]).unwrap(); // Resolve P as an external name.
assert_eq!(core, named.lower(&["P"]).unwrap());
```

Names passed to `parse_core` or `Expr::lower` are ordered oldest to newest, just
like assumptions added to `Context`. Parsing alone does not type check the
expression. `P(x)` is a function application. Since `P` is free here, the exact
expression is only a parsed term. With an explicit polymorphic predicate
`P : Pi(T: U0). T -> U0`, write `P(A,x)` to make its type checkable.

`Pi(x: T). U` and `Sig(x: T). U` bind `x` in `U`. `T -> U` and `T*U` are
anonymous `Pi` and `Sig` types. `T + U` is a coproduct. `*` binds tighter than
`+`, which binds tighter than `->`; all three group to the right. Parentheses
group expressions; `f(x, y)` means `f(x)(y)`. Terms can also use `Lam(x). body`,
pairs `(a,b)`, `inl(a)`, `inr(b)`, and annotations `term : type`. Unicode `Π`,
`Σ`, and `×` are accepted too.

Natural numbers use `Nat`, `Zero`, and `Succ(n)`. Decimal literals from `0` to
`255` are expanded using `Term::from_u8`; larger values can be built with `Succ`.
The dependent eliminators have explicit arguments:

```text
ind_sigma(S, P, branch)
ind_coproduct(C, P, left_case, right_case)
ind_nat(P, zero_case, successor_case)
```

They produce functions, so apply them to the term to eliminate. For example,
`ind_sigma(Nat*Nat, Lam(p). Nat, Lam(a). Lam(b). a)((2,3))` computes to `2`.
Pair projections are defined using `ind_sigma`; `fst` and `snd` are ordinary
names that must be supplied or bound, rather than primitive core operations.

Addition from HoTT Book §1.9 can be written as:

```text
ind_nat(Lam(n). Nat -> Nat, Lam(m). m,
        Lam(n). Lam(g). Lam(m). Succ(g(m)))(2,3)
```

This expression checks against `Nat` and computes to `5`.

This example checks a function of type `Π(A : U₀). Π(b : A). Σ(x : A). A` that
duplicates its argument:

```rust
use lof::core::{check, infer, Context, Term};

let ty = Term::pi(
    Term::u(0),
    Term::pi(
        Term::var(0),
        Term::sigma(Term::var(1), Term::var(2)),
    ),
);
let duplicate = Term::lam(Term::lam(Term::pair(Term::var(0), Term::var(0))));
let context = Context::new();

check(&context, &duplicate, &ty).unwrap();
assert_eq!(infer(&context, &ty).unwrap(), Term::u(1));
```

`Context::assume` adds a checked type as the newest assumption. The core can
infer types for universes, variables, type formers, applications, eliminators,
natural-number constructors, and annotated terms. Lambdas, pairs, and coproduct
injections require an expected type, supplied via `check` or `Term::ann`.

The rules are deliberately small: `U(i) : U(i + 1)` with no universe
cumulativity; `Pi` and `Sigma` live in the maximum of their domain and body
universe levels. Conversion has beta reduction and erases annotations, but does
not include eta conversion. The parser resolves names to core terms; it does
not infer missing arguments or elaborate implicit syntax.

Run `cargo test` to exercise parsing, dependent application, eliminator-based
projections, arithmetic, universe levels, conversion, and de Bruijn substitution.
