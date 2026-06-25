# Switch-statement examples

A collection of small, self-contained Java methods that exercise the Java
`switch` **statement** together with a JML contract that pins down the
expected return value for every relevant input. They are meant as test
material for the symbolic execution of `switch` (in particular for an improved
`switch` treatment and for correct `String` handling).

Each example is one class with

* a single method that takes the value being switched over as its parameter,
* a simple primitive (here: `int`) return type, and
* a `public normal_behavior` contract that specifies `\result` for the given
  precondition.

For every `<Name>.java` there is a matching `<Name>.key` proof obligation
(a `FunctionalOperationContractPO`). Load the `.key` file in the KeY GUI, or
run it head-less:

```
java -jar key-<version>-exe.jar --auto path/to/<Name>.key
```

## Layout

The examples are grouped by the type of the switch selector so that a parse
or proof issue in one group cannot affect the others (each `.key` loads only
the `.java` files in its own directory).

| Directory  | Selector type        |
|------------|----------------------|
| `int/`     | `int`                |
| `strings/` | `java.lang.String`   |
| `enums/`   | enum (reference type)|

## What each example covers

The set spans the combinations of *default position* × *fall-through*:

| Example                         | Selector | Default position | Fall-through                          |
|---------------------------------|----------|------------------|---------------------------------------|
| `int/DefaultLast`               | int      | last             | no                                    |
| `int/DefaultFirst`              | int      | first            | no                                    |
| `int/DefaultMiddle`             | int      | middle           | no                                    |
| `int/NoDefault`                 | int      | none (precond.)  | no                                    |
| `int/Fallthrough`               | int      | none             | yes (cumulative, no breaks)           |
| `int/FallthroughGroups`         | int      | last             | yes (grouped/empty case labels)       |
| `int/MixedFallthrough`          | int      | middle           | yes (default falls through to a case) |
| `strings/StringDefaultLast`     | String   | last             | no                                    |
| `strings/StringDefaultMiddle`   | String   | middle           | no                                    |
| `strings/StringNoDefault`       | String   | none (precond.)  | no                                    |
| `strings/StringGroups`          | String   | last             | yes (grouped/empty case labels)       |
| `strings/StringFallthrough`     | String   | last             | yes (into a non-empty body, + break)  |
| `enums/TrafficLight`            | enum     | last             | no                                    |
| `enums/WeekdayKind`             | enum     | last             | yes (grouped weekend labels)          |

## Current proof status

Verified with the head-less prover (`--auto`) of this build:

* **`int/*` — all close automatically.**
* **`enums/*` — both close automatically.** Two points worth noting:
  * KeY expects enum case labels in **qualified** form
    (`case Light.RED:`, not `case RED:`); the unqualified form does not
    resolve in the front end.
  * `TrafficLight` states its postcondition as a single ordered conditional
    instead of three independent `light == X ==> \result == k` clauses. The
    latter form would additionally require proving the enum constants pairwise
    distinct (the manual "expand dynamic types" step, as in the existing
    `standard_key/java_dl/java5` Months example), whereas the ordered form is
    discharged automatically.
* **`strings/*` — load and run, but do NOT close yet.** This is intentional.
  The contracts use the *correct* `String` semantics: a case matches when the
  selector is `s.equals("label")`. The current `switch` translation, however,
  lowers each case to a **reference-equality** guard (`s == "label"`), so the
  value-based contracts cannot be proven. These examples are exactly the ones
  that should start closing once the `switch` treatment handles `String`
  selectors by value.

So the only open obligations are the `String` ones, which makes this set a
direct regression target for improved `String`/`switch` support.
