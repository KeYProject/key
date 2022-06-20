# Proof Management

This project contains a proof management tool for KeY proofs. It can be used as a stand-alone program via its console
interface or as a GUI extension for KeY.

## Motivation
When verifying Java source code with JML specifications, it is standard that multiple methods with multiple
contracts must be proven. However, due to memory and time constraints, the corresponding proofs are often not conducted
during a single run of KeY. Furthermore, it is frequently the case that the source has to be re-loaded multiple times in
KeY between two proofs, since changes had to be made, for example, to the specification of the methods.

With this workflow it is crucial to have some form of proof management, since it is very difficult for the user to
manually track all changes and detect the proofs that have to be re-conducted after a change in the source code.
KeY comes with a built-in proof management that partially solves the problem. However, it is only able to detect illegal
cyclic dependencies between proofs if they are conducted in the same `Environment` (that is, without reloading the
source code in between).

The intention of this project is to provide a tool that can check a proof bundle (a directory or zip file that contains
source code and a collection of proofs) for consistency.

## Features
The proof management tool contains the following features:
* **MissingProofsChecker:** Detects contracts (in the user-provided source code) that have no proof. Note that only
  unproven contracts from inside the `src` folder are reported (not from the cp or bcp folders, see below).
* **SettingsChecker:** Detects incompatible taclet settings (called `Choices` internally in KeY) between the proofs of a
  bundle. An example of this would be that one proof is conducted using mathematical integer semantics and another one
  with Java integers.
* **ReplayChecker:** Detects proofs that can not be replayed, for example because they were conducted with an old KeY
  version or because the proof file was edited manually and contains syntax errors.
* **DependencyChecker:** Detects proofs that contain unproven dependencies (i.e., rely on contracts that are unproven).
  In addition, the dependency checker reports illegal cyclic dependencies between proofs, for example if two mutually
  recursive methods contain wrong `measured_by` clauses and are proven separately with KeY (and thus the bundle contains
  two proofs that are both correctly closed per se).
* **HTML report:** Besides the plain text messages on the console, an HTML report can be generated that contains the
  console messages in a filterable format, lists contracts, proofs, and shows their corresponding status.

## Usage
### Stand-alone Program (CLI)
```
Usage: pm <command> [<options>...] [<args>...]
  available commands:
    check: Checks a single proof bundle for consistency.
    merge: Merges two proof bundles.
    bundle: Creates a zipped proof bundle (file extension "zproof") from a directory following the proof bundle path rules.
```

Note that only the `check` command is currently implemented, which has the following options:
```
pm check [--missing] [--settings] [--replay] [--dependency] [--report <out_path>] <bundle_path>
```
As expected, the available options correspond to the features described in the section above.
`<bundle_path>` is the path of the proof bundle to check and can either denote a directory or a zip file.

The directory structure of the bundle has to conform that described in
[classpath documentation](https://key-project.org/docs/user/Classpath/).
An example of a (zipped) proof bundle would be:
```
bundle.zproof
  - src            // java classes (.java files only)
    - A.java
    - mypackage
      - B.java
      - C.java
  - cp             // optional: classpath (may contain .jar files and subdirectories
                   //           with .java and/or .class files)
    - someLibrary.java
    - otherLibrary
      - Lib.java
      - Util.class
  - bcp            // optional: bootclasspath (system classes from the Java class library),
                   //           replaces the files shipped with KeY
    - java
      - lang
        - Math.java
        - String.java
        - System.java
        ...
      - math
      ...
```

### KeY GUI Extension
The project adds the `Proof Management` menu to KeY. It currently contains only a single entry which opens a dialog to
configure the checkers to run and the path for the HTML report to generate. After a successful run, the HTML report is
opened in the system's default browser.

## Known Problems / Missing features
Some features are currently not implemented:
* It is not checked that user-defined rules (taclets included in user-provided .key files) are proven.
* Functionality to merge two proof bundles (if there sources and proofs are consistent) is missing.
* For the SettingsChecker, taclet settings have to be exactly identical at the moment, which could probably be relaxed a
  bit in the future.
