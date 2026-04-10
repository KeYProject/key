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
KeY comes with a built-in proof management that partially solves the problem. However, this internal proof management
has a few shortcomings:
1) It only considers the proofs currently loaded in the GUI. This is often not really helpful, since usually it is not a
   good idea to have too many proofs loaded at the same time (memory restrictions).
2) It only considers proofs loaded in the same environment (via "File" -> "Proof Management"), which is an option that
   is not obvious to many users. Furthermore, if the source code changes, a new environment is (and has to be, for 
   soundness reasons) created.
3) The current proof management does not check for compatible settings (overflows, different integer semantics, runtime
   exceptions, ...).
4) Some dependencies are not checked by KeY, for example cycles involving model methods or dependency contracts.

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
    merge: Merges multiple proof bundles.
```

#### check
The `check` command performs the selected consistency checks and is able to give a console or HTML report:
```
pm check [--missing] [--settings] [--replay] [--dependency] [--report <out_path>] <bundle_path>
```
The available options correspond to the features described in the section above.
`<bundle_path>` is the path of the proof bundle to check and can either denote a directory or a zip file.

The directory structure of the bundle has to conform that described in
[classpath documentation](https://keyproject.github.io/key-docs/user/Classpath/).
An example of a (zipped) proof bundle would be:
```
bundle.zproof
  - src            // java classes (.java files only)
    - A.java
    - mypackage
      - B.java
      - C.java
  - classpath      // optional: classpath (may contain .jar files and subdirectories
                   //           with .java and/or .class files)
    - someLibrary.java
    - otherLibrary
      - Lib.java
      - Util.class
  - bootclasspath  // optional: bootclasspath (system classes from the Java class library),
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

#### merge
The `merge` command merges multiple bundles in zip or directory format into a single one.
```
pm merge [--force] [--check "<check_args>"] <bundle1> <bundle2> ... <output>
```
Merging fails when two or more of the input bundles contain files with the same name (at the same path), but different
content. This can be the case if for example different versions of the Java code were used for the proofs. To merge
nonetheless, the `--force` flag can be set. In this case, the resulting bundle will contain the versions from the first
given bundle.

As a shortcut, the command has a `--check` option which performs the check command on the resulting bundle after the
merge and forwards the given arguments to that command.

### KeY GUI Extension
The project adds the `Proof Management` menu to KeY. It currently contains only a single entry which opens a dialog to
configure the checkers to run and the path for the HTML report to generate. After a successful run, the HTML report is
opened in the system's default browser.

## Known Problems / Missing features
Some features are currently not implemented:
* It is not checked that user-defined rules (taclets included in user-provided .key files) are proven.
* For the SettingsChecker, taclet settings have to be exactly identical at the moment, which could probably be relaxed a
  bit in the future.
* An `--auto` flag could be added for the `check` command, which tries to proof contracts without explicit proofs
  automatically. There could also be an option to save these automatically found proofs into the bundle.
* There could be a `bundle` command that creates a proof bundle by creating the required file structure based on the
  information provided in a `.key` file.
