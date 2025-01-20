# KeY -- Deductive Java Program Verifier

[![Tests](https://github.com/KeYProject/key/actions/workflows/tests.yml/badge.svg)](https://github.com/KeYProject/key/actions/workflows/tests.yml) [![CodeQL](https://github.com/KeYProject/key/actions/workflows/codeql.yml/badge.svg)](https://github.com/KeYProject/key/actions/workflows/codeql.yml) [![CodeQuality](https://github.com/KeYProject/key/actions/workflows/code_quality.yml/badge.svg)](https://github.com/KeYProject/key/actions/workflows/code_quality.yml) 

This repository is the home of the interactive theorem prover KeY for formal verification and analysis of Java programs. KeY comes as a standalone GUI application, which allows you to verify the functional correctness of Java programs with respect to formal specifications formulated in the Java Modeling Language JML. Moreover, KeY can also be used as a library e.g. for symbolic program execution, first order reasoning, or test case generation.

For more information, refer to

* [The KeY homepage](https://key-project.org) 
* [The KeY book](https://www.key-project.org/thebook2/)
* [The KeY developer documentation](https://keyproject.github.io/key-docs/)
* KeY's success stories:
  * [Severe bug discovered in JDK sorting routine (TimSort)](http://www.envisage-project.eu/proving-android-java-and-python-sorting-algorithm-is-broken-and-how-to-fix-it/),  
  * [Verification of `java.util.IdentityHashMap`](https://doi.org/10.1007/978-3-031-07727-2_4),
  * [Google Award for analysing a bug in `LinkedList`](https://www.key-project.org/2023/07/23/cwi-researchers-win-google-award-for-finding-a-bug-in-javas-linkedlist-using-key/)

The current version of KeY is 2.12.2, licensed under GPL v2.


Feel free to use the project templates to get started using KeY:
* [For Verification Projects](https://github.com/KeYProject/verification-project-template)
* [Using as a Library](https://github.com/KeYProject/key-java-example)
* [Using as a Symbolic Execution Backend](https://github.com/KeYProject/symbex-java-example)

## Requirements

* Hardware: >=2 GB RAM
* Operating System: Linux/Unix, MacOSX, Windows
* Java 17 or newer
* Optionally, KeY can make use of the following binaries:
  * SMT Solvers:
    * [Z3](https://github.com/Z3Prover/z3#z3)
    * [cvc5](https://cvc5.github.io/)
    * [CVC4](https://cvc4.github.io/)
    * [Princess](http://www.philipp.ruemmer.org/princess.shtml)

## Content of the KeY folder

This folder provides a [gradle](https://gradle.org)-managed project following
[Maven's standard folder layout](https://maven.apache.org/guides/introduction/introduction-to-the-standard-directory-layout.html).
There are several subprojects in this folder. In general, every `key.*/` subproject contains a core component of KeY.
Additional and optional components are in `keyext.*/` folders. The file `build.gradle` is the root build script
describing the dependencies and common build tasks for all subprojects.

`key.util`, `key.core` and `key.ui` are the base for the product "KeY Prover". Special care is needed
if you plan to make changes here.


## Compile and Run KeY

Assuming you are in the directory of this README file, you can create a runnable and deployable version with one of these commands:

1. With `./gradlew key.ui:run` you can run the user interface of KeY directly from the repository. 
   Use `./gradlew key.ui:run --args='--experimental'` to enable experimental features.

2. Use `./gradlew classes` to compile KeY, which includes running JavaCC and Antlr.
   Likewise, use `./gradlew testClasses` if you also want to compile the JUnit test classes.

3. Test your installation with `./gradlew test`. Be aware that this will usually take multiple hours to complete.
   With `./gradlew testFast`, you can run a more lightweight test suite that should complete in a few minutes.

   You can select a specific test case with the `--tests` argument. Wildcards are allowed.
   ```sh
   ./gradlew :key.<subproject>:test --tests "<class>.<method>"
   ```

   You can debug KeY by adding the `--debug-jvm` option, then attaching a debugger at `localhost:5005`.

4. You can create a single jar-version, aka *fat jar*, of KeY with
   ```sh
   ./gradlew :key.ui:shadowJar
   ```
   The file is generated in `key.ui/build/libs/key-*-exe.jar`.

5. A distribution is build with
   ```sh
   ./gradlew :key.ui:installDist :key.ui:distZip
   ```
   The distribution can be tested by calling `key.ui/install/key/bin/key.ui`
   and is zipped in `key.ui/build/distributions`.

   The distribution gives you potential of using single jar files.

# Developing KeY

* Quality is automatically assessed using [SonarQube](https://sonarqube.org) on each pull request.
  The results of the assessments (pass/fail) can be inspected in the checks section of the PR.

  The rules and quality gate are maintained by Alexander Weigl
  <weigl@kit.edu> currently.

* More guideline and documentation for the KeY development can be found under
[key-docs](https://keyproject.github.io/key-docs/devel/).



# Issues and Bug Reports

* For bug reports, please use the [issue tracker](https://github.com/KeYProject/key/issues) or send a mail to support@key-project.org. 

* For discussions, you may want to subscribe and use the mailing list <key-all@lists.informatik.kit.edu> or use [GitHub discussions](https://github.com/KeYProject/key/discussions).

# Contributing to KeY

Feel free to submit [pull requests](https://github.com/KeYProject/key/pulls) via GitHub. Pull requests are assessed using automatic tests, formatting and static source checkers, as well as a manual review by one of the developers. More guidelines and documentation for the KeY development can be found under [key-docs](https://keyproject.github.io/key-docs/devel/).



# License Remark

```
This is the KeY project - Integrated Deductive Software Design
Copyright (C) 2001-2011 Universität Karlsruhe, Germany
						Universität Koblenz-Landau, Germany
						and Chalmers University of Technology, Sweden
Copyright (C) 2011-2024 Karlsruhe Institute of Technology, Germany
						Technical University Darmstadt, Germany
						Chalmers University of Technology, Sweden

The KeY system is protected by the GNU General Public License.
See LICENSE.TXT for details.
```
