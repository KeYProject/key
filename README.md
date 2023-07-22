# KeY -- Deductive Java Program Verifier

[![Tests](https://github.com/KeYProject/key/actions/workflows/tests.yml/badge.svg)](https://github.com/KeYProject/key/actions/workflows/tests.yml) [![CodeQL](https://github.com/KeYProject/key/actions/workflows/codeql.yml/badge.svg)](https://github.com/KeYProject/key/actions/workflows/codeql.yml) [![CodeQuality](https://github.com/KeYProject/key/actions/workflows/code_quality.yml/badge.svg)](https://github.com/KeYProject/key/actions/workflows/code_quality.yml) 

This repository contains the interactive theorem prover "KeY" for the verification of Java programs.

You can find more information about KeY on https://key-project.org or use the
documentation in the companion repository [key-docs](https://github.com/KeYProject/key-docs).
The content of the latter is also available as HTML version under https://keyproject.github.io/key-docs/.

The current version of KeY is 2.10.0, licensed under GPL v2.


## Requirements

* Hardware: >=2 GB RAM
* Operating System: Linux/Unix, MacOSX, Windows
* Java SE 11 or newer
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

If you encounter problems, please send a message to support@key-project.org



# License Remark

```
This is the KeY project - Integrated Deductive Software Design
Copyright (C) 2001-2011 Universität Karlsruhe, Germany
						Universität Koblenz-Landau, Germany
						and Chalmers University of Technology, Sweden
Copyright (C) 2011-2023 Karlsruhe Institute of Technology, Germany
						Technical University Darmstadt, Germany
						Chalmers University of Technology, Sweden

The KeY system is protected by the GNU General Public License.
See LICENSE.TXT for details.
```
