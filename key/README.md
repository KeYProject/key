# KeY -- Deductive Java Program Verifier

This folder contains the interactive theorem prover KeY for the verification of Java programs.

You can find more information on KeY on our [website](https://key-project.org) or in use the 
documentation in the companion repository [key-docs](https://git.key-project.org/key/key-docs).

The current version is 2.8.0, licensed under GPL v2. 


## Requirements: 

* Hardware: >=2 GB RAM
* Operating System: Linux/Unix, MacOSX, Windows
* Java SE 8 or newer
* Optionally, KeY can make use of the following binaries:
  * SMT Solvers: 
    * [Z3](https://github.com/Z3Prover/z3) 
    * [CVC4](http://cvc4.cs.stanford.edu/web/) 

## Content of the KeY folder

This folder provides a [gradle](https://gradle.org)-managed project following 
[Maven's standard folder layout](https://maven.apache.org/guides/introduction/introduction-to-the-standard-directory-layout.html).
There are several modules in this folder. In general every `key.*/` contains a core component of KeY. Additional 
and optional components are in `keyext.*/` folders. The file `build.gradle` is the root build script describing 
the dependencies and build tasks for all sub-modules.

`key.util`, `key.core` and `key.ui` are the base for the product "KeY Prover". Special care are needed 
if you plan to make changes here. 


## Compile and Run KeY

Assuming you are in directory `key/`, the directory of this README file, 
then you can create a runnable and deployable version with one of these commands:

1. With `./gradlew :key.ui:run` you can run the user interface of KeY directly from the repository.

2. Use `./gradlew classes` to compile KeY, includes running JavaCC and Antlr, additional use `./gradlew testClasses` if 
   you also want to compile the JUnit test classes. 

3. Test your installation with `./gradlew test` or `./gradlew testFast`. 
   The later command disables the slow running test cases.
   
   You can select a specific test case with `--tests` argument. Wildcards are allowed. 
   ```
   ./gradlew :key.<subproject>:test --tests "<class>.<method>"
   ```

   You can debug KeY by adding the `--debug-jvm` option, then attaching a debugger at `localhost:5005`.

4. You can create a single jar-version, aka *fat jar*, of KeY with 
   ```
   ./gradlew :key.ui:shadowJar 
   ```
   The file is generated in `key.ui/build/libs/key-*-exe.jar`.

5. A distributiion is build with 
   ```
   ./gradlew :key.ui:installDist :key.ui:distZip
   ```
   The distribution can tested by calling `key.ui/install/key/bin/key.ui` 
   and is zipped in `key.ui/build/distributions`.

   The distribution gives you potential of using single jar files.
   
# Issues and Bug Reports

If you encounter problems, please send a message to

		<support@key-project.org>


# License Remark

```
This is the KeY project - Integrated Deductive Software Design
Copyright (C) 2001-2011 Universität Karlsruhe, Germany
                        Universität Koblenz-Landau, Germany
                        and Chalmers University of Technology, Sweden
Copyright (C) 2011-2020 Karlsruhe Institute of Technology, Germany
                        Technical University Darmstadt, Germany
                        Chalmers University of Technology, Sweden

The KeY system is protected by the GNU General Public License. 
See LICENSE.TXT for details.
```
