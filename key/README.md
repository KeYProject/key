# KeY -- Deductive Java Program Verifier

Currrent Version: 2.7.X 


## Requirements: 

* Hardware: >=2 GB RAM
* Operating System: Linux/Unix, MacOSX, Windows
* Java SE 8 or newer
* Optionally, KeY can make use of the following binaries:
  * SMT Solvers: 
    * [Z3](https://github.com/Z3Prover/z3) 
    * [CVC4](http://cvc4.cs.stanford.edu/web/) 
    * [CVC3](https://cs.nyu.edu/acsys/cvc3/) 
    * [Simplify]() 
    * [Yices](http://yices.csl.sri.com/) -- currently not support 


## Content of the KeY repository

* `build.gradle` -- root build script
* `key.*/` -- KeY's core components. 
* `keyext.*/` -- KeY's additonal components. 
* `LICENSE.TXT`       Information on how KeY is licensed.

KeY follows the [Maven's standard folder
layout](https://maven.apache.org/guides/introduction/introduction-to-the-standard-directory-layout.html)

The documentation of KeY is in the companion repository [key-docs](https://git.key-project.org/key/key-docs).

## Compile and Run KeY

Assuming you are in directory `key/`.

**Quick Start:** 
```
./gradlew run
```

Compile KeY, includes running JavaCC and Antlr
```
./gradlew classes
```

Run all test cases
```
./gradlew test 
```

Run a specific test case
```
./gradlew :key.<subproject>:test --tests "<class>.<method>"
```

You can debug KeY by adding the `--debug-jvm` option, then attaching a debugger at `localhost:5005`.


You can create a *fat jar* with 
```
./gradlew :key.ui:shadowJar 
```
The file is generated in `key.ui/build/libs/key-*-exe.jar`.

A distributiion is build wit 
```
./gradlew :key.ui:installDist :key.ui:distZip
```	
The distribution can tested by calling `key.ui/install/key/bin/key.ui` 
and is zipped in `key.ui/build/distributions`.


---

If you encounter problems, please send a message to

		support@key-project.org


# License Remark

```
This is the KeY project - Integrated Deductive Software Design
Copyright (C) 2001-2011 Universität Karlsruhe, Germany
                        Universität Koblenz-Landau, Germany
                        and Chalmers University of Technology, Sweden
Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
                        Technical University Darmstadt, Germany
                        Chalmers University of Technology, Sweden

The KeY system is protected by the GNU General
Public License. See LICENSE.TXT for details.
```
