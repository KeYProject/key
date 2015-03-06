		********************************
		*             KeY              * 
		*        Version 2.5           *
		********************************

This is the KeY project - Integrated Deductive Software Design
Copyright (C) 2001-2011 Universität Karlsruhe, Germany
                        Universität Koblenz-Landau, Germany
                        and Chalmers University of Technology, Sweden
Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany
                        Technical University Darmstadt, Germany
                        Chalmers University of Technology, Sweden

The KeY system is protected by the GNU General
Public License. See LICENSE.TXT for details.


(1) Requirements: 
-------------------------------------

Hardware:	2 GB RAM

Operating System: Linux/Unix, MacOSX, Windows

Java SE 7 or newer

Optionally, KeY can make use of the following binaries:
	SMT Solvers: bindings exist currently for Z3, Simplify, Yices and CVC3
	             (export to SMT input file possible)


(2) Content of the KeY repository
-------------------------------------

deployment        Folder which will contain the deployed KeY binaries.

doc               Additional documentation of KeY.

key.*             A component of KeY. It contains source code and all required 
                  resources and libraries. A component is defined by a ready
                  to use Eclipse project.

scripts           Scripts to compile, start and deploy KeY.

LICENSE.TXT       Information on how KeY is licensed.


(2) Develop KeY with Eclipse
-------------------------------------

	1) Start Eclipse 4.4 (Luna) with a new workspace.
	   (Older Eclipse versions are not tested.)

	2) Import the following existing projects
	   	* key.core
	   	* key.core.proof_references
	   	* key.core.proof_references.test
	   	* key.core.symbolic_execution
	   	* key.core.symbolic_execution.test
	   	* key.core.test
	   	* key.core.testgen
	   	* key.core.testgen.test
	   	* key.ui
	   	* key.util
	   	* key.util.test

	3) Launch class 'de.uka.ilkd.key.core.Main' as Java Application to start KeY.
	   The following VM arguments are recommended: 

	   	-Xmx2048m -XX:MaxPermSize=256m -ea


(3) Compile and Start KeY using Ant
-------------------------------------

	1) Compile KeY via ant script 'scripts/build.xml'

	   	ant -buildfile scripts/build.xml compileAll

	3) Start KeY via ant script 'scripts/build.xml'

	   	ant -buildfile scripts/build.xml start

	3) Compile Tests via ant script 'scripts/build.xml'

	   	ant -buildfile scripts/build.xml compileAllTests

	4) Start Tests via ant script 'scripts/build.xml'

	   	ant -buildfile scripts/build.xml runAllTests


(4) Deploy KeY 
-------------------------------

	1) Deploy KeY via ant script 'scripts/build.xml'

	   	ant -buildfile scripts/build.xml deployAll

	2) Start deployed KeY

	   	java -jar deployment/KeY.jar


-------------------------------

If you encounter problems, please send a message to

		support@key-project.org
