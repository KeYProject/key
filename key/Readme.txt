		********************************
		*             KeY              * 
		*        Version 2.5           *
		********************************

This is the KeY project - Integrated Deductive Software Design
Copyright (C) 2001-2011 Universität Karlsruhe, Germany
                        Universität Koblenz-Landau, Germany
                        and Chalmers University of Technology, Sweden
Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
                        Technical University Darmstadt, Germany
                        Chalmers University of Technology, Sweden

The KeY system is protected by the GNU General
Public License. See LICENSE.TXT for details.


(1) Requirements: 
-------------------------------------

Hardware:	>=2 GB RAM

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

	1) Start Eclipse 4 (Newest version recommended) with a new workspace.
	   (Eclipse 3.7 (Indigo) and older versions do not work.)

	2) Ensure that a JRE/JDK 1.7 or newer is selected at preference page
	   'Java/Installed JREs'

	3) Optionally, set the following recommended preferences:
	   	* General/Editors/Text Editors
	   	  	* Set 'Displayed tab width' to 3
	   	  	* Select 'Insert spaces for tabs'
	   	* Java/Code Style/Code Templates
	   	  	* Set your full name as @author of 'Comments/Types'
	   	* Java/Code Style/Formatter
	   	  	* Import 'doc/KeYCodeStyle.xml' and select active profile 
	   	  	  'KeY Code Style'

	4) Import the following existing Eclipse Java projects (simply select the folder "key" in the import-dialog)
	   	* key.core (no GUI components allowed; can only access key.util)
	   	* key.core.proof_references (no GUI components allowed; can only access key.util, key.core)
	   	* key.core.proof_references.test
	   	* key.core.symbolic_execution (no GUI components allowed; can only access key.util, key.core)
	   	* key.core.symbolic_execution.test
	   	* key.core.test
	   	* key.core.testgen (no GUI components allowed; can only access key.util, key.core, key.core.*)
	   	* key.core.testgen.test
	   	* key.ui (all GUI stuff goes here)
	   	* key.util (only general utils cannot access any other KeY component)
	   	* key.util.test
	      (* key.core.example   Shows how to programmatically verify all proof 
	                            obligations of the source code and is not used by 
	                            KeY itself.)

	   Attention: The Java projects are not used by the KeY-Based Eclipse 
	              Projects. Instead the Plug-in projects of '../KeY4Eclipse' have
	              to be used. It is not recommended to have both in the same 
	              workspace as they provide the same content.

	5) Launch class 'de.uka.ilkd.key.core.Main' as Java Application to start KeY.
	   The following VM arguments are recommended: 

	   	-Xmx2048m -XX:MaxPermSize=256m -ea


(3) Compile and Start KeY using Ant
-------------------------------------

Assuming you are in directory "key" (if you are in directory
"key/scripts" the "-buildfile scripts/build.xml" can be skipped)

	1) Compile KeY via ant script 'scripts/build.xml'

	   	ant -buildfile scripts/build.xml compileAll

	3) Start KeY via ant script 'scripts/build.xml'

	   	ant -buildfile scripts/build.xml start

	   [[Linux users: the "key" shell script can also be used]]

	3) Compile Tests via ant script 'scripts/build.xml'

	   	ant -buildfile scripts/build.xml compileAllTests

	4) Start Tests via ant script 'scripts/build.xml'

	   	ant -buildfile scripts/build.xml runAllTests


(4) Deploy KeY 
-------------------------------

	1) Deploy KeY via ant script 'scripts/build.xml'

	   	ant -buildfile scripts/build.xml deployAll

	2) Test deployed jar files

	   	ant -buildfile scripts/build.xml test-deploy-all

	3) Start deployed KeY

	   	java -Xmx2048m -jar deployment/KeY.jar

	

-------------------------------

If you encounter problems, please send a message to

		support@key-project.org
