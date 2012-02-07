Symbolic Execution Debugger (SED)
=================================
This folder contains all content of the Symbolic Execution Debugger (SED).

For more details about this project feel free to contact the following persons:
- Martin Hentschel (hentschel@cs.tu-darmstadt.de)


(1) Project Description
-----------------------
A new debugging approach is presented by introducing a software debugger which 
is based on visualizing symbolic program executions. Symbolic execution is a 
program analysis technique that runs a program with symbolic input values 
representing unknown values in order to explore all possible program executions. 
An obvious benefit of such a debugger is that symbolic execution explores all 
possible program executions, and it thus can be used for finding program 
executions that are not intended by the programmer. Symbolic execution captures 
the entire behavior of a program up to a certain point. So once a bug is 
recognized, the debugger can also be used to find the origin of the bug in the 
source code, the reason for the misbehavior and sometimes even possible fixes.


(2) File Structure
------------------
It provides the following file structure:
- src: Contains the whole source code
  - features: Contains the eclipse features
  - plugins: Contains the plug-ins required to use the tool
- Readme.txt: This file


(3) Provided Eclipse features and plug-ins
------------------------------------------
- org.key_project.sed.feature // Contains all SED plug-ins
  - org.key_project.sed.product.ui // Product definition and branding


(4) Setup development IDE
-------------------------
1. Download Eclipse 3.7 SR1 (Indigo) (e.g. in 32 bit version) as bundle 
   "Eclipse Modeling Tools" from
   http://www.eclipse.org/downloads/packages/eclipse-modeling-tools/indigosr1
2. Install find bugs
   => Help -> Eclipse Marketplace...
   => Type in Field "Find:" the value "findbugs" and press enter.
   => Install "FindBugs Eclipse Plugin" with all features.
3. Install SWTBot
   => Help -> Eclipse Marketplace...
   => Type in Field "Find:" the value "swtbot" and press enter.
   => Install "SWTBot" with all features.
4. Install SWTBot IDE
   => Help -> Install New Software...
   => Select "--All Available Sites--" in field "Work with:"
   => Select "SWTBot IDE Support (incubation)/SWTBot IDE Features (incubation)" 
      (Version 2.0.4...)
   => Install it by finishing the wizard


(5) Development
---------------
To develop the project it is recommended to use an empty Eclipse workspace
which can be stored in any directory. It is recommend to store it outside
of the checkout of the KeY repository. The workspace should be configured
with the settings described at:
http://i12www.ira.uka.de/~klebanov/keywiki/index.cgi?KeYDevelopmentInEclipse

To add the required Eclipse projects follow these steps:
1. Import the following projects from ../KeY4Eclipse/src/plugins:
   - org.key_project.key4eclipse.feature
   - org.key_project.key4eclipse
   - org.key_project.key4eclipse.util
   Use the import wizard "Existing Projects into Workspace" for the import.
2. Follow the steps in project org.key_project.key4eclipse/Readme.txt
   to fix the compiler failures and to make the product deployable.
3. Import all projects from "src" into the workspace. Use the import wizard
   "Existing Projects into Workspace" for the import.
   
   
(6) Start the product from development IDE
------------------------------------------
1. Open file org.key_project.sed.product.ui/SymbolicExecutionDebugger.product
2. Click on "Launch an Eclipse application" in tab "Overview" of the
   opened "Product Configuration Editor"


(7) Start automated tests
-------------------------
Coming soon...


(8) Deploy the product
----------------------
1. Open file org.key_project.sed.product.ui/SymbolicExecutionDebugger.product
2. Click on "Eclipse Product export wizard" in tab "Overview" of the
   opened "Product Configuration Editor"
3. Define "Root directory" e.g. "SymbolicExecutionDebugger" and 
   "Destination Directory" e.g. "C:\Temp".
4. Finish the wizard.
