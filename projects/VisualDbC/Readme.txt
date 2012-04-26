Visual DbC (Visual Design-by-Contract)
======================================
This folder contains all content of the Symbolic Execution Debugger (SED).

For more details about this project feel free to contact the following persons:
- Martin Hentschel (hentschel@cs.tu-darmstadt.de)


(1) Project Description
-----------------------
Visual DbC provides a graphical notation, called DbC-Notation, that allows to 
visualize code structure together with specifications in the design by contract 
approach independent from used languages. Also proofs and references that occur 
during proof execution, for instance when a method is called, are included. 
The available tool support allows to create diagrams in that notation from 
scratch, to generate them from existing source code and to instantiate proofs in 
a verification tool. As verification tool is KeY, that allows to verify Java 
code with JML specifications, supported. Other verifications tools are 
integrable. Notation and tool support together are a powerful proof management 
tool to support the verification process.


(2) File Structure
------------------
It provides the following file structure:
- src: Contains the whole source code
  - features: Contains the eclipse features
  - plugins: Contains the plug-ins required to use the tool
- Readme.txt: This file


(3) Provided Eclipse features and plug-ins
------------------------------------------
- de.hentschel.visualdbc.feature // Contains all VisualDbC plug-ins
  - de.hentschel.visualdbc.dataSource // Data source API
  - de.hentschel.visualdbc.dataSource.key // Data source implementation for KeY
  - de.hentschel.visualdbc.dataSource.ui // UI controls to select data sources
  - de.hentschel.visualdbc.dbcmodel // EMF model of the DbC-Diagram
  - de.hentschel.visualdbc.dbcmodel.diagram // Generated GMF code
  - de.hentschel.visualdbc.dbcmodel.diagram.custom 
    // Special auto layout functionality in DbC-Diagrams
  - de.hentschel.visualdbc.dbcmodel.edit // Generated EMF adapter code
  - de.hentschel.visualdbc.dbcmodel.editor // Generated EMF editor
  - de.hentschel.visualdbc.example // Wizards to create example projects
  - de.hentschel.visualdbc.generation 
    // API to generate DbC-diagrams based on a data source
  - de.hentschel.visualdbc.generation.ui // UI wizards to generate DbC-diagrams
  - de.hentschel.visualdbc.help // Help book with intro
  - de.hentschel.visualdbc.interactive.proving.ui 
    // Interactive proving in a DbC-Diagram with proof reference detection 
  - de.hentschel.visualdbc.product.ui // Product definition and branding
  - de.hentschel.visualdbc.statistic.ui // Statistic view
- <tests>
  - de.hentschel.visualdbc.all.test / Allows to execute all tests at once
  - de.hentschel.visualdbc.dataSource.key.test 
    // Tests for de.hentschel.visualdbc.dataSource.key
  - de.hentschel.visualdbc.dataSource.test 
    // Tests for de.hentschel.visualdbc.dataSource
  - de.hentschel.visualdbc.dataSource.ui.test 
    // Tests for de.hentschel.visualdbc.dataSource.ui
  - de.hentschel.visualdbc.dbcmodel.diagram.custom.test 
    // Tests for de.hentschel.visualdbc.dbcmodel.diagram.custom
  - de.hentschel.visualdbc.dbcmodel.tests 
    // Tests for de.hentschel.visualdbc.dbcmodel
  - de.hentschel.visualdbc.example.test 
    // Tests for de.hentschel.visualdbc.example
  - de.hentschel.visualdbc.generation.test 
    // Tests for de.hentschel.visualdbc.generation
  - de.hentschel.visualdbc.generation.ui.test 
    // Tests for de.hentschel.visualdbc.generation.ui
  - de.hentschel.visualdbc.interactive.proving.ui.test 
    // Tests for de.hentschel.visualdbc.interactive.proving.ui
- <misc>
  - de.hentschel.visualdbc.updateSite 
    // The update site used to provide Visual DbC at 
    // http://i12www.ira.uka.de/~projekt/download/releases/eclipse/


(4) Setup development IDE
-------------------------
1. Download Eclipse 3.7 SR1 (Indigo) in 32 bit version as bundle 
   "Eclipse Modeling Tools" from
   http://www.eclipse.org/downloads/packages/eclipse-modeling-tools/indigosr1
2. Install GMF tooling
   => Help -> Install Modeling Components
   => Select "Graphical Modeling Framework Tooling" in group 
      "Concrete Syntax Development"
   => Install it by finishing the wizard
3. Install find bugs
   => Help -> Eclipse Marketplace...
   => Type in Field "Find:" the value "findbugs" and press enter.
   => Install "FindBugs Eclipse Plugin" with all features.
4. Install SWTBot
   => Help -> Eclipse Marketplace...
   => Type in Field "Find:" the value "swtbot" and press enter.
   => Install "SWTBot" with all features.
5. Install SWTBot IDE
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
   - org.key_project.key4eclipse
   - org.key_project.key4eclipse.bugfix_mac_os
   - org.key_project.key4eclipse.feature
   - org.key_project.key4eclipse.starter.core
   - org.key_project.key4eclipse.starter.core.test
   - org.key_project.key4eclipse.util
   - org.key_project.key4eclipse.util.test
   - org.key_project.swtbot.swing
   Use the import wizard "Existing Projects into Workspace" for the import.
2. Follow the steps in project file org.key_project.key4eclipse/Readme.txt
   to fix the compiler failures and to make the product deployable.
3. Import all projects from "src" into the workspace. Use the import wizard
   "Existing Projects into Workspace" for the import.   
   
   
(6) Start the product from development IDE
------------------------------------------
1. Open file de.hentschel.visualdbc.product.ui/Visual DbC.product
2. Click on "Launch an Eclipse application" in tab "Overview" of the
   opened "Product Configuration Editor"


(7) Start automated tests
-------------------------
- Start JUnit 3 tests (for generated EMF code):
  Run class de.hentschel.visualdbc.dbcmodel.tests.DbCAllTests as 
  "JUnit Plug-in Test". 

- Start JUnit 4 tests:
  Run class de.hentschel.visualdbc.all.test.suite.AllTests as 
  "JUnit Plug-in Test". 
   
- Start SWTBot tests:
  Run class de.hentschel.visualdbc.all.test.suite.swtbot.SWTBotAllTests
  as "SWTBot Test". Use the JVM settings defined in the JavaDoc comment of 
  this class.


(8) Deploy the product
----------------------
1. Open file de.hentschel.visualdbc.product.ui/Visual DbC.product
2. Click on "Eclipse Product export wizard" in tab "Overview" of the
   opened "Product Configuration Editor"
3. Define "Root directory" e.g. "VisualDbC" and 
   "Destination Directory" e.g. "C:\Temp".
4. Finish the wizard.
