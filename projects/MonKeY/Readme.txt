MonKeY
======
This folder contains all content of MonKeY.

For more details about this project feel free to contact the following persons:
- Martin Hentschel (hentschel@cs.tu-darmstadt.de)


(1) Project Description
-----------------------
The aim of this project is to provide a simple user interface that
allows to proof a whole project automatically in KeY. The program starts
for all available proof abligation a proof in KeY and tries to fulfill
it with the automatic mode. Finally the user can export the verification
result as CSV file.

The functionality to proof a whole project automatically was requested by:
- Ina Schaefer (i.schaefer@tu-braunschweig.de)
- Thomas Thüm (thomas.thuem@ovgu.de)
- Sven Apel (apel@fim.uni-passau.de)


(2) File Structure
------------------
It provides the following file structure:
- src: Contains the whole source code
  - features: Contains the eclipse features
  - plugins: Contains the plug-ins required to use the tool
- Readme.txt: This file


(3) Provided Eclipse features and plug-ins
------------------------------------------
- org.key_project.monkey.feature
  // Provides the whole functionality
  - org.key_project.monkey.product.ui // The whole functionality.
  - org.key_project.monkey.help // The help pages.
- <tests>
  - org.key_project.monkey.all.test // Allows to execute all tests at once
  - org.key_project.monkey.product.ui.test 
    // Tests for org.key_project.monkey.product.ui

(4) Setup development IDE
-------------------------
1. Download Eclipse 3.7 SR2 (Indigo) (e.g. in 32 bit version) as bundle 
   "Eclipse Modeling Tools" from
   http://www.eclipse.org/downloads/packages/eclipse-modeling-tools/indigosr2
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


(5) Development (Workspace configuration)
-----------------------------------------
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
2. Follow the steps in project org.key_project.key4eclipse/Readme.txt
   to fix the compiler failures and to make the product deployable.
3. Import all projects from "src" into the workspace. Use the import wizard
   "Existing Projects into Workspace" for the import.
   
   
(6) Important notice
--------------------
SWT and Swing runs both in his own UI thread. For synchronization it is
required to use Display#syncExec(Runnable) and SwingUtil#invokeAndWait(Runnable)
or Display#asyncExec(Runnable) and SwingUtil#invokeLater(Runnable). Keep
always in mind that a synchronous call is not possible from SWT or Swing thread.
In this case only an asynchronous method call is possible. If you don't
respect this knowledge Mac OS will cause deadlocks!   

   
(7) Start the product from development IDE
------------------------------------------
1. Open file org.key_project.monkey.product.ui/MonKeY.product
2. Click on "Launch an Eclipse application" in tab "Overview" of the
   opened "Product Configuration Editor"

   
(8) Start the product in batch mode from development IDE
--------------------------------------------------------
1. Create a duplicate of created launch configuration from section
   (7) Start the product from development IDE.
2. Add program argument -batch
3. Launch configuration

   
(9) Start the contained KeY from development IDE
------------------------------------------------
1. Create a duplicate of created launch configuration from section
   (7) Start the product from development IDE.
2. Add program argument -keyonly
3. Launch configuration
   

(10) Start automated tests
-------------------------
- Start JUnit tests:
  Run class org.key_project.monkey.all.test.suite.AllMonKeYTests as 
  "JUnit Plug-in Test". 
   
- Start SWTBot tests:
  Run class org.key_project.monkey.all.test.suite.swtbot.SWTBotAllMonKeYTests
  as "SWTBot Test". Use the JVM settings defined in the JavaDoc comment of 
  this class.


(11) Deploy the product
-----------------------
1. Open file org.key_project.monkey.product.ui/MonKeY.product
2. Click on "Eclipse Product export wizard" in tab "Overview" of the
   opened "Product Configuration Editor"
3. Define "Root directory" e.g. "MonKeY" and "Destination Directory"
   e.g. "C:\Temp".
4. Finish the wizard.
5. Windows only: Copy content from 
   org.key_project.monkey.product.ui/deployment/win32
   into the created root directory. 