KeY 4 Eclipse
=============
This folder contains all content of the KeY integration into Eclipse.

For more details about this project feel free to contact the following persons:
- Martin Hentschel (hentschel@cs.tu-darmstadt.de)
- Niklas Bunzel (niklas.bunzel@gmx.de)
- Marco Drebing (marcodrebing@gmail.com)
- Christoph Schneider (scneider.christoph@gmx.de)
- Stefan Käsdorf (stefan.kaesdorf@web.de)


(1) Project Description
-----------------------
The aim of this project is to provide the KeY functionality in Eclipse.

The Eclipse Plug-In has the following user relevant features:
- Start proof for a Java method/constructor via context menu or main menu
- Start and stop the auto mode
- View the Proof Tree
- Setting Proof Search Strategy Properties



(2) File Structure
------------------
It provides the following file structure:
- src: Contains the whole source code
  - features: Contains the eclipse features
  - plugins: Contains the plug-ins required to use the tool
  - tests: Contains all plug-ins which contains automated tests
- Readme.txt: This file


(3) Provided Eclipse features and plug-ins
------------------------------------------

- org.key_project.keyide.feature 
  // Provides UI integration of KeY into Eclipse
  - org.key_project.keyide.product.ui // Product and branding
- <tests>
  // Extends SWTBot for Swing
  - org.key_project.keyide.ui.test // Allows to execute ui tests
  


(4) Setup development IDE
-------------------------
1. Download Eclipse 3.7 SR2 (Indigo) (e.g. in 32 bit version) as bundle 
   "Eclipse Modeling Tools" from
   http://www.eclipse.org/downloads/packages/eclipse-modeling-tools/indigosr2
2. Install SWTBot
   => Help -> Eclipse Marketplace...
   => Type in Field "Find:" the value "swtbot" and press enter.
   => Install "SWTBot" with all features.
3. Install SWTBot IDE
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
1. Import all projects from "src" into the workspace. Use the import wizard
   "Existing Projects into Workspace" for the import.
2. Follow the steps src/plugins/org.key_project.keyide/Readme.txt to
   fix the compiler failures and to make that the product is deployable.
   
   
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
1. Open file org.key_project.keyide.product.ui/KeYIDE.product
2. Click on "Launch an Eclipse application" in tab "Overview" of the
   opened "Product Configuration Editor"


(8) Start automated tests
-------------------------
- Start JUnit tests:
  Run class org.key_project.keyide.all.test.suite.AllTests as 
  "JUnit Plug-in Test". 
   
- Start SWTBot tests:
  Run class org.key_project.keyide.all.test.suite.swtbot.SWTBotAllTests
  as "SWTBot Test". Use the JVM settings defined in the JavaDoc comment of 
  this class.


(9) Deploy the product
----------------------
1. Open file org.key_project.keyide.product.ui/KeYIDE.product
2. Click on "Eclipse Product export wizard" in tab "Overview" of the
   opened "Product Configuration Editor"
3. Define "Root directory" e.g. "KeYIDE" and "Destination Directory"
   e.g. "C:\Temp".
4. Finish the wizard.
