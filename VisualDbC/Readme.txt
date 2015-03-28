		******************************
		*         Visual DbC         *
		******************************

This folder contains all content of Visual DbC.

Fore more details about this project visit 
http://www.key-project.org/eclipse/VisualDbC
or contact Martin Hentschel (hentschel@cs.tu-darmstadt.de).


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


(2) Repository File Structure
-----------------------------
The project folder is structured as follows:
- src          // Contains the whole source code
  - features   // Contains the specified Eclipse features
  - plugins    // Contains the developed Eclipse plug-ins with application logic
  - tests      // Contains the developed Eclipse plug-ins with tests for the 
                  application logic
- Readme.txt:  // This file


(3) Setup Development IDE
-------------------------
Follow the steps in the sub sections precisely. Notice that you have to use
the mentioned Eclipse version!


(3.1) Setup required KeY-Based Eclipse Projects
-----------------------------------------------
1. KeY4Eclipse - Follow the instructions of Section (3) in 
   '../KeY4Eclipse/Readme.txt' carefully


(3.2) Import Eclipse Projects from GIT Repository
-------------------------------------------------
1. Select main menu item 'File, Import...'
2. Select 'General, Existing Projects into Workspace' and press 'Next >'
3. Set root directory to '<root>/GIT/KeY/VisualDbC/src'
4. Ensure that 'Copy projects into workspace' is NOT selected.
5. Finish the wizard


(4) Start Visual DbC as Eclipse Product
---------------------------------------
1. Open 'de.hentschel.visualdbc.product.ui/Visual DbC.product'
2. Click on 'Launch an Eclipse application'
   (From now on the created launch configuration can be used)


(5) Run JUnit Tests
-------------------
1. Open class 'de.hentschel.visualdbc.all.test.suite.AllVisualDbCTests'
2. Select main menu item 'Run, Run As, JUnit Plug-in Test'
   (Terminate the launched JUnit Plug-in Test.)
3. Select main menu item 'Run, Run Configurations...'
4. Select tab 'Arguments' and add the following 'VM arguments':
   -Xmx2048m -XX:MaxPermSize=256m -ea


(6) Run SWTBot Tests
--------------------
1. Open class 
   'de.hentschel.visualdbc.all.test.suite.swtbot.SWTBotAllVisualDbCTests'
2. Select main menu item 'Run, Run As, SWTBot Test'
   (Terminate the launched SWTBot Test'.)
3. Select main menu item 'Run, Run Configurations...'
4. Select tab 'Arguments' and add the following 'VM arguments':
   -Xmx2048m -XX:MaxPermSize=256m -ea -Dorg.eclipse.swtbot.search.timeout=10000


(7) Deploy Visual DbC as Eclipse product
----------------------------------------
1. Open 'de.hentschel.visualdbc.product.ui/Visual DbC.product'
2. Click on 'Eclipse Product export wizard'
3. Set 'Root directory' to 'SymbolicExecutionDebugger'
4. Define target 'Directory', e.g. 'C:\Temp'.
5. Finish the wizard.