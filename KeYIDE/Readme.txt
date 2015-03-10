		**************************
		*         KeYIDE         *
		**************************

This folder contains all content of the KeYIDE.

Fore more details about this project visit 
http://www.key-project.org/eclipse/KeYIDE
or contact Martin Hentschel (hentschel@cs.tu-darmstadt.de).


(1) Project Description
-----------------------
The goal of the KeYIDE is to provide an alternative user interface for KeY
which is directly integrated into Eclipse.


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
2. Visual DbC - Follow the instructions of Section (3) in 
   '../VisualDbC/Readme.txt' carefully


(3.2) Import Eclipse Projects from GIT Repository
-------------------------------------------------
1. Select main menu item 'File, Import...'
2. Select 'General, Existing Projects into Workspace' and press 'Next >'
3. Set root directory to '<root>/GIT/KeY/KeYIDE/src'
4. Ensure that 'Copy projects into workspace' is NOT selected.
5. Finish the wizard


(4) Start KeYIDE as Eclipse Product
-----------------------------------
1. Open 'org.key_project.keyide.product.ui/KeYIDE.product'
2. Click on 'Launch an Eclipse application'
   (From now on the created launch configuration can be used)


(5) Run JUnit Tests
-------------------
1. Open class 'org.key_project.keyide.ui.test.suite.AllKeYIDEUITests'
2. Select main menu item 'Run, Run As, JUnit Plug-in Test'
   (Terminate the launched JUnit Plug-in Test.)
3. Select main menu item 'Run, Run Configurations...'
4. Select tab 'Arguments' and add the following 'VM arguments':
   -Xmx2048m -XX:MaxPermSize=256m -ea


(6) Run SWTBot Tests
--------------------
1. Open class 
   'org.key_project.keyide.ui.test.suite.swtbot.SWTBotAllKeYIDEUITests'
2. Select main menu item 'Run, Run As, SWTBot Test'
   (Terminate the launched SWTBot Test'.)
3. Select main menu item 'Run, Run Configurations...'
4. Select tab 'Arguments' and add the following 'VM arguments':
   -Xmx2048m -XX:MaxPermSize=256m -ea -Dorg.eclipse.swtbot.search.timeout=10000


(7) Deploy KeYIDE as Eclipse product
------------------------------------
1. Open 'org.key_project.keyide.product.ui/KeYIDE.product'
2. Click on 'Eclipse Product export wizard'
3. Set 'Root directory' to 'KeYIDE'
4. Define target 'Directory', e.g. 'C:\Temp'.
5. Finish the wizard.