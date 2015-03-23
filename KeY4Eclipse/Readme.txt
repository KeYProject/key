		*********************************
		*         KeY 4 Eclipse         *
		*********************************

This folder contains all content of the KeY integration into Eclipse.

Fore more details about this project visit 
http://www.key-project.org/eclipse/Starter
or contact Martin Hentschel (hentschel@cs.tu-darmstadt.de).


(1) Project Description
-----------------------
This project hast the goals:
1. to provide the KeY code for other Eclipse plug-ins.
2. to offer general KeY specific functionality for Eclipse like settings.
3. to allow the user to start the original user interface of KeY directly 
   within Eclipse.


(2) Repository File Structure
-----------------------------
The project folder is structured as follows:
- doc          // Additional documentation
- src          // Contains the whole source code
  - features   // Contains the specified Eclipse features
  - plugins    // Contains the developed Eclipse plug-ins with application logic
  - tests      // Contains the developed Eclipse plug-ins with tests for the 
                  application logic
  - updateSite // Contains the specified Eclipse update-site
  - utilities  // Contains utilities used during development
- Readme.txt:  // This file


(3) Setup Development IDE
-------------------------
Follow the steps in the sub sections precisely. Notice that you have to use
the mentioned Eclipse version!


(3.1) Recommended Folder and File Structure
-------------------------------------------

The Eclipse Plug-in Development Environment (PDE) used to develop Eclipse 
plug-ins will automatically create new folders at fixed locations. To be not 
surprised about that, it is recommend to use the following folder structure. 

- <root> // The root folder can be chosen freely. For Windows it is recommended 
            to avoid long paths because of the 256 character limits. 
            E.g. 'D:\Research'
  - Development // Contains one folder with IDE specific meta data per 
                   project/application. In our case only one for KeY.
    - KeY // Contains the Eclipse workspace in which KeY is developed in
             and additional workspaces for launched Eclipse products.
      - eclipse_workspace // The workspace to develop KeY.
      - junit-workspace // This workspace is created automatically when a 
                           JUnit Plug-in Test is executed.
      - runtime-KeY4Eclipse.product // Workspaces like this are automatically 
                                       created when a *.product file is 
                                       launched.
      - eclipse // This is a symbolic link (shortcut) which starts 
                   Eclipse to guarantee that the correct Java version 
                   and workspace (eclipse_workspace) are used.
  - GIT // Contains all GIT repositories.
    - KeY // The GIT clone of the KeY repository.
  - Tools // Contains all related tools which require no installation.
    - jdk1.7.0_75 // The used JDK which needs to be Java 7 or newer.
    - eclipse_4_4_2 // The used Eclipse for development. 
                       (Only Eclipse Luna SR2 (4.4.2) can be used!)
                                       
Define now your root directory and move the KeY GIT repository into it.


(3.2) Install Java 7 or newer
-----------------------------

If not already available install a JDK 7 or newer. The recommended location is:
<root>/Tools/jdk1.7.0_75


(3.3) Download Eclipse Luna SR2 (4.4.2)
---------------------------------------

1. Download Eclipse Luna SR2 (4.4.2) as package 'Eclipse Modeling Tools' from:
   https://eclipse.org/downloads/packages/eclipse-modeling-tools/lunasr2
   Only this previse Eclipse version can be used! 
   Do not use a different one or a version provided by a third party like a 
   Linux distribution!

2. Extract the downloaded archive to:
   <root>/Tools/eclipse_4_4_2

3. Create symbolic link (shortcut) named 'eclipse' to start Eclipse. The use of 
   the link will ensure that the correct Java version and workspace are used. 
   Store the link for instance at '<root>/Development/KeY'.
   
   The link target should be:
      "<root>\Tools\eclipse_4_4_2\eclipse.exe" 
      -vm "<root>\Tools\jdk1.7.0_75\bin" 
      -data "<root>\Development\KeY\eclipse_workspace"
   

(3.4) Install required Eclipse Features
---------------------------------------

1. Start Eclipse via the created link '<root>/Development/KeY/eclipse'
2. Optionally install FindBugs
   2.1. Select main menu item 'Help -> Eclipse Marketplace...'
   2.2. Type in Field "Find:" the value "findbugs" and press enter.
   2.3. Install "FindBugs Eclipse Plugin <version>" with all features.
3. Install SWTBot
   3.1. Select main menu item 'Help -> Eclipse Marketplace...'
   3.2. Type in Field "Find:" the value "swtbot" and press enter.
   3.3. Install "SWTBot" with all features.
4. Install Graphiti and GMF
   4.1. Select main menu item 'Help, Install Modeling Components'
        (If not available, a wrong Eclipse Version/Package is used. 
         see Section (3.3))
   4.2. Select "Graphical Modeling Framework Tooling" and "Graphiti (Incubation)".
   4.3. Finish the wizard and install all features.


(3.5) Configure Text Editors and Code Style
-------------------------------------------

Open Preference ('Window, Preferences') and set the mentioned values. 
Keep the default values everywhere else.
1. Select preference page 'General, Editors, Text Editors'
    - Set 'Display tab width' to '3'
    - Select 'Insert spaces for tabs'
2. Select preference page 'Java, Code Style, Formatter'.
   - Import '<root>/GIT/KeY/key/doc/KeYEclipsePlugIn.xml'
     (Active Profile will automatically change to 'KeY Code Style')
3. Select preference page 'Java, Code Style, Code Templates'.
   - Edit 'Comments, Types' and replace '${user}' with your full name.
4. Select preference page 'Java, Installed JREs'
   - Ensure that the default (selected) JRE is a JDK 7 or newer.   


(3.6) Import Eclipse Projects from GIT Repository
-------------------------------------------------
KeY consists of different components specified by Eclipse Java Projects located
in the KeY repository at 'key/key.*'. These Eclipse Java Projects are not used
by the Eclipse projects. Eclipse Plug-in Projects located in the KeY
repository at 'KeY4Eclipse/src/plugins/org.key_project.*' and
'KeY4Eclipse/src/tests/org.key_project.*.test' are used instead.
These Plug-in projects provide the same source code as the Java Projects with
additional extensions required for Plug-ins. 

It is recommended NOT to work with the Java Projects and 
NOT to import them into the workspace!

1. Switch into perspective 'Plug-in Development'

2.1. Select main menu item 'File, Import...'
2.2. Select 'General, Existing Projects into Workspace' and press 'Next >'
2.3. Set root directory to '<root>/GIT/KeY/KeY4Eclipse/src'
2.4. Ensure that 'Copy projects into workspace' is NOT selected.
2.5. Finish the wizard

3.1. Select main menu item 'File, Import...'
3.2. Select 'General, Existing Projects into Workspace' and press 'Next >'
3.3. Set root directory to '<root>/GIT/KeY/Stubby/src'
3.4. Ensure that 'Copy projects into workspace' is NOT selected.
3.5. Finish the wizard

(4) Start KeY4Eclipse as Eclipse Product
----------------------------------------
1. Open 'org.key_project.key4eclipse.starter.product.ui/KeY4Eclipse.product'
2. Click on 'Launch an Eclipse application'
   (From now on the created launch configuration can be used)


(5) Start KeY as Java Application
---------------------------------
1. Open class 'de.uka.ilkd.key.core.Main'
2. Select main menu item 'Run, Run As, Java Application'
   (Terminate the launched Java Application.)
3. Select main menu item 'Run, Run Configurations...'
4. Select tab 'Arguments' and add the following 'VM arguments':
   -Xmx2048m -XX:MaxPermSize=256m -ea


(6) Run JUnit Tests
-------------------
1. Open class 'org.key_project.key4eclipse.all.test.suite.AllTests'
2. Select main menu item 'Run, Run As, JUnit Plug-in Test'
   (Terminate the launched JUnit Plug-in Test.)
3. Select main menu item 'Run, Run Configurations...'
4. Select tab 'Arguments' and add the following 'VM arguments':
   -Xmx2048m -XX:MaxPermSize=256m -ea
   
   Optionally, specify locations of SMT solver:
   -Dcvc3SolverPath=<path to application (exe) file>
   -DsimplifySolverPath=<path to application (exe) file>
   -DyicesSolverPath=<path to application (exe) file>
   -Dz3SolverPath=<path to application (exe) file>


(7) Run SWTBot Tests
--------------------
1. Open class 'org.key_project.key4eclipse.all.test.suite.swtbot.SWTBotAllTests'
2. Select main menu item 'Run, Run As, SWTBot Test'
   (Terminate the launched SWTBot Test'.)
3. Select main menu item 'Run, Run Configurations...'
4. Select tab 'Arguments' and add the following 'VM arguments':
   -Xmx2048m -XX:MaxPermSize=256m -ea -Dorg.eclipse.swtbot.search.timeout=10000


(8) Deploy KeY4Eclipse as Eclipse product
-----------------------------------------
1. Open 'org.key_project.key4eclipse.starter.product.ui/KeY4Eclipse.product'
2. Click on 'Eclipse Product export wizard'
3. Set 'Root directory' to 'KeY4Eclipse'
4. Define target 'Directory', e.g. 'C:\Temp'.
5. Finish the wizard.


(9) Important notice
--------------------
SWT and Swing run both in their own UI thread. For synchronization it is
required to use Display#syncExec(Runnable) and SwingUtil#invokeAndWait(Runnable)
or Display#asyncExec(Runnable) and SwingUtil#invokeLater(Runnable). Keep
always in mind that a synchronous call is not possible from SWT or Swing thread.
In this case only an asynchronous method call is possible. If you don't
respect this knowledge Mac OS will cause deadlocks!