		*********************************
		*         Shell Utility         *
		*********************************

This folder contains all content of the Shell Utility.

Fore more details about this project contact Martin Hentschel 
(hentschel@cs.tu-darmstadt.de).


(1) Project Description
-----------------------
Integrates a Wizard into Eclipse which is opened via keyboard shortcut STRG+0
to specifiy size and location of the current window. This is useful for instance
to create screencasts.


(2) Repository File Structure
-----------------------------
The project folder is structured as follows:
- src          // Contains the whole source code
  - features   // Contains the specified Eclipse features
  - plugins    // Contains the developed Eclipse plug-ins with application logic
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
3. Set root directory to '<root>/GIT/KeY/ShellUtility/src'
4. Ensure that 'Copy projects into workspace' is NOT selected.
5. Finish the wizard