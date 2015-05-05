		*******************************
		*         JML Editing         *
		*******************************

This folder contains all content of the Java Editor extension to support JML.

Fore more details about this project visit 
http://www.key-project.org/eclipse/JMLEditing
or contact Martin Hentschel (hentschel@cs.tu-darmstadt.de).


(1) Project Description
-----------------------
The aim of this project is to extend the Java Editor to support editing of JML.


(2) Repository File Structure
-----------------------------
It provides the following file structure:
- src: Contains the whole source code
  - features: Contains the eclipse features
  - plugins: Contains the plug-ins required to use the tool
  - tests: Contains all plug-ins which contains automated tests
- Readme.txt: This file


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
3. Set root directory to '<root>/GIT/KeY/JMLEditing/src'
4. Ensure that 'Copy projects into workspace' is NOT selected.
5. Finish the wizard


(4) Start JML Editing as Eclipse Product
----------------------------------------
1. Open 'org.key_project.jmlediting.product.ui/JMLEditing.product'
2. Click on 'Launch an Eclipse application'
   (From now on the created launch configuration can be used)