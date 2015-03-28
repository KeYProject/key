		****************************************
		*         File Header Modifier         *
		****************************************

This folder contains all content of the File Header Modifier.

Fore more details about this project contact Martin Hentschel 
(hentschel@cs.tu-darmstadt.de).


(1) Project Description
-----------------------
A utility program which is used to add the EPL header to source files of Eclipse 
based projects.


(2) Repository File Structure
-----------------------------
It provides the following file structure:
- src                  // Contains the whole source code
  - FileHeaderModifier // Contains the whole source code
- Readme.txt:          // This file


(3) Usage
---------
1.  Open class 'FileHeaderModifier'
2.  Change the constants with the directories
3.  Update the old and new header file
4.  Execute class 'FileHeaderModifier' as Java Application
5.  Replace the original source code with the created content in the output directory
6.  Open class 'FileHeaderChecker'
7.  Change the constants with the directories (Same paths)
8.  Execute class 'FileHeaderChecker' as Java Application
9.  Make sure that no files are missing
10. Make sure that the modified source code is still working