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


(5) Improvements to realize
---------------------------
1. Reimplement resolving to use more of JDT, see:
   https://www.google.de/url?sa=t&rct=j&q=&esrc=s&source=web&cd=5&ved=0CD8QFjAEahUKEwjJ0Zej2pvIAhVD1hQKHfvgCsY&url=https%3A%2F%2Fwww.eclipsecon.org%2F2008%2Fsub%2Fattachments%2FJDT_fundamentals.ppt&usg=AFQjCNEvqJP07qeEgjVYDLwTbQWa8j8oIQ&sig2=HsG8mWHnkCPo28-_InUB8g&bvm=bv.103627116,d.d24&cad=rja
   
   String content = "public class X {"  + "\n" +  "  String field;"   + "\n" +  "}";
   ICompilationUnit cu = fragment.createCompilationUnit("X.java", content, false, null);

   int start = content.indexOf("String");
   int length = "String".length();
   IJavaElement[] declarations = cu.codeSelect(sta