JML Editing
===========
This folder contains all content of the Java Editor extension to support JML.

For more details about this project feel free to contact the following persons:
- Martin Hentschel (hentschel@cs.tu-darmstadt.de)


(1) Project Description
-----------------------
The aim of this project is to extend the Java Editor to support editing of JML.


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
- org.key_project.jmlediting.feature
  - org.key_project.javaeditor // General functionality to extend the Java Editor at runtime
  - org.key_project.jmlediting.core // JML support
  - org.key_project.jmlediting.ui // UI Integration of JML support
  - org.key_project.jmlediting.product.ui // Minimal Eclipse product


(4) Setup development IDE
-------------------------
1. Download Eclipse 4.4 Luna as bundle 
   "Eclipse Modeling Tools" from
   https://eclipse.org/downloads/packages/eclipse-modeling-tools/lunar
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
   
   
(5) Start the product from development IDE
------------------------------------------
1. Open file org.key_project.jmlediting.product.ui/JMLEditing.product
2. Click on "Launch an Eclipse application" in tab "Overview" of the
   opened "Product Configuration Editor"
