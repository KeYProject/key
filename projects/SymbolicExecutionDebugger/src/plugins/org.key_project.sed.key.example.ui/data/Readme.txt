SED Examples
============
The Symbolic Execution Debugger (SED) allows to debug any method or statement
directly without setting up a fixture calling the program fragment of interest
and to explore all feasible execution paths interactively at the same time using
symbolic execution.

The examples contained in this project are designed to explain the basic usage
of the SED using a symbolic execution engine based on KeY. The project is 
organized as follows:

* src        - The source code used to explain the functionality of the SED.
* lib_specs  - Stubs for used Java API method required for symbolic execution 
               with KeY. This folder is added to KeY's class path in project
               properties page 'KeY'.
* Readme.txt - This file explaining the SED Examples.

Open an example class and follow the instructions in the Javadoc documentation. 
We recommend the following order:

1. example1.Number    - Debug a method and control symbolic execution.
2. example2.QuickSort - Find the origin of a bug.
3. example3.ArrayUtil - Use JML specifications during symbolic execution.
4. example4.AVLTree   - Inspect large data structures using memory layouts.

For more details about the Symbolic Execution Debugger (SED) visit: 
http://www.key-project.org/eclipse/SED