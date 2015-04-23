		*****************************************************
		*         Symbolic Execution Debugger (SED)         *
		*   Example Symbolic Execution Engine Integration   *
		*****************************************************

This folder provides an example implementation showing how to integrate a 
symbolic execution engine into the Symbolic Execution Debugger.

Fore more details visit http://www.key-project.org/eclipse/SED
or contact Martin Hentschel (hentschel@cs.tu-darmstadt.de).


(1) Description
----------------
The Symbolic Execution Debugger extends the Eclipse Debug Platform
(http://www.eclipse.org/eclipse/debug/) with support for symbolic execution.

Different symbolic execution engines can be integrated by implementing
the extended debug model for symbolic execution
(http://www.key-project.org/eclipse/SED/index.html#ExtendedDebugModel).

The provided plug-ins are a good starting point for an own integration and
designed to explain the basic types and their responsibilities.


(2) Provided plug-ins
---------------------
- org.key_project.sed.example.core // Starts the symbolic execution engine and
                                      constructs the symbolic execution tree.
- org.key_project.sed.example.ui   // Provides the user interface integration 
                                      including launch short cut and controls
                                      to edit a launch configuration.


(3) Setup Development IDE
-------------------------
1. Start an Eclipse 3.7 or newer which contains the Plug-in Development 
   Environment (PDE) like the 'Eclipse Modeling Tools' package.

2. Install the Symbolic Execution Debugger (SED) via an update-site listed at
   http://www.key-project.org/download/

3. Import the Eclipse projects 'org.key_project.sed.example.core' and
   'org.key_project.sed.example.ui' via the import wizard.


(4) Launch the Example
----------------------
1. Select context menu item 'Run As, Eclipse Application' of the project
   'org.key_project.sed.example.ui'.

2. Select main menu item 'SED Example, Launch Example' in the launched Eclipse 
   Application.