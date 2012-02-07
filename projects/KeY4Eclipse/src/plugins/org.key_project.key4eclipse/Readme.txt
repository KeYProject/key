This plug-in "org.key_project.key4eclipse" provides the KeY code
to all other plug-ins.

To use and deploy this plug-in the following modifications must be done in
every workspace:
- Checkout KeY repository
- Download KeY externals and extract them into any directory.
  (e.g. from http://www.key-project.org/download/releases/KeYExtLib-1.6.zip)
- Configure development IDE
  1. Open the preference dialog ("Window, Preferences...")
  2. Select preference page "General, Workspace, Linked Resources"
  3. Add the following path variables:
     - Name: key_lib
       Location: The directory that contains the KeY externals (antlr.jar, 
                 javacc.jar, junit.jar, objenesis.jar and recoderKey.jar). 
                 E.g.: D:\Forschung\Tools\KeY-External Libs
     - Name: key_rep 
       Location: The directory that contains the KeY repository 
                 (e.g. it contains the directory "system")
                 E.g.: D:\Forschung\GIT\KeY
  4. Refresh the project "org.key_project.key4eclipse".
  5. Execute "system/build.xml" as "Ant Build...".
     a) Switch to tab JRE
     b) Add the following VM arguments: -Xms512m -Xmx512m
     c) Switch to tab "Environment"
     d) Add variable "KEY_LIB" with the path to the KeY externals as value.
        E.g.: D:\Forschung\Tools\KeY-External Libs
     e) Execute it to generate KeY code and to make rules available at runtime.
- Configure build process
  1. Create file "org.key_project.sed.external.key/customTargets.properties"
     with the following key value pairs:
     - Name: key.rep
       Value: Path to the KeY repository (it contians folder "system")
     - Name: ext.dir
       Value: Path to the KeY external libraries (recoderKey.jar, ...)
     
     Example content:   
        key.rep=D:/Forschung/GIT/KeY
        ext.dir=D:/Forschung/Tools/KeY-External Libs

Important notice:
SWT and Swing runs both in his own UI thread. For synchronization it is
required to use Display#syncExec(Runnable) and SwingUtil#invokeAndWait(Runnable)
or Display#asyncExec(Runnable) and SwingUtil#invokeLater(Runnable). Keep
always in mind that a synchronous call is not possible from SWT or Swing thread.
In this case only an asynchronous method call is possible. If you don't
respect this knowledge Mac OS will cause deadlocks!
