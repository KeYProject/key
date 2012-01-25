This plug-in "org.key_project.key4eclipse" provides the KeY code
to all other plug-ins.

To use and deploy this plug-in the following modifications must be done in
every workspace:
- Checkout KeY repository
- Download KeY externals and extract them into any directory.
  (e.g. from http://www.key-project.org/download/releases/KeYExtLib-1.6.zip)
- Configure development IDE
  1. Open the properties of plug-in project "org.key_project.key4eclipse"
  2. Select properties page "Resource, Linked Resources"
  3. Set path in variable "KEY_REPOSITORY" to the directory that contains the 
     KeY repository (e.g. it contains the directory "system")
  4. Set path in variable "KEY_EXTERNALS" to the directory that contains the
     KeY externals (antlr.jar, javacc.jar, junit.jar, objenesis.jar and 
     recoderKey.jar)
  5. Refresh the project "org.key_project.key4eclipse".
  6. Execute "system/build.xml" as "Ant Build...".
     a) Switch to tab HRE
     b) Add the following VM arguments: -Xms512m -Xmx512m
     c) Switch to tab "Environment"
     d) Add variable "KEY_LIB" with the path to the KeY externals as value.
     e) Execute it to generate KeY code and to make rules available at runtime.
- Configure build process
  1. Open file "org.key_project.sed.external.key/customTargets.xml" with the
     "Ant Editor" or any other text editor.
  2. Set value of property "keyRepository" to the directory that contains the
     KeY repository (e.g. it contains the directory "system")
  3. Set value of property "ext.dir" to the directory that contains the
     KeY externals (antlr.jar, javacc.jar, junit.jar, objenesis.jar and 
     recoderKey.jar)
