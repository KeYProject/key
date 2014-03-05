All files in this subdirectory have been created using the "Stubmaker" tool
(de.uka.ilkd.stubmaker) and edited by hand.

The generated classed correspond to the API provided by SUN's JDK version 1.6.
The JAR file to extract from is named rt.jar and can typically be found at
/usr/lib/jvm/java-6-sun-1.6.0.26/jre/lib/rt.jar

In addition some stubs of JUnit classes are included as far as they are needed
for test generation.  

The stubs are java files w/o method or constructor bodies so that they 
cannot accidently be executed symbolically.
The set is closed, i.e. all references to classes outside the set have been
removed. This is why the some fields, methods or inheritances have not been
included in these files.

The following command line arguments where used:
   -expand -hide JAVALANG.TXT rt.jar
