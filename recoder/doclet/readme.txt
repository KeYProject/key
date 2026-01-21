Files modified (as before marked with //new):
Standard.java
ClassWriter.java
HtmlStandardWriter.java
ConfigurationStandard.java
resources/standard.properties  // added option entry

plus package specification removed from the rest.

No update needed for the remaining classes.
New -linksource option added.

To make the patch work, you might have to force javadoc to use the
correct local path:

javadoc -docletpath <path to doclet> -doclet Standard -sourcepath <path to sources> -linksources <packages or classes>


Not done:
- no proper error messages if sourcepath is missing with active -linksources



Second feature:
Abstract classes in the class listing of a package are printed in italics,
like interfaces. This conforms to UML conventions and carries important
information.
This also should extend to the all classes index.

One could even consider extending this to ANY class and method link
in summaries that are abstract (or interfaces or members of interfaces).
