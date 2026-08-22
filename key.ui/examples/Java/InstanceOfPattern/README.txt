example.name = Binding InstanceOf
example.path = Java 25
example.file = project.key
example.additionalFile.1 = src/InstanceOfPatternExample.java


Java 16+ Instanceof Pattern Matching Example
=============================================

This example demonstrates KeY's support for Java 16+ instanceof pattern matching,
which allows type checking and variable binding in a single expression.

Feature Overview
----------------
Traditional instanceof (pre-Java 16):
    if (obj instanceof String) {
        String s = (String) obj;
        return s.length();
    }

Pattern matching instanceof (Java 16+):
    if (obj instanceof String s) {
        // 's' is automatically bound as a String
        return s.length();
    }

What This Example Shows
-----------------------
1. Basic pattern matching (getStringLength method)
   - The pattern variable 's' is bound in the true branch
   
2. Negated instanceof (checkNotString method)
   - Pattern binding happens in the else branch, not the if branch
   - Demonstrates: if(!(x instanceof T e)) { ... } else { ... }
   
3. Multiple instanceof patterns (processNumber method)
   - Chained instanceof checks with different types
   
4. Pattern variables in complex expressions (compareIfBothStrings)
   - Multiple pattern variables bound in the same branch
   - Combined with && operator
   
5. Traditional vs pattern matching comparison (traditionalVsPattern)
   - Shows both styles work correctly together

Key Taclets
-----------
The following taclets in genericRules.key handle pattern matching:

- instanceof_pattern_if_split: Splits if-statements and binds the pattern variable
- instanceof_pattern_negated_if: Handles negated instanceof by swapping branches  
- instanceof_pattern_cast_elimination: Eliminates redundant casts after instanceof

Loading This Example
--------------------
1. Open KeY
2. Load the project.key file from this directory
3. Select a method to verify
4. Start symbolic execution

The instanceof pattern matching will be automatically handled during proof search.

Requirements
------------
- Java 16 or later (for compilation)
- KeY with instanceof pattern matching support

See Also
--------
- Java 16 Release Notes: https://openjdk.java.net/projects/jdk/16/
- JEP 394: Pattern Matching for instanceof
  https://openjdk.java.net/jeps/394
