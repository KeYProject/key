example.name = Record Patterns
example.path = Java 25
example.file = Sum.key
example.additionalFile.1 = src/RecordPatternExample.java

Java 21+ Record Patterns Example
================================

A record pattern matches a record value and deconstructs it into its components in a
single expression:

    if (obj instanceof Point(int x, int y)) {
        return x + y;
    }

The example shows plain record patterns (sum), nested record patterns (nested),
a conditional component pattern (conditional), a record pattern inside a
compound assignment (compound), and the null-matching rule for unconditional
component patterns (nullMatching).

Open project.key in the GUI to choose one of the contracts.
