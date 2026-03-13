
This directory contains test cases for the class 
`de.uka.ilkd.key.nparser.KeYParserExceptionTest`.

To add a test case add your single .key file that contains an error
that should be presented to the user (like syntax error, unresolved
names, ...)

The first lines of the file may contain meta data on what to
expect from the exception. Meta data are key-value pairs like

    // <key>: <value>

The following keys are supported

| Key              | Description |
| ---              | --- |
| `noException`    | This particular file must **not** throw an exception. Default: false |
| `exceptionClass` | Either a fully qualified class name or a short classname (w/o package prefix) of the actual type of the exception. Optional. |
| `msgContains`    | A string which occur somewhere in the exception message (obtained via {@link Exception#getMessage()}). Optional |
| `msgMatches`     | A regular expression that must match the exception message (obtained via {@link Exception#getMessage()}). Optional |
| `msgIs`          | A string to which the exception message (obtained via {@link Exception#getMessage()}) must be equal. Optional |
| `position`       | A tuple in form `line`/`column` describing the position within this file. Both line and column are 1-based. It is also checked that the URL of the location points to the file under test. Optional |
| `ignore`         | Ignore this test case if set to true. Default is false. |
| `broken`         | If broken tests are disabled, ignore this test case if set to true. Indicates that this needs to be fixed! Default is false. |
| `verbose`        | Logs the stacktrace if set to true. Default is false. |
| `checkScript`    | Experimental: Provide a piece of java (script) code that must return true to make the test succeed. You may use the variable 'env' containing the parsed KeYEnvironment. |
\@author Mattias Ulbrich

