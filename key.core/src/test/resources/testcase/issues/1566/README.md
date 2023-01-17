https://git.key-project.org/key/key/-/issues/1566

## Description

Amongst others, the term `o.f@heap + 1` is parsed incorrectly

## Reproducible
  
always

### Steps to reproduce 

Create A.java:
````
class A { int f; }
````

Create a.key (in same directory):
````
\javaSource ".";

\programVariables { A that; }

\problem { that.f@heap + 1 = 1 + that.f@heap }
````

Load it. KeY fails.

This file can be loaded into %"v2.8.0" however.

### Additional information

Another problem is that the error message is pretty broken and does not allow to browse the guilty source code:
`Could not build term on: heap+1/tmp/k/a.key:6:18`

---

* Commit: bee2f7f582f39c914b5f11725aa1eb115233fde8, master at the time