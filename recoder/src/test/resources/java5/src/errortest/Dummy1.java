import static Dummy2.foo; // impossible to import from default package, see http://bugs.sun.com/bugdatabase/view_bug.do?bug_id=4989710

public class Dummy1 {
    void bar() {
        foo(); // should be an error, but recoder does not recognize this (yet?)
        
    	fooe(new c(),new c());  // tests absence of an error from recoder .75
    }
    
    void fooe( c v1, b v2 ) {
    }

    void fooe( b v1, c v2 ) {
    }

    // this one should be recognized.
    void fooe( c v1, c v2 ) {
    }
    
    abstract void bar2000(String x);
    
    // Test...
    void bar2001() { 
        // Test again...
        bar2000(/*attach*/ "Hello");
        String s = /*attach*/ "Hello again";
    }
}

class b { }
class c extends b { }

class PType implements Comparable<String> {
	public int compareTo(String x) {
		// this must fail!!!
		new PType().compareTo(new Object());
	}
}