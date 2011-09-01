class ExampleJavaLangSystem {

    //@ invariant System.out != null;

    //@ normal_behavior
    //@ ensures true;
    /*@ pure @*/ void helloWorld () {
        java.io.PrintStream out = System.out;
        out.println("Hello World");
    }

    //@ normal_behavior
    //@ ensures true;
    /*@ pure @*/ void print () {
        java.io.PrintStream out = System.out;
        out.println(false);
        out.println(42);
        out.println(this);
    }

    //@ diverges true;
    //@ ensures false;
    /*@ pure @*/ void exit () {
	System.exit(42);
    }
}
