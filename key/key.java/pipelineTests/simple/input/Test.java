public class Test {
    public static int abc;
    static {
        abc = 1+1; // should be resolved to 2
    }

    public int memberVar;
    { memberVar = 42; }
}

public class SubClass extends Test {
    public int memberVar;
    { memberVar = 41; }
}