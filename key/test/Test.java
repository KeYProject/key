class Test {
    public static final int CONST = 42;
    //@ensures \result == 42;
    public int foo() {return CONST;}
}