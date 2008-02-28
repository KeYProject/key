package testPackage;

public class TestClass {

    byte b;
    short s;
    int i;
    long l;

    TestClass[] array;

    public static TestClass instance = new TestClass();

    public int getOne() {
        return 1;
    }

    public int m(int a) {
        return 2;
    }

    public int m(long a) {
        return 3;
    }

    public static int staticMethod() {
        return 4;
    }

}

