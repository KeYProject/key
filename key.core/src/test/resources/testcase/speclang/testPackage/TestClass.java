package testPackage;

// The former class-level `/*@ spec_java_math @*/` pragma was removed: JMLtk does
// not accept standalone spec-math-mode comments (it only knows code_*_math
// modifiers). Tests that need JAVA spec math set SpecMathMode.JAVA explicitly.
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

