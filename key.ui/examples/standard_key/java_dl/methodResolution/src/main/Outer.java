package main;

public class Outer {
    public byte m(long i) { return 2; }

    private int m(int i) { return 1; }

    public static int callM() {
        Outer a = new Outer();
        return a.m(1);
    }

    public static int callMviaB() {
        return B.callM();
    }

    final class B {
        public static int callM() {
            Outer a = new Outer();
            return a.m(1);
        }
    }
}
