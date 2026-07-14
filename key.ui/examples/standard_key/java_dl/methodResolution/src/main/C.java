package main;
public final class C extends A {

    public static int callM() {
        C a = new C();
        byte val = 1;
        return a.m(val);
    }
}
