package main;

public class A {

  public byte m(long i) { return 2; }

  protected int m(int i) { return 3; }

  private int m(byte i) { return 1; }

    public static int callM() {
     A a = new A();
     byte val = 1;
     return a.m(val);
  }

  public static int callMviaB() {
     return B.callM();
  }

}

