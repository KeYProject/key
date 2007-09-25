class A {

  public  byte m(long i) { return 2; }

  private int m(int i) { return 1; }

  static int callM() {
     A a = new A();
     return a.m(1);
  }

  static int callMviaB() {
     return B.callM();
  }

}

class B {

  static int callM() {
     A a = new A();
     return a.m(1);
  }
}

public class Main {

  public static void main(){
      System.out.println(A.callM());
      System.out.println(B.callM());
      System.out.println(A.callMviaB());
  }
}
  

