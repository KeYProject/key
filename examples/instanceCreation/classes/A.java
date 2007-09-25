public class A extends SuperA {
  public int d;
  public int e = 3;

  public A() {
  }

  public A(int offset) {
     super(offset);
     a = a + e;
  }

}