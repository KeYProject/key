public class SuperA {
  public int a = 3;
  public int b = a + 1;
  public int c;

  { a ++; }
  
  public SuperA() {
  } 

  public SuperA(int offset) {
     this();
     a+=offset;
  }
}
