
public class MethodHierarchyCallWithExceptionTest {
   /*@ requires true;
     @ ensures true;
     @*/
   public void main() {
      a();
   }
   
   public void a() {
      try {
         b();
      }
      catch (RuntimeException e) {
         int ae = -1;
      }
      int a1 = 1;
   }
   
   public void b() {
      c();
   }
   
   public void c() {
      throw new RuntimeException();
   }
}
