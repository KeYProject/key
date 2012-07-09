public class MethodBodyTest {
   public void emptyVoid() {
   }

   public void emptyVoidSingleLined() {}
   
   public void doSomething() {
      int x = 32;
   }
   
   public int returnInt() {return 42;}
   
   public int containsIf(int x) {
      if (x >= 0) {
         return x;
      }
      else return x * -1;
   }
}
