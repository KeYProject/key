
public class MethodsOnSatisfiable {

   private static int x_global;

   private static void doSomething() {
      if(x_global>=0){
         main(x_global);
      }else{
         main(x_global);
      }
   }

   private static int main(int x) {
      if (x >= 0) {
         return 42;
      }
      else {
         return -4711;
      }
   }
}
