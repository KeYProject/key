
public class GlobalVariablesOnTrue {

   private static int x_global;

   private static void doSomething() {
      x_global=17;
      main(x_global);
      x_global=-1;
      main(x_global);
      
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
