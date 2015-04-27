public class superMethodCall {
   public void testMethod(){
   }
}

class SuperMethodB extends superMethodCall {
   public void testMethod(){
      super.testMethod();
   }
}
