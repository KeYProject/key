public class superMethodA {
   public void testMethodSuper(){
   }
}

class SuperMethodB extends superMethodA {
   public void testMethod(){
      testMethodSuper();
   }
}
