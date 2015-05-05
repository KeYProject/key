public class SuperConstructorCall {
   public SuperConstructorCall() {
   }
}

class SuperConstructorB extends SuperConstructorCall {
   public SuperConstructorB(){
      super();
   }
}

