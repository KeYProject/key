
public class NestedInstanceAccess {
   /*@ normal_behavior
     @ requires \invariant_for(first);
     @ requires \invariant_for(first.b);
     @ requires \invariant_for(second);
     @ requires \invariant_for(second.b);
     @ ensures true;
     @*/
   public int main(A first, A second) {
      first.b.value = 2;
      second.b.value = 3;
      int subResult = subMain(first, second);
      return subResult;
   }
   
   public int subMain(A first, A second) {
      int fbv = first.b.value;
      int sbv = second.b.value;
      return fbv + sbv;
   }
   
   private static class A {
      public B b;
   }
   
   private static class B {
      public int value;
   }
}
