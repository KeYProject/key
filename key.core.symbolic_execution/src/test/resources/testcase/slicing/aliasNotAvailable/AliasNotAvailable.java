public class AliasNotAvailable {
   private Container container;
   
   /*@ normal_behavior
     @ requires o1 != null && \invariant_for(o1);
     @ requires o1.container != null && \invariant_for(o1.container);
     @ requires o2 != null && \invariant_for(o2);
     @ requires o2.container != null && \invariant_for(o2.container);
     @ requires o1 != 02;
     @ requires o1.container != o2.container;
     @ ensures true;
     @*/
   public static int main(AliasNotAvailable o1,
                          AliasNotAvailable o2) {
      o2.container = o1.container;
      o2.container.x = 40;
      o1.container.y = 2;
      o1.container.z = -4711;
      Container c = o1.container;
      c.result = c.x + c.y;
      return c.result;
   }
   
   private static class Container {
      private int x;
      private int y;
      private int z;
      private int result;
   }
}
