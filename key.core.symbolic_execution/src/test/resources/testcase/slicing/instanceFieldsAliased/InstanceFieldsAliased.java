
public class InstanceFieldsAliased {
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
   public static int main(InstanceFieldsAliased o1,
                          InstanceFieldsAliased o2) {
      o2.container.x = 40;
      Container c = o1.container;
      o2.container = c;
      c.y = 2;
      o1.container.z = -4711;
      o2.container.result = o2.container.x + o2.container.y;
      return c.result;
   }
   
   private static class Container {
      private int x;
      private int y;
      private int z;
      private int result;
   }
}
