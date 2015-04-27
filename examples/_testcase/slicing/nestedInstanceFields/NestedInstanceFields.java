
public class NestedInstanceFields {
   private Container container;
   
   /*@ normal_behavior
     @ requires \invariant_for(obj);
     @ requires \invariant_for(obj.container);
     @ ensures true;
     @*/
   public static int main(NestedInstanceFields obj) {
      obj.container.x = 40;
      obj.container.y = 2;
      obj.container.z = -4711;
      obj.container.result = obj.container.x + obj.container.y;
      return obj.container.result;
   }
   
   private static class Container {
      private int x;
      private int y;
      private int z;
      private int result;
   }
}
