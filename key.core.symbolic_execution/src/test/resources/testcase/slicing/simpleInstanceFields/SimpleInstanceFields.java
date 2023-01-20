
public class SimpleInstanceFields {
   private int x;
   private int y;
   private int z;
   private int result;
   
   /*@ normal_behavior
     @ requires \invariant_for(obj);
     @ ensures true;
     @*/
   public static int main(SimpleInstanceFields obj) {
      obj.x = 40;
      obj.y = 2;
      obj.z = -4711;
      obj.result = obj.x + obj.y;
      return obj.result;
   }
}
