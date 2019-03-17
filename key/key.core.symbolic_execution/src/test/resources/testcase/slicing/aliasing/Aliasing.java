
public class Aliasing {
   private int value;
   
   public static int main(Aliasing a, Aliasing b) {
      a.value = 2;
      b.value = 3;
      int resultValue = a.value + b.value;
      return resultValue;
   }
}
