
public class LocalVariablesTest {
   public static int main(int y) {
      int main = y - 2;
      int subResult = sub(main);
      return subResult;
   }
   
   public static int sub(int x) {
      int sub = x + 2;
      return sub;
   }
}
