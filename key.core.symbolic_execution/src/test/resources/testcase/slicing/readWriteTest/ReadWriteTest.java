
public class ReadWriteTest {
   public static int staticInt;
   
   public int instanceInt;
   
   public int main(int paramInt) {
      int localInt = 2;
      int resultInt = localInt + paramInt + staticInt + instanceInt;
      return resultInt;
   }
   
   public static int functionTest(int paramInt) {
      int localInt = 2;
      int resultValue = magic() + paramInt + localInt;
      return resultValue;
   }
   
   public static int magic() {
      return 42;
   }
}
