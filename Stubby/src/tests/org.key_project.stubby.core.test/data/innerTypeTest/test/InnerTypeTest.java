public class InnerTypeTest {
   public static int main(InnerA obj) {
      return obj.value;
   }
}

class A {
   class InnerA {
      public int value;
   }
}