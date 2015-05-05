public class InnerTypeTest {
   public static int main(A.InnerA obj) {
      return obj.value;
   }
}

class A {
   class InnerA {
      public int value;
   }
}