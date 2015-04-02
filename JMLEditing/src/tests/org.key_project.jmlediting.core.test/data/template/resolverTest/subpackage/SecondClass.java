package test.subpackage;

import test.SuperClass;

public class SecondClass extends SuperClass {
   public String publicSecondClass;
   private int privateSecondClass;
   protected float protectedSecondClass;
   long packageSecondClass;

   public class NestedInSecondClass {
      public String publicNestedInSecondClass;
      private int privateNestedInSecondClass;
      protected long protectedNestedInSecondClass;
      long packageNestedInSecondClass;
      
   }
}
