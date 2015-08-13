package test;

public class OutlineSpecTest {

   public int /*@ spec_public@*/ balance = 0;
   
   
   public int a = 0;
   
   public int/*@ pure @*/ amount() {
      /*@ behavior
       *@   random comment in method
       *@
       */
      return i;
   }
   
   public int /*@ pure nullable @*/ testMulti (){
      return 1;
   }


   public int /*@ spec_protected nullable@*/ balance2 = 0;

   
}
