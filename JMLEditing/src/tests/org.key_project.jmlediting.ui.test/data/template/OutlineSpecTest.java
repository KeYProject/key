package test;

public class OutlineSpecTest {
   
   public class clazz {
      //randome comment
      
      
      public void clazz1(){
         
      }
   }

   public int /*@ spec_public@*/ balance = 0;
   
   
   public int a = 0;
   
   public int/*@ pure @*/ amount() {
      /*@ behavior
       @   random comment in method
       @
       */
      return i;
   }
   
   public void a(){
      
   }

   /*@ behavior
    @ 
    @
    */
   public int /*@ pure nullable @*/ testMulti (){
      return 1;
   }


   public int /*@ spec_protected nullable@*/ balance2 = 0;
   
   /*@ behavior
   @ 
   @
   */
   public void a(){
      new clazz(){
         
      }
      
   }
   //ohne comment
   public void acsda(){
      new clazz(){
         
      }
      
   }
   
   
   public clazz /*@nullable@*/ z = new clazz(){
      
   };
 
   public clazz  zz = new clazz(){
      
   };
   
   
}
