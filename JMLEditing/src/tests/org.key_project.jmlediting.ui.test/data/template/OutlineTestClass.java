package test;

//offset out of Class (4:1)

/**
 * 
 * normal JDoc Comment  (7:24)
 *
 */
public class TestClass {
   
   /*@
   @ invariant 4 = 4;
   @
   @*/
   
      
   //@ public invariant 4 = 4;
   
   //@ private invariant 4 = 4;
   
   //@ protected invariant 4 = 4;
   
   
   
   /*
    * some casual Java Comment  (12:32)
    */
   /*@
    * JML COMMENT  (15:19)
    */
   //offset in Class (18:4)
   
   public static void main(String[] args) throws Exception {
      //offset in String: (21:36)
      System.out.println("//@Hello  World!@//"); //just a normal Comment with a "String"  (21:90)
      //offset in Method: (23:7)
      int x;
      //@set s = "shit";
      //@ and a jml comment  (23:29)
      Char c= 'a';
   }
   
   //@invariant 1 == 1;
   // the normal nehavior
   //normal_behaviour comment above the behavior
  /*@ normal_behavior
   @  requires x > y;
   @*/
   public void a(){
      //public
      int x;
      
   }
   
   //just behavior
   /*@ behavior
   @ requires x > y;
   @*/
   public void ab(){
      //public
      
   }
   
   //@ ghost int a = 1;
   
   
   //and exceptional behavior
   
 /*@ exceptional_behavior
   @ requires x > y;
   @*/
   //test comment between mehtiod and jml
   public void acb(){
      //public
      
   }
   
   
   
   
   
   
   
   
   
   //test hat nix damit zu tun
   public void def() {
      
   }
   
   public void defe() {
      
   }
   
   //@ set a = "a";
   

}
