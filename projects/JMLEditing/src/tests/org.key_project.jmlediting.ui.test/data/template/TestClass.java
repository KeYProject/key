package test;

/**
 * 
 * normal JDoc Comment  (5:24)
 *
 */
public class TestClass {
   /*
    * some casual Java Comment  (10:32)
    */
   /*@
    * JML COMMENT  (13:19)
    */
   public static void main(String[] args) throws Exception {
      //offset in String: (17:36)
      System.out.println("//@Hello  World!@//"); //just a normal Comment with a "String"  (17:90)
      //offset in normal Java: (19:7)
      
      //@ and a jml comment  (20:29)
   }
}
