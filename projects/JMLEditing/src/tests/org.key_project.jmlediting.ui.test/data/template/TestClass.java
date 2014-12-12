package test;

//offset out of Class (4:1)

/**
 * 
 * normal JDoc Comment  (7:24)
 *
 */
public class TestClass {
   /*
    * some casual Java Comment  (12:32)
    */
   /*@
    @ JML COMMENT  (15:19)
    */
   //offset in Class (18:4)
   
   public static void main(String[] args) throws Exception {
      //offset in String: (21:36)
      System.out.println("//@Hello  World!@//"); //just a normal Comment with a "String"  (21:90)
      //offset in Method: (23:7)
      
      //@ and a jml comment  (23:29)
      char c= 'a';
   }
}
