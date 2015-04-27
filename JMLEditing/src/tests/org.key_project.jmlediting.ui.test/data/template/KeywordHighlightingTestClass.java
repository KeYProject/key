package test;

// ensures true;

/**
 * 
 * ensures true ;
 *
 */
public class TestClass {
   /*
    * ensures true;
    */
   /*@
     @ ensures true;
     @*/
   
   public static void main(String[] args) throws Exception {
      System.out.println("//@Hello  World!@//");
      ensures true;
      //@ ensures true;
   }
   public void a(){
      /**
       * requires ;
       */
      /*
       * requires ;
       */
      // requires ;
      int x;
      /*@
        @ requires ; 
        @*/
      int y;
      //@ requires ;
      requires ;
   }
   public void b(){
      /**
       * asdf ;
       */
      /*
       * asdf ;
       */
      // asdf ;
      /*@
        @ asdf ; 
        @*/
      //@ asdf ;
      asdf ;  
   }
}
