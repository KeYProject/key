package test;


public class HoverTestClass {
   
   private int magicX;
   
   /*@
     @ normal_behavior
     @   assignable this.magicX;
     @   requires magic;
     @   ensures this.magicX = \old(this.magicX) +1;
     @*/
   public void doMagic(boolean magic) {
      if (magic) {
         this.magicX ++;
      } else {
         this.magicX = Math.random()*100;
      }
   }
   
   /*
    * behavior
    *   assignable \nothing;
    */
   // Oh, somebody forget the JML annotations here, do not expect an hover
   public void doNothing() {
      
   }
   
   private int requires;
   
   /*@
     @ exceptional_behavior
     @   assignable \nothing;
     @   ensures requires == \old(requires);
     @*/
   public void dontCallMe() {
      throw new Error("Dont call me");
   }
   

}
