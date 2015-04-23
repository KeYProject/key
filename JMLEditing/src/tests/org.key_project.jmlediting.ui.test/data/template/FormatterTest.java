package org.key_project.jmlediting.ui.test.formatter;

public //@helper
class FormatterTest {
   
   private 
/*@spec_public*/ class 
         Hello {
      
   }
   
   /*@
     @ public normal_behavior
     @   ensures funny;
     @   requires nonsense;
     @*/
   public
//@pure
   void /*@ */ ensures (Object o)
    // Wrong comments should be changed, too
{
      /*@
         @ invariant hello;
@ decreasing me;
        @*/
      for         (int
   i = 0; i < 3; 
            i++) {
         
}
   }

}
