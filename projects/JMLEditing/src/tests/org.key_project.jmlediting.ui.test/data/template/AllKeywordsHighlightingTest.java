package org.key_project.jmlediting.ui.test.highlighting;

/*@
  @ public invariant numCalls >= 0;
  @ protected invariant numCalls >= handledCalls;
  @ private invariant needsRefresh <==> numCalls != handlesCalls;
  @*/
public abstract class AllKeywordsHighlightingTest {
   
   private /*@ spec_public */ int numCalls;
   private /*@ spec_protected*/ int handledCalls;
   private boolean needsRefresh;
   
   /*@
     @ public normal_behavior
     @   ensures numCalls == 0;
     @*/
   public AllKeywordsHighlightingTest() {
      numCalls = 0;
      handledCalls = 0;
      needsRefresh = !isFresh();
   }
   
   /*@
     @ public normal_behavior
     @   requires number > 0;
     @   ensures this.numCalls == \old(this.nunCalls); 
     @ 
     @ also
     @ 
     @ public exceptional_behavior
     @   requires number <= 0;
     @*/
   public void callMe(int number) {
      int oldNumCalls = numCalls;
      /*@
        @ loop_invariant oldNumCalls + number == this.numCalls + number -i;
        @ decreasing  number -i;
        @*/
      for (int i = 0; i < number; i++) {
         increaseCalls();
      }
      
   }
   
   /*@
     @ private behavior
     @   ensures this.numCalls == \old(numCalls) +1;
     @*/
   private void increaseCalls() {
      this.numCalls ++;
   }
   
   /*@
     @ protected normal_behavior
     @   requires numCalls > handledCalls;
     @   requires same;
     @   ensures \old(handledCalls) == 1 + this.handledCalls;
     @*/
   protected abstract void handleCall();
   
   /*@
     @ public normal_behavior
     @   requires (\forall int i; 0<= i && i < data.length; data[i] >= 0);
     @   ensures \result <==> (\exists int i; 0 <= i && i <data.length; data[i] == this.numCalls);
     @   assignable \nothing;
     @*/
   public boolean containsNumCalls(int[] data) {
      for (int i : data) {
         if (i == this.numCalls)
            return true;
      }
      return false;
   }
   
   /*@
     @ ensures \result <==> this.numCalls == this.handledCalls;
     @*/
   protected /*@ pure */ boolean isFresh() {
      return this.numCalls == this.handledCalls;
   }
   
   /*@
     @ protected normal_behavior
     @   accessible \everything;
     @   requires (\num_of int i; i > 0 && i < 10; i) == 8;
     @   requires (\max non_null String s; s.length < 10; s.length) == 10;
     @   requires (\min nullable String s; s == null ? -20 : s.length) == -20;
     @   ensures (\product int i;;i) == 0;
     @   ensures (\sum long l ; -5<l && l <5; l) == 0;
     @   
     @ also
     @ 
     @ protected normal_behavior
     @   requires \not_specified;   
     @   requires \same;
     @*/
   protected /*@helper*/ void tryBreakEverything() {
      
   }

}
