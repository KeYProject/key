package ex03;

public class AbstractParser {
   private Callback callback;
   
   /*@ normal_behavior
     @ requires \invariant_for(callback);
     @ ensures true;
     @*/
   public final void parse() {
      if (callback != null) {
         callback.start(this);
         doParse();
         callback.end(this);
      }
   }
   
   /*@ normal_behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   protected void doParse() {
   }

   public Callback getCallback() {
      return callback;
   }

   public void setCallback(Callback callback) {
      this.callback = callback;
   }
}

interface Callback {
   /*@ normal_behavior
     @ requires source != null;
     @ ensures true;
     @ assignable \everything;
     @*/
   public void start(AbstractParser source);
   
   /*@ normal_behavior
     @ requires source != null;
     @ ensures true;
     @ assignable \everything;
     @*/
   public void end(AbstractParser source);
}