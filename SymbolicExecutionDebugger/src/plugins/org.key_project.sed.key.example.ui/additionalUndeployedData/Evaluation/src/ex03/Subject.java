package ex03;

public class Subject {
   private Observer[] observer;
   
   protected void fireUpdate() {
      if (observer != null) {
         int length = observer.length;
         /*@ loop_invariant i >= 0 && i <= length;
           @ decreasing length - i;
           @*/
         for (int i = 0; i < length; i++) {
            observer[i].update(this);
         }
      }
   }

   public Observer[] getObserver() {
      return observer;
   }

   public void setObserver(Observer[] observer) {
      if (observer != null) {
         for (Observer o : observer) {
            if (o == null) {
               throw new IllegalArgumentException("At least one Observer is null.");
            }
         }
      }
      this.observer = observer;
   }
}

interface Observer {
   /*@ normal_behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public void update(Subject source);
}
