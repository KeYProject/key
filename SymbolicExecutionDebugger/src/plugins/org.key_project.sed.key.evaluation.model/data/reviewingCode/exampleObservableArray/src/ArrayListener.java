/**
 * Allows to observe changes on an {@link ObservableArray}.
 * @see ObservableArray
 * @see ArrayEvent
 */
public interface ArrayListener {
   /**
    * Invoked when the element at an array index has changed.
    * <p>
    * Implementations require nothing and are allowed to change everything.
    * An implementation only guarantees that no {@link Exception} will be thrown.
    * @param e The {@link ArrayEvent} with all details.
    */
   /*@ normal_behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public /*@ helper @*/ void elementChanged(ArrayEvent e);
}
