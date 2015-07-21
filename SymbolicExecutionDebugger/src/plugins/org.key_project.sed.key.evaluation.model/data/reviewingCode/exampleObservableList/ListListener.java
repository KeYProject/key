import java.util.EventListener;

/**
 * Allows to observe changes on an {@link ObservableList}.
 * @see ObservableList
 * @see ListEvent
 */
public interface ListListener extends EventListener {
   /**
    * Invoked when an element was added to the {@link ObservableList}.
    * <p>
    * Implementations require nothing and are allowed to change everything.
    * An implementation only guarantees that no {@link Exception} will be thrown.
    * @param e The {@link ListEvent} with all details.
    */
   /*@ normal_behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public void elementAdded(ListEvent e);
}
