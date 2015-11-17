import java.util.EventObject;

/**
 * An event caused by an {@link ObservableList} and observed via
 * {@link ListListener} instances.
 * @see ObservableList
 * @see ListListener
 */
public class ListEvent extends EventObject {
   /**
    * The element.
    */
   private Object element;

   /**
    * Constructor.
    * @param source The {@link ObservableList} on which the event occurred.
    * @param element The element.
    */
   public ListEvent(ObservableList source, Object element) {
      super(source);
      this.element = element;
   }

   /**
    * Returns the element.
    * @return The element.
    */
   public Object getElement() {
      return element;
   }
}
