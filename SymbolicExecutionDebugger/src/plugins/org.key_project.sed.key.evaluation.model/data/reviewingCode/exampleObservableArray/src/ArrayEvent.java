/**
 * An event caused by an {@link ObservableArray} and observed via
 * {@link ArrayListener} instances.
 * @see ObservableArray
 * @see ArrayListener
 */
public class ArrayEvent {
   /**
    * The {@link ObservableArray} on which the event occurred.
    */
   private final ObservableArray source;
	
   /**
    * The modified index in the array.
    */
   private final int index;
   
   /**
    * The new element.
    */
   private final Object newElement;

   /**
    * Constructor.
    * @param source The {@link ObservableArray} on which the event occurred.
    * @param index The modified index in the array.
    * @param newElement The new element.
    */
   public ArrayEvent(ObservableArray source, int index, Object newElement) {
      this.source = source;
      this.index = index;
      this.newElement = newElement;
   }

   /**
    * Returns the {@link ObservableArray} on which the event occurred.
    * @return The {@link ObservableArray} on which the event occurred.
    */
   public ObservableArray getSource() {
      return source;
   }

   /**
    * Returns the modified index in the array.
    * @return The modified index in the array.
    */
   public int getIndex() {
      return index;
   }

   /**
    * Returns the new element.
    * @return The new element.
    */
   public Object getNewElement() {
      return newElement;
   }
}
