
/**
 * An observable array which delegates all actions to a base array.
 * @see ArrayListener
 * @see ArrayEvent
 */
public class ObservableArray {
   /**
    * The base array to which all actions are delegated.
    * <p>
    * The base array is never {@code null}.
    */
   private final /*@ non_null @*/ Object[] array;
   
   /**
    * The optional available {@link ArrayListener}.
    * <p>
    * If no listeners are available the array might be {@code null} or empty.
    */
   private /*@ nullable @*/ ArrayListener[] arrayListeners;
   
   /**
    * Constructor.
    * @param array The base array to which all actions are delegated.
    */
   public ObservableArray(Object[] array) {
      if (array == null) {
         throw new IllegalArgumentException("Base array is null.");
      }
      this.array = array;
   }

   /**
    * Sets the value at index to the given {@link Object}.
    * @param index The index in the array to modify.
    * @param element The element to set at the given index.
    */
   public void set(int index, Object element) {
      array[index] = element;
      fireElementChanged(new ArrayEvent(this, index, element));
   }

   /**
    * Informs all available {@link ArrayListener} about an array change
    * by calling {@link ArrayListener#elementChanged(ArrayEvent)}.
    * @param e The {@link ArrayEvent} containing all event details.
    */
   private void fireElementChanged(ArrayEvent e) {
      if (arrayListeners != null) {
         /*@ loop_invariant i >= 0 && i <= arrayListeners.length;
           @ decreasing arrayListeners.length - i;
           @ assignable \everything;
           @*/
         for (int i = 0; i < arrayListeners.length; i++) {
            if (arrayListeners[i] != null) {
               arrayListeners[i].elementChanged(e);
            }
         }
      }
   }

   /**
    * Sets the available {@link ArrayListener}.
    * @param arrayListeners The new {@link ArrayListener}.
    */
   public void setArrayListeners(ArrayListener[] arrayListeners) {
      this.arrayListeners = arrayListeners;
   }
}
