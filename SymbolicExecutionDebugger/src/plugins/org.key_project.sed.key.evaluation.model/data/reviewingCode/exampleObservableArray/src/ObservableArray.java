/**
 * An observable array which delegates all actions to an array.
 * @see ArrayListener
 * @see ArrayEvent
 */
public class ObservableArray {
   /**
    * The array to which all actions are delegated.
    * <p>
    * The array is never {@code null},
    * but the value at an array index might be {@code null}.
    */
   /*@ invariant array != null;
     @*/
   private final /*@ nullable @*/ Object[] array;
   
   /**
    * The optional available {@link ArrayListener} instances.
    * <p>
    * If no listeners are available, array {@link arrayListeners} might be {@code null} or empty.
    * Also the value at an array index might be {@code null}.
    */
   private /*@ nullable @*/ ArrayListener[] arrayListeners;
   
   /**
    * Constructs an {@link ObservableArray} taking ownership of the given array.
    * <p>
    * In case that the given array is {@code null} an 
    * {@link IllegalArgumentException} will be thrown.
    * @param array The array to which all actions are delegated.
    * @throws IllegalArgumentException if the given array is {@code null}.
    */
   public ObservableArray(Object[] array) {
      if (array == null) {
         throw new IllegalArgumentException("Array is null.");
      }
      this.array = array;
      this.arrayListeners = null;
   }

   /**
    * Sets the value at index to the given {@link Object} and
    * informs all at call time available {@link ArrayListener} about the change.
    * <p>
    * The change is represented as {@link ArrayEvent} which contains all
    * details about the performed modification.
    * @param index The index in the array to modify.
    * @param element The element to set at the given index which might be {@code null}.
    */
   public void set(int index, Object element) {
      array[index] = element;
      fireElementChanged(new ArrayEvent(this, index, element));
   }

   /**
    * Informs all at call time available {@link ArrayListener} about an array change
    * by calling {@link ArrayListener#elementChanged(ArrayEvent)}.
    * @param e The {@link ArrayEvent} to be passed to the {@link ArrayListener} instances.
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
    * Sets the available {@link ArrayListener} instances.
    * @param arrayListeners The new {@link ArrayListener} instances which might be {@code null}.
    */
   public void setArrayListeners(ArrayListener[] arrayListeners) {
      this.arrayListeners = arrayListeners;
   }
}