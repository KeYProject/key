/**
 * Effective Java 2nd Edition, Page 24 (PDF Page 47)
 */
public final class Stack {
   /**
    * The elements on the stack.
    * The array is never {@code null}.
    */
   private final /*@ non_null @*/ Object[] elements;
   
   /**
    * The current size of the stack 
    * which is always a valid array index in {@link #elements}.
    */
   /*@ invariant size >= 0 && size <= elements.length;
     @*/
   private int size = 0;
   
   /**
    * Constructor.
    * @param maximalSize The maximal stack size.
    */
   public Stack(int maximalSize) {
      elements = new Object[maximalSize];
   }
   
   /**
    * Private constructor for cloning purpose.
    * @param elements The elements on the stack.
    * @param size The current size of the stack.
    */
   private Stack(Object[] elements, int size) {
      assert elements != null;
      assert size >= 0 && size <= elements.length;
      this.elements = elements; // TODO: Aliasing problem
      this.size = size;
   }
   
   /**
    * Creates an independent copy with the same content.
    * @return The created copy.
    */
   public Stack clone() {
      return new Stack(elements, size);
   }

   /**
    * Adds the given {@link Object} to the stack.
    * <p>
    * In case that the maximal stack length has reached,
    * an {@link IllegalStateException} will be thrown.
    * @param e The {@link Object} to add.
    */
   public void push(Object e) {
      if (size < elements.length) {
         elements[size++] = e; // TODO: Memory leak
      }
      else {
         throw new IllegalStateException("Stack is full.");
      }
   }

   /**
    * Returns and removes the top entry from the stack.
    * <p>
    * In case that the stack is empty, 
    * an {@link IllegalStateException} will be thrown.
    * @return The top stack entry which was removed from the stack.
    */
   public Object pop() {
      if (size >= 1) {
         return elements[--size];
      }
      else {
         throw new IllegalStateException("Stack is empty.");
      }
   }
}
