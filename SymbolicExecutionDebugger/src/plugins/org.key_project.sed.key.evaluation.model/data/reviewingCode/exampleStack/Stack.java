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
    * which is always a valid array index in {@link #elements}
    * or the length of {@link #elements} if the stack is full.
    */
   /*@ invariant size >= 0 && size <= elements.length;
     @*/
   private int size = 0;
   
   /**
    * Constructor to create an empty stack with the specified maximal size.
    * @param maximalSize The maximal stack size.
    */
   public Stack(int maximalSize) {
      elements = new Object[maximalSize];
   }
   
   /**
    * Constructor for cloning purpose which creates an indepedent stack
    * with the content of the given {@link Stack}.
    * @param existingStack The existing {@link Stack} which provides the initial content.
    */
   public Stack(Stack existingStack) {
      this.elements = existingStack.elements; // TODO: Aliasing problem
      this.size = existingStack.size;
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
