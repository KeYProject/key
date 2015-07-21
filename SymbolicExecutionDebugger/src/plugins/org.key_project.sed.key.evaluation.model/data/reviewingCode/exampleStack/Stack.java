/**
 * A stack which stores contained elements in an array.
 * <p>
 * A new element is added on top of the stack by {@link #push(Object)}
 * and the top element can be removed by {@link #pop()}.
 */
public final class Stack {
   /**
    * The elements on the stack.
    * The {@link Object} array is never {@code null} and all array indices
    * {@code >= size} are {@code null}.
    */
   /*@ invariant elements != null;
     @ invariant \typeof(elements) == \type(Object[]);
     @ invariant (\forall int i; i >= size && i < elements.length; elements[i] == null);
     @*/
   private final /*@ nullable @*/ Object[] elements;
   
   /**
    * The current size of the stack 
    * which is always a valid array index in {@link #elements}
    * or the length of {@link #elements} if the stack is full.
    */
   /*@ invariant size >= 0 && size <= elements.length;
     @*/
   private int size;
   
   /**
    * Constructor to create an empty stack with the specified maximal size.
    * @param maximalSize The maximal stack size.
    */
   public Stack(int maximalSize) {
      elements = new Object[size];
      size = 0;
   }
   
   /**
    * Constructor for cloning purpose which creates an independent stack
    * with the content of the given {@link Stack}.
    * @param existingStack The existing {@link Stack} which provides the initial content.
    */
   public Stack(Stack existingStack) {
      this.elements = existingStack.elements;
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
         elements[size++] = e;
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
