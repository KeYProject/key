package javax.realtime;

public class MemoryStack{

    private ScopedMemory[] stack;

    //@ public static invariant EMPTY_STACK!=null && EMPTY_STACK.size()==0;
    private static MemoryStack EMPTY_STACK;

    /*@ public invariant stack!=null;
      @*/

    /*@ public invariant (\forall int i,j; 0<=i && i<stack.length && 
      @    i<j && j<stack.length; stack[i]!=null && stack[i]!=stack[j] &&
      @    outerScope(stack[i], stack[j]));
      @*/

    /*@ public invariant (\forall int i; 1<=i && i<stack.length; 
      @    stack[i].parent == stack[i-1]);
      @*/

    /*@ public normal_behavior
      @  working_space 0;
      @  ensures \fresh(\result) && \result.stack.length==stack.length+1 &&
      @          \result.stack[stack.length]==m && (\forall int i; i>=0 &&
      @            i<stack.length; \result.stack[i]==stack[i]);
      @*/
    public MemoryStack push(ScopedMemory m);

    /*@ public normal_behavior
      @  ensures \result==(\exists int i; i>=0 && i<stack.length; stack[i]==m);
      @ also public normal_behavior
      @  ensures \result == outerScope(m, stack[stack.length-1]);
      @*/
    public /*@pure@*/ boolean contains(ScopedMemory m);

    /*@ public normal_behavior
      @  ensures \result==((o instanceof MemoryStack) && 
      @      stack.length == ((MemoryStack) o).stack.length &&
      @      (\forall int i; 0<=i && i<stack.length; 
      @       stack[i]==((MemoryStack) o).stack[i]));
      @*/
    public /*@pure@*/ boolean equals(Object o);

    /*@ public normal_behavior
      @  ensures \result==stack[i];
      @*/
    public /*@pure@*/ ScopedMemory get(int i);

    /*@ public normal_behavior
      @  ensures \result==stack.length;
      @*/ 
    public /*@pure@*/ int size(){return stack.length;}

    /*@ public normal_behavior
      @  ensures \result==stack[stack.length-1];
      @*/
    public /*@pure@*/ ScopedMemory top();
}
