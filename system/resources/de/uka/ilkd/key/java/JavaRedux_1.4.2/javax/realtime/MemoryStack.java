package javax.realtime;

public class MemoryStack{

    private ScopedMemory[] _stack;

    //@ public static invariant EMPTY_STACK!=null && EMPTY_STACK.size()==0;
    private static MemoryStack EMPTY_STACK;

    /*@ public invariant _stack!=null;
      @*/

    /*@ public invariant (\forall int i,j; 0<=i && i<_stack.length && 
      @    i<j && j<_stack.length; _stack[i]!=null && _stack[i]!=_stack[j] &&
      @    \outerScope(_stack[i], _stack[j]));
      @*/

    /*@ public invariant (\forall int i; 1<=i && i<_stack.length; 
      @    _stack[i].parent == _stack[i-1]);
      @*/

    /* public normal_behavior
      @  working_space 0;
      @  ensures \fresh(\result) && \result._stack.length==_stack.length+1 &&
      @          \result._stack[_stack.length]==m && (\forall int i; i>=0 &&
      @            i<_stack.length; \result._stack[i]==_stack[i]);
      @*/
    public MemoryStack push(ScopedMemory m);

    /*@ public normal_behavior
      @  ensures \result==(\exists int i; i>=0 && i<_stack.length; _stack[i]==m);
      @ also public normal_behavior
      @  ensures \result == \outerScope(m, _stack[_stack.length-1]);
      @*/
    public /*@pure@*/ boolean contains(ScopedMemory m);

    /*@ public normal_behavior
      @  ensures \result==((o instanceof MemoryStack) && 
      @      _stack.length == ((MemoryStack) o)._stack.length &&
      @      (\forall int i; 0<=i && i<_stack.length; 
      @       _stack[i]==((MemoryStack) o)._stack[i]));
      @*/
    public /*@pure@*/ boolean equals(Object o);

    /*@ public normal_behavior
      @  ensures \result==_stack[i];
      @*/
    public /*@pure@*/ ScopedMemory get(int i);

    /*@ public normal_behavior
      @  ensures \result==_stack.length;
      @*/ 
    public /*@pure@*/ int size(){return _stack.length;}

    /*@ public normal_behavior
      @  ensures \result==_stack[_stack.length-1];
      @*/
    public /*@pure@*/ ScopedMemory top();
}
