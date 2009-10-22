final class LinkedList implements List {
        
    private /*@nullable@*/ Node first;
    private /*@nullable@*/ Node last;
    private int size;
    
    //@ represents footprint <- first, last, size, \reachLocs(first.next, first);
    
    /*@ invariant size == 0 && first == null && last == null
      @            || size > 0
      @               && first != null 
      @               && last != null 
      @               && last.next == null
      @               && \reach(first.next, first, last, size - 1);
      @*/
   
    
    /*@ normal_behaviour
      @   ensures size() == 0;
      @   ensures \fresh(footprint);
      @*/
    public /*@pure@*/ LinkedList() {
    }
    

    public void add(Object o) {
	Node node = new Node();
	node.data = o;
	if(size == 0) {
	    first = node;
	    last = node;
	} else {
	    last.next = node;
	    last = node;
	}
	size++;
    }

    
    public Object get(int index) {
	if(index < 0 || size <= index) {
	    throw new IndexOutOfBoundsException();
	}
	
	Node node = first;
	/*@ loop_invariant 0 <= i && i <= index && \reach(first.next, first, node, i);
	  @ assignable \nothing;
	  @*/
	for(int i = 0; i < index; i++) {
	    node = node.next;
	}
	
	return node.data;
    }
    
    
    public ListIterator iterator() {
	return null;//TODO
    }
    
    
    public int size() {
	return size;
    }
    
    
    public boolean contains(Object o) {
	if(size == 0) {
	    return false;
	}
	
	Node node = first;
	/*@ loop_invariant 0 <= i && i < size && \reach(first.next, first, node, i)
	  @   && (\forall int x; 0 <= x && x < i; get(x) != o);
	  @ assignable \nothing;
	  @*/
	for(int i = 0; i < size - 1; i++) {
	    if(node.data == o) {
		return true;
	    }
	    node = node.next;
	}
	
	return node.data == o;
    }
    
    
    //interactive proofs:
    //-footprint (apply reachDependenciesChangeHeapAtLocs)
    //-<inv> (apply reachDependenciesChangeHeapAtLocs)
    
    //not yet verified: 
    //-add
    //-contains
}
