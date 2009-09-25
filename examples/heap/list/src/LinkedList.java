//not yet verifiable
final class LinkedList implements List {
        
    private /*@nullable@*/ Node first;
    private /*@nullable@*/ Node last;
    
    //@ represents footprint <- first, last, \reachLocs(first.next, first);
    
    /*@ invariant first == null && last == null
      @            || first != null 
      @               && last != null 
      @               && last.next == null
      @               && \reach(first.next, first, last);
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
	if(first == null) {
	    first = node;
	    last = node;
	} else {
	    last.next = node;
	    last = node;
	}
    }

    
    public Object get(int index) {
	if(index < 0 || first == null) {
	    throw new IndexOutOfBoundsException();
	}
	
	Node node = first;
	/*@ loop_invariant 0 <= i && i <= index && \reach(first.next, first, node, i);
	  @ assignable \nothing;
	  @*/
	for(int i = 0; i < index; i++) {
	    if(node.next == null) {
		throw new IndexOutOfBoundsException();
	    }
	    node = node.next;
	}
	
	return node.data;
    }
    
    
    public int size() {
	if(first == null) {
	    return 0;
	}
	int i = 0;
	/*@ loop_invariant 0 <= i && \reach(first.next, first, node, i);
	  @ assignable \nothing;
	  @*/
	for(Node node = first; node.next != null; node = node.next) {
	    i++;
	}
	return i;
    }
}
