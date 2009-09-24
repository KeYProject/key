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
	Node n = new Node();
	n.data = o;
	if(first == null) {
	    first = n;
	    last = n;
	} else {
	    last.next = n;
	    last = n;
	}
    }

    
    public Object get(int index) {
	if(index < 0) {
	    throw new IndexOutOfBoundsException();
	}
	Node n = first;
	/*@ loop_invariant 0 <= index;
	  @ assignable \nothing;
	  @*/
	while(index > 0) {
	    if(n == null) {
		throw new IndexOutOfBoundsException();
	    }
	    n = n.next;
	    index--;
	}
	return n.data;
    }
    
    
    //@ ensures \result >= 0;
    //@ diverges true;
    public int size() {
	int i = 0;
	/*@ loop_invariant i >= 0 && \reach(first.next, first, n, i);
	  @ assignable \nothing;
	  @*/
	for(Node n = first; n != last; n = n.next) {
	    i++;
	}
	return i;
    }
}
