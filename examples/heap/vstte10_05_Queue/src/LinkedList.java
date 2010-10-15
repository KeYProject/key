class LinkedList {
    private final int head;
    private final /*@nullable@*/ LinkedList tail;
    private final int length;
    
    //@ public final ghost \seq seq;
    //@ public final ghost \locset repr;
    
    
    /*@ public invariant \subset(this.*, repr);
      @ private invariant length == seq.length; 
      @ private invariant length != 0 ==> seq[0] == head;
      @ private invariant tail == null ==> length <= 1;
      @ private invariant tail != null ==> 2 <= length
      @                                    && \subset(tail.*, repr)
      @                                    && \subset(tail.repr, repr)
      @                                    && \disjoint(this.*, tail.repr)
      @                                    && seq[1..length] == tail.seq
      @                                    && tail.\inv;
      @*/
    
    
    //@ public accessible \inv: repr \measured_by length; 
    
    
    /**
     * Constructs an empty linked list.
     */
    /*@ public normal_behaviour
      @   ensures seq == \seq_empty;
      @   ensures repr == \all_fields(this);
      @*/
    public /*@pure@*/ LinkedList() {
	head = 42;
	tail = null;
	length = 0;
	//@ set seq = \seq_empty;
	//@ set repr = \all_fields(this);
    }
    
    
    /**
     * Constructs a linked list with one element.
     */
    /*@ public normal_behaviour
      @   ensures seq == \seq_singleton(h);
      @   ensures repr == \all_fields(this);
      @*/
    public /*@pure@*/ LinkedList(int h) {
	head = h;
	tail = null;
	length = 1;
	//@ set seq = \seq_singleton(h);
	//@ set repr = \all_fields(this);
    }
    
    
    /**
     * Constructs a linked list whose head is h and whose tail is "t"
     */
    /*@ public normal_behaviour
      @   requires t.\inv && 0 < t.length; 
      @   ensures seq == \seq_concat(\seq_singleton(h), t.seq);
      @   ensures repr == \set_union(\all_fields(this), t.repr);
      @*/
    /*@pure@*/ LinkedList(int h, LinkedList t) {
	head = h;
	tail = t;
	length = t.length + 1;
	//@ set seq = \seq_concat(\seq_singleton(h), t.seq);
	//@ set repr = \set_union(\all_fields(this), t.repr);
    }
    

    /**
     * Returns a new linked list whose first element (head)
     * is "d" and whose tail is "this".
     */
    /*@ public normal_behaviour
      @   ensures \result.\inv;
      @   ensures \result.seq == \seq_concat(\seq_singleton(d), seq);
      @   ensures \subset(\result.repr, \set_union(\all_fields(\result), repr));      
      @*/
    public /*@pure@*/ LinkedList cons(int d) {
	if(length == 0) {
	    return new LinkedList(d);
	} else {
	    return new LinkedList(d, this);
	}
    }
    
    
    /**
     * Returns a new list that is the concatenation of this list and
     * the list "end".
     */
    /*@ public normal_behaviour
      @   requires end.\inv;
      @   ensures \result.\inv;      
      @   ensures \result.seq == \seq_concat(seq, end.seq);
      @   ensures \fresh(\set_minus(\result.repr, end.repr));      
      @   measured_by seq.length;
      @*/
    public /*@pure@*/ LinkedList concat(LinkedList end) {
	if(tail != null) {
	    end = tail.concat(end);
	}
	return end.cons(head);
    }
    
    
    /**
     * Returns a new list that is the reverse of this list.
     */
    /*@ public normal_behaviour
      @   ensures \result.\inv;      
      @   ensures \result.seq == \seq_reverse(seq);
      @   ensures \fresh(\set_minus(\result.repr, repr));
      @   measured_by seq.length;
      @*/
    public /*@pure@*/ LinkedList reverse() {
	if(tail == null) {
	    return this;
	} else {
	    LinkedList r = tail.reverse();
	    LinkedList e = new LinkedList(head);
	    r = r.concat(e);
	    return r;
	}
    }
    
    
    /*@ public normal_behaviour
      @   requires seq.length != 0;
      @   ensures \result == seq[0];
      @*/
    public /*@pure@*/ int head() {
	return head;
    }
    
    
    /*@ public normal_behaviour
      @   ensures seq.length <= 1 ==> \result == null;
      @   ensures 2 <= seq.length ==> \result.seq == seq[1..seq.length]
      @                                && \subset(\result.repr, repr);
      @*/
    public /*@pure nullable@*/ LinkedList tail() {
	return tail;
    }
    
    
    /*@ public normal_behaviour
      @   ensures \result == seq.length;
      @*/
    public /*@pure@*/ int length() {
	return length;
    }
}
