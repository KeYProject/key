public class List{
    
    public /*@nullable@*/ Node head;

    public /*@nullable@*/ Node tail;

    /*@ public normal_behavior
      @  working_space_constructed 1000*\space(Node);
      @  ensures true;
      @*/
    public List(){   }

    /*@ public normal_behavior
      @  working_space_reentrant \space(Node);
      @  assignable tail, head, tail.next, \object_creation(Node), 
      @    \object_creation(javax.realtime.LTMemory), \object_creation(javax.realtime.MemoryStack);
      @  ensures true;
      @*/
    public @ExternallyConstructedScope @NoLocalScope void add(Object o){
	if(tail == null){
	    tail = head = new@<reentrantScope> Node(o);
	}else{
	    tail.next = new@<reentrantScope> Node(o);
	}
    }

    /*@ public normal_behavior
      @  working_space_local \space(List);
      @  ensures true;
      @*/
    public @ExternallyConstructedScope void testList(Test o){
	List l = new@<localScope> List();
	int i=0;
	/*@ loop_invariant i>=0;
	  @ assignable l.tail, l.head, l.tail.next, \object_creation(Node), i;
	  @ decreases 100-i;
	  @ working_space_single_iteration_param {\reentrantScope(l)} \space(Node);
	  @*/
	while(i<100){
	    l.add(o);
	    i++;
	}
    }

    /*@ public normal_behavior
      @  requires \reentrantScope(l).consumed + \space(Node) <= \reentrantScope(l).size;
      @  ensures true;
      @*/
    public @ExternallyConstructedScope void testListContract(Test o, List l){
	l.add(o);
    }

}
