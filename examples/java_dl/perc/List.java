public class List{
    
    public Node head;

    public Node tail;

    /*@ public normal_behavior
      @  working_space_constructed 1000*\space(Node);
      @  ensures true;
      @*/
    public List(){   }

    /*@ public normal_behavior
      @  working_space_reentrant \space(Node);
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
    public @ExternallyConstructedScope void testList(Object o){
	List l = new@<localScope> List();
	l.add(o);
    }

}
