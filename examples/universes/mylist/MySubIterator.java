public class MySubIterator extends MyIterator {
 
    public MySubIterator(Object o) {
	super(null);
    }


    public Object violate() {
	//violates encapsulation by returning a node which may be part of a list
        return pos.next.next;
    }
}
