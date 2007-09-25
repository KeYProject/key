//normal basic list
public class MyList {

    private MyNode head;

    public void prepend(Object data) {
        MyNode newHead = new MyNode(data);
        newHead.next = this.head;
        head = newHead;
    }
    
    public MyIterator iterator() {
	return new MyIterator(head);
    }
}
