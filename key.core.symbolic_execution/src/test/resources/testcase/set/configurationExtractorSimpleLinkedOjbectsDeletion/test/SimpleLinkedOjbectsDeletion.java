
public class SimpleLinkedOjbectsDeletion {
	private int value;
	
	private SimpleLinkedOjbectsDeletion next;
	
	/*@ requires x != null & x.next != null & x.next.next != null;
	  @ ensures true;
	  @*/
	public static int compute(SimpleLinkedOjbectsDeletion x) {
		x.value = 1;
		x.next.value = 2;
		x.next.next.value = 3;
		x.next = x.next.next;
		return x.value + x.next.value;
	}
}
