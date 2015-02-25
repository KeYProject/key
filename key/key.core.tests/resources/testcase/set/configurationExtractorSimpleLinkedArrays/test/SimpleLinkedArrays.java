
public class SimpleLinkedArrays {
	private int value;
	
	private SimpleLinkedArrays[] next;
	
	/*@ requires x != null & x.next != null & x.next[0].next != null & x.next.length == 1 & x.next[0].next.length == 1;
	  @ ensures true;
	  @*/
	public static int compute(SimpleLinkedArrays x) {
		x.value = 1;
		x.next[0].value = 2;
		x.next[0].next[0].value = 3;
		return x.value + x.next[0].value + x.next[0].next[0].value + x.next.length;
	}
}
