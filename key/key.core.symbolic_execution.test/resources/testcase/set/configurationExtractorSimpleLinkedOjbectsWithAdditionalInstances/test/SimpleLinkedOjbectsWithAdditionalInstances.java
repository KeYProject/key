
public class SimpleLinkedOjbectsWithAdditionalInstances {
	private int value;
	
	private SimpleLinkedOjbectsWithAdditionalInstances next;
	
	/*@ requires x != null & x.next != null & x.next.next != null & a != null & a.x == 42 & b != null;
	  @ ensures true;
	  @*/
	public static int compute(IntWrapper a, SimpleLinkedOjbectsWithAdditionalInstances x, IntWrapper b) {
		x.value = 1;
		x.next.value = 2;
		x.next.next.value = 3;
		b.x = 99;
		return x.value + x.next.value + x.next.next.value + a.x + b.x;
	}
	
	public static class IntWrapper {
		public int x;
	}
}
