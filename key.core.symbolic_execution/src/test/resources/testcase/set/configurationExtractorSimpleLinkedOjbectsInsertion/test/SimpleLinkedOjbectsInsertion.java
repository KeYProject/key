
public class SimpleLinkedOjbectsInsertion {
	private int value;
	
	private SimpleLinkedOjbectsInsertion next;
	
	/*@ requires x != null & x.next != null & x.next.next != null;
	  @ ensures true;
	  @*/
	public static int compute(SimpleLinkedOjbectsInsertion x) {
		x.value = 1;
		x.next.value = 2;
		x.next.next.value = 3;
		SimpleLinkedOjbectsInsertion y = new SimpleLinkedOjbectsInsertion();
		y.value = 4;
		y.next = x.next;
		x.next = y;
		return x.value + x.next.value + x.next.next.value + x.next.next.next.value;
	}
	
//	public static void main(String[] args) {
//		SimpleLinkedOjbectsInsertion first = new SimpleLinkedOjbectsInsertion();
//		SimpleLinkedOjbectsInsertion second = new SimpleLinkedOjbectsInsertion();
//		SimpleLinkedOjbectsInsertion third = new SimpleLinkedOjbectsInsertion();
//		first.next = second;
//		second.next = third;
//		System.out.println(compute(first));
//	}
}
