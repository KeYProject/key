
public class SimpleLinkedOjbects {
	private int value;
	
	private SimpleLinkedOjbects next;
	
	/*@ requires x != null & x.next != null & x.next.next != null;
	  @ ensures true;
	  @*/
	public static int compute(SimpleLinkedOjbects x) {
		x.value = 1;
		x.next.value = 2;
		x.next.next.value = 3;
		return x.value + x.next.value + x.next.next.value;
	}
	
//	public static void main(String[] args) {
//		SimpleLinkedOjbects first = new SimpleLinkedOjbects();
//		SimpleLinkedOjbects second = new SimpleLinkedOjbects();
//		SimpleLinkedOjbects third = new SimpleLinkedOjbects();
//		// Scenario 1, first.next = first
//		first.next = first;
//		System.out.println(compute(first) + "(first.next = first)");
//		// Scenario 2, first.next = second AND second.next = second
//		first.next = second;
//		second.next = second;
//		System.out.println(compute(first) + "(first.next = second & second.next = next)");
//		// Scenario 3, first.next = second AND second.next = first
//		second.next = first;
//		System.out.println(compute(first) + "(first.next = second & second.next = first)");
//		// Scenario 4, first.next = second AND second.next = third
//		second.next = third;
//		System.out.println(compute(first) + "(first.next = second & second.next = third)");
//	}
}
