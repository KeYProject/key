
public class SimpleLinkedOjbectsInstanceVariable {
	private int value;
	
	private SimpleLinkedOjbectsInstanceVariable next;
	
	/*@ requires this.next != null & this.next.next != null;
	  @ ensures true;
	  @*/
	public int compute() {
		this.value = 1;
		this.next.value = 2;
		this.next.next.value = 3;
		return this.value + this.next.value + this.next.next.value;
	}
}
