package example8;

public class UnmodifiableList {
	public final UnmodifiableList next;
	public final int value;
	
	public UnmodifiableList(UnmodifiableList next, int value) {
		this.next = next;
		this.value = value;
	}

	public static int sumFirstThree(UnmodifiableList start) {
		int sum = 0;
		sum += start.value;
		sum += start.next.value;
		sum += start.next.next.value;
		return sum;
	}
}
