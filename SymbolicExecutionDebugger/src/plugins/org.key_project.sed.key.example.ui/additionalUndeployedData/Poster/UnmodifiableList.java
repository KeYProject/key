
public class UnmodifiableList {
	private int value;
	
	private UnmodifiableList next;
	
	public static int magicUpdate(UnmodifiableList root) {
		root.value = 1;
		root.next.value = 2;
		root.next.next.value = 3;
		return root.value + root.next.value + root.next.next.value;
	}
}
