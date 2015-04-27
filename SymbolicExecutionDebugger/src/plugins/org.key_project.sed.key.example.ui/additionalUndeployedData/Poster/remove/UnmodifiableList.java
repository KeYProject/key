package remove;

public class UnmodifiableList {
	private int value;
	
	private UnmodifiableList next;
	
	public static int magicRemove(UnmodifiableList root) {
		root.value = 1;
		root.next.value = 2;
		root = root.next;
		return root.value;
	}
}
