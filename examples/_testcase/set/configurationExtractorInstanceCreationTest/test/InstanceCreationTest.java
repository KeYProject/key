
public class InstanceCreationTest {
	private InstanceCreationTest next;
	
	private static InstanceCreationTestWrapper classWrapper;
	
	private InstanceCreationTestWrapper instanceWrapper;
	
	public int compute() {
		classWrapper = new InstanceCreationTestWrapper(1);
		instanceWrapper = new InstanceCreationTestWrapper(2);
		if (next != null) {
			next.instanceWrapper = new InstanceCreationTestWrapper(3);
			InstanceCreationTestWrapper localWrapper = new InstanceCreationTestWrapper(4);
			return classWrapper.value + instanceWrapper.value + next.instanceWrapper.value + localWrapper.value;
		}
		else {
			return -100;
		}
	}
}

class InstanceCreationTestWrapper {
	public int value;

	public InstanceCreationTestWrapper(int value) {
		super();
		this.value = value;
	}
}