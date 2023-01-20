
public class ObjectArrayIndexWriteAccess {
	public static int compute(ObjectIntWrapper[] array) {
		if (array != null) {
			if (array.length == 1) {
				array[0] = new ObjectIntWrapper(42);
				return array[0].value;
			}
			else {
				return -200;
			}
		}
		else {
			return -100;
		}
	}
}

class ObjectIntWrapper {
	public int value;

	public ObjectIntWrapper(int value) {
		this.value = value;
	}
}