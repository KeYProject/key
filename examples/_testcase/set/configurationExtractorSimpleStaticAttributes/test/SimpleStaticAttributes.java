
public class SimpleStaticAttributes {
	private int x;
	
	private static SimpleStaticAttributes instance;
	
	public static final SimpleStaticAttributes finalInstance = new SimpleStaticAttributes(41);
	
	public static int staticInt;
	
	public static final int finalStaticint = 42;
	
	public SimpleStaticAttributes(int x) {
		this.x = x;
	}
	
	public static int compute(SimpleStaticAttributes newInstance) {
		staticInt = 1;
		if (finalStaticint == 42 && staticInt == 1) {
			instance = newInstance;
			return instance.x + finalInstance.x + staticInt + finalStaticint;
		}
		else {
			return -1;
		}
	}
}
