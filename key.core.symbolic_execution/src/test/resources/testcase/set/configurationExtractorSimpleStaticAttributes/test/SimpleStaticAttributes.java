
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
		SimpleStaticAttributes.staticInt = 1;
		if (SimpleStaticAttributes.finalStaticint == 42 && SimpleStaticAttributes.staticInt == 1) {
			SimpleStaticAttributes.instance = newInstance;
			return SimpleStaticAttributes.instance.x + SimpleStaticAttributes.finalInstance.x + SimpleStaticAttributes.staticInt + SimpleStaticAttributes.finalStaticint;
		}
		else {
			return -1;
		}
	}
}
