
public class MethodPOTest {
	private int x;
	
	public static void voidMethod(MethodPOTest param) {
		int value = param.x;
	}
	
	public static int returnMethod(MethodPOTest param) {
		return param.x;
	}
}
