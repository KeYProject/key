import java.awt.Color;


public class FieldDeclarationTest {
	private int x = 10;
	
	public static final int CONST = 42;
	
	private static Color color = Color.BLACK;
	
	private static final int CONST_AGAIN;
	
	static {
		if (true) {
			throw new RuntimeException();
		}
		CONST_AGAIN = 4711;
	}
}
