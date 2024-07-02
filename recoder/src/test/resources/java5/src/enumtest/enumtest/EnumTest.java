package enumtest;

@AnAnnotation(x=10) public class EnumTest {
	public void foo() {
		Color c = Color.BLACK;
		System.err.println(c.toString());
		Color.BLACK.foo();
		switch (c) {
		case BLACK:
		case RED:
		case GOLD:
			break;
		}
	}
}

enum Color {
	BLACK,
	@AnAnnotation RED,
	GOLD;
	
	public int foo() { return 0; }
	public static Color returnRed() { return RED; }
}

enum Ord {
	A(1),
	B(2),
	C(3),
	;
	private Ord(int i) {
		// whatever...
	}
}

@interface AnAnnotation { int x() default 10; }