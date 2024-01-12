
public class StatementKindTest {
	public void main() {
		// void method
		foo();
		// Declarations
		int i;
		boolean b = true;
		// Assignments
		i = 0;
		i = i + 1;
		i += 2;
		i ++;
		i --;
		i -= 2;
		i *= 2;
		i /= 2;
		i %= 4;
		i = get42();
		i = (2 + 4) * 2;
	}
	
	public void foo() {
	}
	
	public int get42() {
		return 42;
	}
}
