
public class VariablesStaticTest {
	public static int z;
	
	public int main() {
		z = 2;
		StaticFields.a = 4;
		StaticFields.b = 8;
		return z + StaticFields.a + StaticFields.b; 
	}
}

class StaticFields {
	public static int a;
	
	public static int b;
}
