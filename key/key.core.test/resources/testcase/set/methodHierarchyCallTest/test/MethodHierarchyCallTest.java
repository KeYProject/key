
public class MethodHierarchyCallTest {
	public int main() {
		return a();
	}
	
	public int a() {
		return b();
	}
	
	public int b() {
		return c();
	}
	
	public int c() {
		return 42;
	}
}
