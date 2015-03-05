public class Main {
	public int main() {
		int defaultValue = SameName.defaultPackage();
		int aValue = a.SameName.a();
		int aSubValue = a.sub.SameName.aSub();
		int bValue = b.SameName.b();
		int cValue = c.SameName.c();
		int dValue = d.SameName.d();
		return defaultValue + aValue + aSubValue + bValue + cValue;
	}
}
