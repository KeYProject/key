
public class MethodFormatTest {
	public static	int main() {return a();}
	
   public static int a() {return b();}	public static int b() {	return	c();	}public static int c() {return d();}
	
	public static int d() {return e();
	}public static int e() {return f();}
	
  public static int f() {return g();
	}public static int g() {
		return 42;
	}
}
