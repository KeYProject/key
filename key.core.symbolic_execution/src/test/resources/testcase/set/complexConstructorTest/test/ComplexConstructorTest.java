
public class ComplexConstructorTest {
	public static int main() {
		DefaultConstructor dc = new DefaultConstructor();
		ExplicitConstructor ec = new ExplicitConstructor();
		ExplicitConstructorWithSuper ecws = new ExplicitConstructorWithSuper();
		A a = new A();
		A aCustom = new A(12);
		B b = new B();
		B bCustomB = new B(true);
		B bCustomIB = new B(11, true);
		return dc.x + ec.x + ecws.x + a.a + aCustom.a + b.a + b.a + bCustomB.a + bCustomIB.a;
	}
}

class DefaultConstructor {
	public int x;
}

class ExplicitConstructor {
	public int x;
	
	public ExplicitConstructor() {
	}
}

class ExplicitConstructorWithSuper {
	public int x;
	
	public ExplicitConstructorWithSuper() {
		super();
	}
}

class A {
	public int a;
	
	public A() {
		this(42);
	}
	
	public A(int a) {
		this.a = a;
	}
}

class B extends A {
	public boolean b;

	public B() {
		this(false);
	}

	public B(boolean b) {
		this.b = b;
	}
	
	public B(int a, boolean b) {
		super(a);
		this.b = b;
	}
}