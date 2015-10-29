package resolver.test;

public class ResolverTestClass1 {

	public int field1;
	public String field10;
	private /*@ spec_public @*/String field11;
	
	public static int staticField10 = 0;
	
	public int methodNoParameter1() {
		return 1; 
	}
	public int method1Parameter4(int parameter1) {
		return parameter1;
	}
	public static int staticMethodNoParameter10() {
		return 1;
	}
	public static int staticMethod1Parameter10(int parameter1) {
		return parameter1;
	}
	public ResolverTestClass1 getThis(ResolverTestClass1 parameter1) {
	    return this;
	}
	public Object getThisAsObjectType() {
	    return this;
	}
}
