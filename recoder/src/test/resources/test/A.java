package test;

public class A {
	private String method(int i) {
		return "int";
	}
	
	public String method(Integer i) {
		return "Integer";
	}
	
	public String privateContext() {
		return method(5);
	}
}
