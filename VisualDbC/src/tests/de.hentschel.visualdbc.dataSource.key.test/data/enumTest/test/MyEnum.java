public enum MyEnum {
	A(null),
	B(A),
	C(B);
	
	private MyEnum previous;
	
	private MyEnum(MyEnum previous) {
		this.previous = previous;
	}
	
	public int getValue() {
		return 0;
	}

	public MyEnum getPrevious() {
		return previous;
	}
}