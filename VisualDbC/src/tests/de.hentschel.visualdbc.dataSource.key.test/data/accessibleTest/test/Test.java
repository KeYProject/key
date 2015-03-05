package test;

public class Test {
	private int x;
	
	public Test(int x) {
		this.x = x;
	}
}

class B {
    //@ accessible \inv : this.*, c.*;
    public final /*@ nullable @*/ Test c;
    
    //@ invariant \invariant_for(c);
    
    B(int x) { c = new Test(x); }
}