public class B extends A {
    
    public int a() {
	return 2;
    }

    public int mInB() {
	return a();
    }

    public int m2InB() {
	return a2(2);
    }

}
