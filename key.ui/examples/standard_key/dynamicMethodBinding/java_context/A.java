public class A {
    
    private int a() {
	return 1;
    }

    public int mInA() {
	return a();
    }


  
    private int a2(byte a) {
	return 1;
    }

    public int a2(int a) {
	return 2;
    }

    public int m2InA() {
	return a2((byte)2);
    }

}
