package pck2;
public class B extends A{

    protected int test() {	
	return super.test()+1;
    }
   
    public int pubTest() {
        return test();
    }

}