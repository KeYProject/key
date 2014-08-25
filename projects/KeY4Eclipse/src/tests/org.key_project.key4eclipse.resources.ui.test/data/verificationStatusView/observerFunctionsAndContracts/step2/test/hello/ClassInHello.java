package hello;

public class ClassInHello {
	private int x;
	private int y;
	
	//@ model int ofm;
	//@ represents ofm = 2*x;
    //@ accessible ofm : this.x;
}
