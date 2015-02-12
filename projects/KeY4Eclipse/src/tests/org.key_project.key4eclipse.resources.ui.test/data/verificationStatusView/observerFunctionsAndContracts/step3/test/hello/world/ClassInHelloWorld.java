package hello.world;

public class ClassInHelloWorld {
	private int x;
	private int y;
	
	//@ model int ofm;
	//@ represents ofm = 2*x;
    //@ accessible ofm : this.x;
    //@ accessible ofm : this.x, this.y;
    //@ accessible ofm : this.y;
	
    //@ accessible \inv : this.x;
	
	//@ model int ofn;
	//@ represents ofn = 2*x;
    //@ accessible ofn : this.x;
    //@ accessible ofn : this.x, this.y;
    //@ accessible ofn : this.y;
}
