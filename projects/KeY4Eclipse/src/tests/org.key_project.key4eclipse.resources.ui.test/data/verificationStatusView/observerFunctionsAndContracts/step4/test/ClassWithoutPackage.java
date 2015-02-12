
public class ClassWithoutPackage {
	private int x;
	private int y;
	private int z;
	
	//@ model int ofm;
	//@ represents ofm = 2*x;
    //@ accessible ofm : this.z;
	
	//@ model int ofn;
	//@ represents ofn = 2*x;
    //@ accessible ofn : this.x;
    //@ accessible ofn : this.z;
}
