package recursion;

public class Rec0 {
	
	static int i = 0;
	
    //@ public normal_behavior requires i>=0 && i<=2; ensures true;
    public static void x() {
        if (i>=0) Rec1.y();
        i--;
    }
}
