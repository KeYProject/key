package recursion;

public class Rec2 {
	
	static int i = 0;
	
    //@ public normal_behavior requires i>=0 && i<=2; ensures true;
    public static void z() {
        if (i>=0) Rec0.x();
        i--;
    }
}
