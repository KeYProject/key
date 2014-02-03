package recursion;

public class Rec1 {
	
	static int i = 0;
	
    //@ public normal_behavior requires i>=0 && i<=2; ensures true;
    public static void y() {
        if (i>=0) Rec2.z();
        i--;
    }
}
