package recursion;

public class A {
	
	static int i = 0;
	
    //@ public normal_behavior requires i>=0 && i<=2; ensures true;
    public static void a() {
        if (i>=0) C.c();
        i--;
    }
}
