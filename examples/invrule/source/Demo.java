public class Demo {

    static boolean limit=false;

    public static void main(String args[]) {
	System.out.println((new Demo()).mul(3,3,8));
    }

    int mul(int x, int y, int MAX) {
	int z=0;
	while (y>0) {
	    if (z+x>MAX) {
		limit=true;
		break;
	    }
	    z = z+x;
	    y = y-1;
	}
	return z;
    }


}
