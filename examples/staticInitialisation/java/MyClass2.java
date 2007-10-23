public class MyClass2 {

    public static Object[] o;
    public static MyClass2 my;
    public static MyClass2[][] mine;


    public static void main(String[] args) {
	     MyClass2 d = null;
	     MyClass2.mine[0][0].my = d;
	     System.out.println(MyClass2.my);
    }

}