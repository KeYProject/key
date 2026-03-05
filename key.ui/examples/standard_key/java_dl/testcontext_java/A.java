public class InnerClassMethodResolution {

    public  byte m(long i) { return 2; }

    private int m(int i) { return 1; }

    static int callM() {
        InnerClassMethodResolution a = new InnerClassMethodResolution();
        return a.m(1);
    }

    static int callMviaB() {
        return B.callM();
    }

    final class B {
        static int callM() {
            InnerClassMethodResolution a = new InnerClassMethodResolution();
            return a.m(1);
        }
    }

}


public class Main {

    public static void main(){
        System.out.println(InnerClassMethodResolution.callM());
        System.out.println(InnerClassMethodResolution.B.callM());
        System.out.println(InnerClassMethodResolution.callMviaB());
    }
}


