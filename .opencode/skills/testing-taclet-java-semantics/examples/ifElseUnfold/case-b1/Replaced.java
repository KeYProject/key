public class Replaced {
    public static void main(String[] args) {
        int b = 1;
        int x;
        boolean boolv = (b == 0);
        if (boolv) x = 1; else { x = 2; }
        System.out.println("x=" + x);
    }
}
