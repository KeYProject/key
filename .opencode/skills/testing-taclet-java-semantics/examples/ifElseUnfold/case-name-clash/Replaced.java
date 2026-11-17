public class Replaced {
    public static void main(String[] args) {
        int b = 1;
        boolean boolv = true;
        int x;
        boolean boolv_0 = (b == 0);   // \new #boolv: must not capture the surrounding boolv
        if (boolv_0) x = 1; else { x = 2; }
        System.out.println("x=" + x + " boolv=" + boolv);
    }
}
