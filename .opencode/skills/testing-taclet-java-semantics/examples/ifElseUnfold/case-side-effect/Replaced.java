public class Replaced {
    public static void main(String[] args) {
        int i = 0;
        int x;
        boolean boolv = (i++ == 0);
        if (boolv) x = 1; else { x = 2; }
        System.out.println("x=" + x + " i=" + i);
    }
}
