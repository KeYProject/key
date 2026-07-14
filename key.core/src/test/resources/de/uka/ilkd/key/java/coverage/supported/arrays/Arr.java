public class Arr {
    int sum(int[] a) { int s = 0; for (int i = 0; i < a.length; i++) s += a[i]; return s; }
    int grid() { int[][] m = new int[2][3]; m[1][2] = 7; return m[1][2]; }
}
