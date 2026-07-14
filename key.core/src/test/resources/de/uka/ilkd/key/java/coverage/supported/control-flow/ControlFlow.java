public class ControlFlow {
    int f(int n) {
        int r = 0;
        outer:
        for (int i = 0; i < n; i++) {
            int j = 0;
            while (j < i) { if (j == 5) break outer; j++; }
            do { r++; } while (r < 0);
        }
        if (r > 10) { r = 10; } else { r = r + 1; }
        return r;
    }
}
