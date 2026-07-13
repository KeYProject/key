public class VarInFor {
    int f() {
        int r = 0;
        for (var i = 0; i < 3; i++) { r = r + i; }
        return r;
    }
}
