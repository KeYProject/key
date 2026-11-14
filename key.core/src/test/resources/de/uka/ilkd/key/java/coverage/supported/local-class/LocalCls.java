public class LocalCls {
    int f() {
        class Local { int g() { return 9; } }
        Local l = new Local();
        return l.g();
    }
}
