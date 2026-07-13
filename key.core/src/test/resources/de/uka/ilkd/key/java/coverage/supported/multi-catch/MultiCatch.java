public class MultiCatch {
    static class E1 extends Exception { }
    static class E2 extends Exception { }
    int f(int x) throws Exception {
        try {
            if (x == 1) throw new E1(); else throw new E2();
        } catch (E1 | E2 e) {
            return -1;
        }
    }
}
