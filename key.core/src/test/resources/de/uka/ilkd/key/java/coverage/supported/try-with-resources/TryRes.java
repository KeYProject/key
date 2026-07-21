public class TryRes {
    static class Res implements java.io.Closeable {
        public void close() throws java.io.IOException { }
    }
    int f() throws java.io.IOException {
        try (Res r = new Res()) {
            return 1;
        }
    }
}
