public class Exceptions {
    int f(int x) {
        try {
            if (x < 0) throw new RuntimeException("neg");
            return 1;
        } catch (RuntimeException e) {
            return -1;
        } finally {
            x = 0;
        }
    }
}
