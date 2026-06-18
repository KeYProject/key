class TypeInference {
    static int m(int a, int b) {
        var x = a + 1;
        final var y = b + 2;
        return x + y;
    }
}