public class IdenticalTermsDuringProof {
    public static int mid(final int x, final int y, final int z) {
        int mid = z;
        if (y < z) {
            if (x <= y) {
                mid = y;
            }
        } else {
            mid = y;
        }
        return mid;
    }
}
