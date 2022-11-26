package java.lang;

public class Float {
    public static /*@ strictly_pure @*/ boolean isNaN(float val) {
        return val != val;
    }
}
