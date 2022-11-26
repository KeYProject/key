package java.lang;

public class Double {
    public static /*@ strictly_pure @*/ boolean isNaN(double val) {
        return val != val;
    }
}
