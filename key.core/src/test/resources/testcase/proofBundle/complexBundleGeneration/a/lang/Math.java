package java.lang;

public final class Math {
    
    private Math() {}
    
    /*@ public normal_behavior
      @ requires y != 0;
      @ ensures (\exists int r; r * y + \result == x);
      @ ensures y < 0 ==> (0 >= \result && \result > y);
      @ ensures y > 0 ==> (0 <= \result && \result < y);
      @ assignable \strictly_nothing;
      @*/
    public static int floorMod(int x, int y);

    public static final double PI = 3.14159265358979323846;
    public static final double E = 2.7182818284590452354;

    public static double toRadians(double angdeg) {
        return angdeg / 180.0 * PI;
    }

    public static double toDegrees(double angrad) {
        return angrad * 180.0 / PI;
    }

    public static int abs(int a) {
        return (a < 0) ? -a : a;
    }

    public static long abs(long a) {
        return (a < 0) ? -a : a;
    }

    /*@ public normal_behaviour
      @  ensures a <= 0.0d ==> \result == 0.0d - a;
      @  ensures a > 0.0d ==> \result == a;
      @  assignable \strictly_nothing;
      @  // no_state  // for future use
      @*/
    public static double abs(double a) {
        return (a <= 0.0D) ? 0.0D - a : a;
    }

    public static float abs(float a) {
        return (a <= 0.0F) ? 0.0F - a : a;
    }

    public static int min(int a, int b) {
        return (a <= b) ? a : b;
    }

    public static long min(long a, long b) {
        return (a <= b) ? a : b;
    }

    public static double min(double a, double b) {
        return (a <= b) ? a : b;
    }

    public static float min(float a, float b) {
        return (a <= b) ? a : b;
    }

    public static int max(int a, int b) {
        return (a >= b) ? a : b;
    }

    public static long max(long a, long b) {
        return (a >= b) ? a : b;
    }

    public static double max(double a, double b) {
        if (a != a)
            return a;
        return (a >= b) ? a : b;
    }

    public static float max(float a, float b) {
        if (a != a)
            return a;
        return (a >= b) ? a : b;
    }

    public static double sin(double d);
    public static double asin(double d);
    public static double cos(double d);
    public static double acos(double d);
    public static double tan(double d);
    public static double atan2(double a, double b);
    public static double sqrt(double d);
    public static double pow(double a , double b);
    public static double exp(double a);
    public static double atan(double a);
}
