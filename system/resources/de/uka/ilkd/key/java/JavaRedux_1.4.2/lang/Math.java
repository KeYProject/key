


package java.lang;

import java.util.Random;
import gnu.classpath.Configuration;
public final class Math {
    private Math() {}

    static {}
    public static final double E = 2.718281828459045;
    public static final double PI = 3.141592653589793;
    public static int abs(int i) {}
    public static long abs(long l) {}
    public static float abs(float f) {}
    public static double abs(double d) {}
    public static int min(int a, int b) {}
    public static long min(long a, long b) {}
    public static float min(float a, float b) {}
    public static double min(double a, double b) {}
    public static int max(int a, int b) {}
    public static long max(long a, long b) {}
    public static float max(float a, float b) {}
    public static double max(double a, double b) {}
    public native static double sin(double a);
    public native static double cos(double a);
    public native static double tan(double a);
    public native static double asin(double a);
    public native static double acos(double a);
    public native static double atan(double a);
    public native static double atan2(double y, double x);
    public native static double exp(double a);
    public native static double log(double a);
    public native static double sqrt(double a);
    public native static double pow(double a, double b);
    public native static double IEEEremainder(double x, double y);
    public native static double ceil(double a);
    public native static double floor(double a);
    public native static double rint(double a);
    public static int round(float a) {}
    public static long round(double a) {}
    public static synchronized double random() {}
    public static double toRadians(double degrees) {}
    public static double toDegrees(double rads) {}
}
