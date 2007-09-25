


package java.util;

import java.security.AccessController;
import java.security.PrivilegedAction;
import java.text.DateFormatSymbols;
public abstract class TimeZone implements java.io.Serializable, Cloneable {
    public static final int SHORT = 0;
    public static final int LONG = 1;
    private static synchronized TimeZone defaultZone() {}
    private static synchronized HashMap timezones() {}
    static TimeZone getDefaultTimeZone(String sysTimeZoneId) {}
    public abstract int getOffset(int era, int year, int month,
                                int day, int dayOfWeek, int milliseconds);
    public int getOffset(long date) {}
    public abstract int getRawOffset();
    public abstract void setRawOffset(int offsetMillis);
    public String getID() {}
    public void setID(String id) {}
    public final String getDisplayName() {}
    public final String getDisplayName(Locale locale) {}
    public final String getDisplayName(boolean dst, int style) {}
    public String getDisplayName(boolean dst, int style, Locale locale) {}

    private String getDefaultDisplayName(boolean dst) {}
    public abstract boolean useDaylightTime();
    public abstract boolean inDaylightTime(Date date);
    public int getDSTSavings() {}
    public static TimeZone getTimeZone(String ID) {}
    public static String[] getAvailableIDs(int rawOffset) {}
    public static String[] getAvailableIDs() {}
    public static TimeZone getDefault() {}

    public static void setDefault(TimeZone zone) {}
    public boolean hasSameRules(TimeZone other) {}
    public Object clone() {}
}
