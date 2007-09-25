


package java.util;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.lang.reflect.InvocationTargetException;
public abstract class Calendar implements Serializable, Cloneable {
    public static final int ERA = 0;
    public static final int YEAR = 1;
    public static final int MONTH = 2;
    public static final int WEEK_OF_YEAR = 3;
    public static final int WEEK_OF_MONTH = 4;
    public static final int DATE = 5;
    public static final int DAY_OF_MONTH = 5;
    public static final int DAY_OF_YEAR = 6;
    public static final int DAY_OF_WEEK = 7;
    public static final int DAY_OF_WEEK_IN_MONTH = 8;
    public static final int AM_PM = 9;
    public static final int HOUR = 10;
    public static final int HOUR_OF_DAY = 11;
    public static final int MINUTE = 12;
    public static final int SECOND = 13;
    public static final int MILLISECOND = 14;
    public static final int ZONE_OFFSET = 15;
    public static final int DST_OFFSET = 16;
    public static final int FIELD_COUNT = 17;
    public static final int SUNDAY = 1;
    public static final int MONDAY = 2;
    public static final int TUESDAY = 3;
    public static final int WEDNESDAY = 4;
    public static final int THURSDAY = 5;
    public static final int FRIDAY = 6;
    public static final int SATURDAY = 7;
    public static final int JANUARY = 0;
    public static final int FEBRUARY = 1;
    public static final int MARCH = 2;
    public static final int APRIL = 3;
    public static final int MAY = 4;
    public static final int JUNE = 5;
    public static final int JULY = 6;
    public static final int AUGUST = 7;
    public static final int SEPTEMBER = 8;
    public static final int OCTOBER = 9;
    public static final int NOVEMBER = 10;
    public static final int DECEMBER = 11;
    public static final int UNDECIMBER = 12;
    public static final int AM = 0;
    public static final int PM = 1;
    protected int[] fields = new int[FIELD_COUNT];
    protected boolean[] isSet = new boolean[FIELD_COUNT];
    protected long time;
    protected boolean isTimeSet;
    protected boolean areFieldsSet;
    static final long serialVersionUID = -1807547505821590642L;
    private static ResourceBundle getBundle(Locale locale) {}
    protected Calendar() {}
    protected Calendar(TimeZone zone, Locale locale) {}
    public static synchronized Calendar getInstance() {}
    public static synchronized Calendar getInstance(TimeZone zone) {}
    public static synchronized Calendar getInstance(Locale locale) {}
    public static synchronized Calendar getInstance(TimeZone zone, Locale locale) {}
    public static synchronized Locale[] getAvailableLocales() {}
    protected abstract void computeTime();
    protected abstract void computeFields();
    public final Date getTime() {}
    public final void setTime(Date date) {}
    public long getTimeInMillis() {}
    public void setTimeInMillis(long time) {}
    public int get(int field) {}
    protected final int internalGet(int field) {}
    public void set(int field, int value) {}
    public final void set(int year, int month, int date) {}
    public final void set(int year, int month, int date, int hour, int minute) {}
    public final void set(int year, int month, int date,
                        int hour, int minute, int second) {}
    public final void clear() {}
    public final void clear(int field) {}
    public final boolean isSet(int field) {}
    protected void complete() {}
    public boolean equals(Object o) {}
    public int hashCode() {}
    public boolean before(Object o) {}
    public boolean after(Object o) {}
    public abstract void add(int field, int amount);
    public abstract void roll(int field, boolean up);
    public void roll(int field, int amount) {}
    public void setTimeZone(TimeZone zone) {}
    public TimeZone getTimeZone() {}
    public void setLenient(boolean lenient) {}
    public boolean isLenient() {}
    public void setFirstDayOfWeek(int value) {}
    public int getFirstDayOfWeek() {}
    public void setMinimalDaysInFirstWeek(int value) {}
    public int getMinimalDaysInFirstWeek() {}
    public abstract int getMinimum(int field);
    public abstract int getMaximum(int field);
    public abstract int getGreatestMinimum(int field);
    public abstract int getLeastMaximum(int field);
    public int getActualMinimum(int field) {}
    public int getActualMaximum(int field) {}
    public Object clone() {}
    public String toString() {}
    private void writeObject(ObjectOutputStream stream) throws IOException {}
    private void readObject(ObjectInputStream stream)
     throws IOException, ClassNotFoundException {}
}
