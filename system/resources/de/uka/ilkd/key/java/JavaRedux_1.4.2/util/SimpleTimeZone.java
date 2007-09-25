


package java.util;
public class SimpleTimeZone extends TimeZone {
    public static final int STANDARD_TIME = 1;
    public static final int WALL_TIME = 0;
    public static final int UTC_TIME = 2;
    public SimpleTimeZone(int rawOffset, String id) {}
    public SimpleTimeZone(int rawOffset, String id,
                        int startMonth, int startDayOfWeekInMonth,
                        int startDayOfWeek, int startTime,
                        int endMonth, int endDayOfWeekInMonth,
                        int endDayOfWeek, int endTime) {}
    public SimpleTimeZone(int rawOffset, String id,
                        int startMonth, int startDayOfWeekInMonth,
                        int startDayOfWeek, int startTime,
                        int endMonth, int endDayOfWeekInMonth,
                        int endDayOfWeek, int endTime, int dstSavings) {}
    public SimpleTimeZone(int rawOffset, String id,
                        int startMonth, int startDayOfWeekInMonth,
                        int startDayOfWeek, int startTime, int startTimeMode,
                        int endMonth, int endDayOfWeekInMonth,
                        int endDayOfWeek, int endTime, int endTimeMode,
                        int dstSavings) {}
    public void setStartYear(int year) {}
    private int checkRule(int month, int day, int dayOfWeek) {}
    public void setStartRule(int month, int day, int dayOfWeek, int time) {}
    public void setStartRule(int month, int day, int dayOfWeek, int time, boolean after) {}
    public void setStartRule(int month, int day, int time) {}
    public void setEndRule(int month, int day, int dayOfWeek, int time) {}
    public void setEndRule(int month, int day, int dayOfWeek, int time, boolean after) {}
    public void setEndRule(int month, int day, int time) {}
    public int getOffset(int era, int year, int month,
                       int day, int dayOfWeek, int millis) {}
    public int getRawOffset() {}
    public void setRawOffset(int rawOffset) {}
    public int getDSTSavings() {}
    public void setDSTSavings(int dstSavings) {}
    public boolean useDaylightTime() {}
    private int getDaysInMonth(int month, int year) {}
    private boolean isBefore(int calYear,
                           int calMonth, int calDayOfMonth, int calDayOfWeek,
                           int calMillis, int mode, int month,
                           int day, int dayOfWeek, int millis) {}
    public boolean inDaylightTime(Date date) {}
    public synchronized int hashCode() {}

    public synchronized boolean equals(Object o) {}
    public boolean hasSameRules(TimeZone other) {}
    public String toString() {}
    private void readObject(java.io.ObjectInputStream input)
     throws java.io.IOException, ClassNotFoundException {}
    private void writeObject(java.io.ObjectOutputStream output)
     throws java.io.IOException {}
}
