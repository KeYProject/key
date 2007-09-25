


package java.util;
public class GregorianCalendar extends Calendar {
    public static final int BC = 0;
    public static final int AD = 1;

    static final long serialVersionUID = -8125100834729963327L;
    private static ResourceBundle getBundle(Locale locale) {}
    public GregorianCalendar() {}
    public GregorianCalendar(TimeZone zone) {}
    public GregorianCalendar(Locale locale) {}
    public GregorianCalendar(TimeZone zone, Locale locale) {}
    public GregorianCalendar(int year, int month, int day) {}
    public GregorianCalendar(int year, int month, int day, int hour, int minute) {}
    public GregorianCalendar(int year, int month, int day,
                           int hour, int minute, int second) {}
    public void setGregorianChange(Date date) {}
    public final Date getGregorianChange() {}
    public boolean isLeapYear(int year) {}
    private long getLinearTime(int year, int dayOfYear, int millis) {}

    private int getWeekDay(int year, int dayOfYear) {}
    private int[] getDayOfYear(int year) {}
    protected synchronized void computeTime() {}
    private boolean isLeapYear(int year, boolean gregorian) {}
    private int getLinearDay(int year, int dayOfYear, boolean gregorian) {}
    private void calculateDay(int day, boolean gregorian) {}
    protected synchronized void computeFields() {}
    public boolean equals(Object o) {}
    public void add(int field, int amount) {}
    public void roll(int field, boolean up) {}

    private void cleanUpAfterRoll(int field, int delta) {}
    public void roll(int field, int amount) {}
    public int getMinimum(int field) {}
    public int getMaximum(int field) {}
    public int getGreatestMinimum(int field) {}
    public int getLeastMaximum(int field) {}
    public int getActualMinimum(int field) {}
    public int getActualMaximum(int field) {}
}
