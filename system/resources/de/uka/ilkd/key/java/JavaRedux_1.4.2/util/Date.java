


package java.util;
public class Date implements Cloneable, Comparable, java.io.Serializable {
    public Date() {}
    public Date(long time) {}
    public Date(int year, int month, int day) {}
    public Date(int year, int month, int day, int hour, int min) {}
    public Date(int year, int month, int day, int hour, int min, int sec) {}
    public Date(String s) {}

    public Object clone() {}
    public static long UTC(int year, int month, int date,
                         int hrs, int min, int sec) {}
    public long getTime() {}
    public int getTimezoneOffset() {}
    public void setTime(long time) {}
    public boolean after(Date when) {}
    public boolean before(Date when) {}
    public boolean equals(Object obj) {}
    public int compareTo(Date when) {}
    public int compareTo(Object obj) {}

    public int hashCode() {}

    public String toString() {}
    public String toLocaleString() {}
    public String toGMTString() {}

    private static int parseTz(String tok, char sign)
     throws IllegalArgumentException {}

    private static int parseMonth(String tok) {}

    private static boolean parseDayOfWeek(String tok) {}
    public static long parse(String string) {}
    public int getYear() {}
    public void setYear(int year) {}
    public int getMonth() {}
    public void setMonth(int month) {}
    public int getDate() {}
    public void setDate(int date) {}
    public int getDay() {}
    public int getHours() {}
    public void setHours(int hours) {}
    public int getMinutes() {}
    public void setMinutes(int minutes) {}
    public int getSeconds() {}
    public void setSeconds(int seconds) {}
    private void readObject(java.io.ObjectInputStream input)
     throws java.io.IOException, ClassNotFoundException {}
    private void writeObject(java.io.ObjectOutputStream output)
     throws java.io.IOException {}
}
