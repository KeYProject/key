


package java.lang;

import java.io.Serializable;
public final class Boolean implements Serializable {
    private boolean value;
    public static final Boolean TRUE = new Boolean(true);
    public static final Boolean FALSE = new Boolean(false);
    public Boolean(boolean value) {}
    public Boolean(String s) {}
    public boolean booleanValue() {}
    public static Boolean valueOf(boolean b) {}
    public static Boolean valueOf(String s) {}
    public static String toString(boolean b) {}
    public String toString() {}
    public int hashCode() {}
    public boolean equals(Object obj) {}
    public static boolean getBoolean(String name) {}
}
