

package java.util;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
public final class Locale implements Serializable, Cloneable {
    public static final Locale ENGLISH = new Locale("en");
    public static final Locale FRENCH = new Locale("fr");
    public static final Locale GERMAN = new Locale("de");
    public static final Locale ITALIAN = new Locale("it");
    public static final Locale JAPANESE = new Locale("ja");
    public static final Locale KOREAN = new Locale("ko");
    public static final Locale CHINESE = new Locale("zh");
    public static final Locale SIMPLIFIED_CHINESE = new Locale("zh", "CN");
    public static final Locale TRADITIONAL_CHINESE = new Locale("zh", "TW");
    public static final Locale FRANCE = new Locale("fr", "FR");
    public static final Locale GERMANY = new Locale("de", "DE");
    public static final Locale ITALY = new Locale("it", "IT");
    public static final Locale JAPAN = new Locale("ja", "JP");
    public static final Locale KOREA = new Locale("ko", "KR");
    public static final Locale CHINA = SIMPLIFIED_CHINESE;
    public static final Locale PRC = CHINA;
    public static final Locale TAIWAN = TRADITIONAL_CHINESE;
    public static final Locale UK = new Locale("en", "GB");
    public static final Locale US = new Locale("en", "US");
    public static final Locale CANADA = new Locale("en", "CA");
    public static final Locale CANADA_FRENCH = new Locale("fr", "CA");
    private String convertLanguage(String language) {}
    public Locale(String language, String country, String variant) {}
    public Locale(String language, String country) {}
    public Locale(String language) {}
    public static Locale getDefault() {}
    public static void setDefault(Locale newLocale) {}
    public static Locale[] getAvailableLocales() {}
    public static String[] getISOCountries() {}
    public static String[] getISOLanguages() {}
    public String getLanguage() {}
    public String getCountry() {}
    public String getVariant() {}
    public final String toString() {}
    public String getISO3Language() {}
    public String getISO3Country() {}
    public final String getDisplayLanguage() {}
    public String getDisplayLanguage(Locale locale) {}
    public final String getDisplayCountry() {}
    public String getDisplayCountry(Locale locale) {}
    public final String getDisplayVariant() {}
    public String getDisplayVariant(Locale locale) {}
    public final String getDisplayName() {}
    public String getDisplayName(Locale locale) {}
    public Object clone() {}
    public int hashCode() {}
    public boolean equals(Object obj) {}
    private void writeObject(ObjectOutputStream s)
     throws IOException {}
    private void readObject(ObjectInputStream s)
     throws IOException, ClassNotFoundException {}
}
