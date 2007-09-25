


package java.util;
public class StringTokenizer implements Enumeration {
    public StringTokenizer(String str) {}
    public StringTokenizer(String str, String delim) {}
    public StringTokenizer(String str, String delim, boolean returnDelims) {}
    public boolean hasMoreTokens() {}
    public String nextToken(String delim) throws NoSuchElementException {}
    public String nextToken() throws NoSuchElementException {}
    public boolean hasMoreElements() {}
    public Object nextElement() throws NoSuchElementException {}
    public int countTokens() {}
}
