


package java.util;
public abstract class ListResourceBundle extends ResourceBundle {
    public ListResourceBundle() {}
    public final Object handleGetObject(String key) {}
    public Enumeration getKeys() {}
    protected abstract Object[][] getContents();
}
