


package java.util;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintStream;
import java.io.PrintWriter;
public class Properties extends Hashtable {
    protected Properties defaults;
    public Properties() {}
    public Properties(Properties defaults) {}
    public Object setProperty(String key, String value) {}
    public void load(InputStream inStream) throws IOException {}
    public void save(OutputStream out, String header) {}
    public void store(OutputStream out, String header) throws IOException {}
    public String getProperty(String key) {}
    public String getProperty(String key, String defaultValue) {}
    public Enumeration propertyNames() {}
    public void list(PrintStream out) {}
    public void list(PrintWriter out) {}
    private void formatForOutput(String str, StringBuffer buffer, boolean key) {}
}
