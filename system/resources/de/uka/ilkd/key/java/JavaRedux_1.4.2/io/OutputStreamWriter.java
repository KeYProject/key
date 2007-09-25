


package java.io;

import gnu.java.io.EncodingManager;
import gnu.java.io.encode.Encoder;
public class OutputStreamWriter extends Writer {
    public OutputStreamWriter(OutputStream out, String encoding_scheme) throws UnsupportedEncodingException {}
    public OutputStreamWriter(OutputStream out) {}
    public void close() throws IOException {}
    public String getEncoding() {}
    public void flush() throws IOException {}
    public void write(char[] buf, int offset, int count) throws IOException {}
    public void write(String str, int offset, int count) throws IOException {}
    public void write(int ch) throws IOException {}
}
