


package java.io;

import gnu.java.io.EncodingManager;
import gnu.java.io.decode.Decoder;
public class InputStreamReader extends Reader {
    public InputStreamReader(InputStream in) {}
    public InputStreamReader(InputStream in, String encoding_name) throws UnsupportedEncodingException {}
    public void close() throws IOException {}
    public String getEncoding() {}
    public boolean ready() throws IOException {}
    public int read(char[] buf, int offset, int length) throws IOException {}
    public int read() throws IOException {}
    public long skip(long count) throws IOException {}
}
