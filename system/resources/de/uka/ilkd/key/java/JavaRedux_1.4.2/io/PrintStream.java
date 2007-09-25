


package java.io;
public class PrintStream extends FilterOutputStream {
    public PrintStream(OutputStream out) {}
    public PrintStream(OutputStream out, boolean auto_flush) {}
    public PrintStream(OutputStream out, boolean auto_flush, String encoding) throws UnsupportedEncodingException {}
    public boolean checkError() {}
    protected void setError() {}
    public void close() {}
    public void flush() {}
    public void print(boolean bool) {}
    public void print(int inum) {}
    public void print(long lnum) {}
    public void print(float fnum) {}
    public void print(double dnum) {}
    public void print(Object obj) {}
    public void print(String str) {}
    public void print(char ch) {}
    public void print(char[] charArray) {}
    public void println() {}
    public void println(boolean bool) {}
    public void println(int inum) {}
    public void println(long lnum) {}
    public void println(float fnum) {}
    public void println(double dnum) {}
    public void println(Object obj) {}
    public void println(String str) {}
    public void println(char ch) {}
    public void println(char[] charArray) {}
    public void write(int oneByte) {}
    public void write(byte[] buffer, int offset, int len) {}
}
