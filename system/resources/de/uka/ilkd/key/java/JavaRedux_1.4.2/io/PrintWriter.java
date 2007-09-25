

package java.io;
public class PrintWriter extends Writer {
    protected Writer out;
    public PrintWriter(Writer wr) {}
    public PrintWriter(Writer wr, boolean autoflush) {}
    public PrintWriter(OutputStream out) {}
    public PrintWriter(OutputStream out, boolean autoflush) {}
    protected void setError() {}
    public boolean checkError() {}
    public void flush() {}
    public void close() {}
    public void print(String str) {}
    public void print(char ch) {}
    public void print(char[] charArray) {}
    public void print(boolean bool) {}
    public void print(int inum) {}
    public void print(long lnum) {}
    public void print(float fnum) {}
    public void print(double dnum) {}
    public void print(Object obj) {}
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
    public void write(int ch) {}
    public void write(char[] charArray, int offset, int count) {}
    public void write(String str, int offset, int count) {}
    public void write(char[] charArray) {}
    public void write(String str) {}
}
