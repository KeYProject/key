

package java.io;
public class PipedReader extends Reader {
    PipedWriter source;
    boolean closed;
    static final int PIPE_SIZE = 2048;
    char[] buffer = new char[PIPE_SIZE];
    int in = -1;
    int out = 0;
    char[] read_buf = new char[1];
    public PipedReader() {}
    public PipedReader(PipedWriter source) throws IOException {}
    public void connect(PipedWriter source) throws IOException {}
    void receive(char[] buf, int offset, int len)
     throws IOException {}
    public int read() throws IOException {}
    public int read(char[] buf, int offset, int len)
     throws IOException {}

    public boolean ready() throws IOException {}
    public void close() throws IOException {}
}
