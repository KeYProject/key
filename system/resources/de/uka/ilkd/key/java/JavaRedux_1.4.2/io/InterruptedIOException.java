


package java.io;
public class InterruptedIOException extends IOException {
    public int bytesTransferred;
    public InterruptedIOException() {}
    public InterruptedIOException(String message) {}
    InterruptedIOException(String message, int bytesTransferred) {}
}
