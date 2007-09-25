


package java.io;
public class OptionalDataException extends ObjectStreamException {
    public boolean eof;
    public int length;
    OptionalDataException(boolean eof, int count) {}
}
