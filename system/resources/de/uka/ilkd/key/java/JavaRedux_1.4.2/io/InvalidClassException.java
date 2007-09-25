


package java.io;
public class InvalidClassException extends ObjectStreamException {
    public String classname;
    public InvalidClassException(String message) {}
    public InvalidClassException(String classname, String message) {}
    public String getMessage() {}
}
