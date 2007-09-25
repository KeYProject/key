

package java.lang;

import java.io.PrintStream;
import java.io.PrintWriter;
import java.io.Serializable;
public class Throwable implements Serializable {
    public Throwable() {}
    public Throwable(String message) {}
    public Throwable(String message, Throwable cause) {}
    public Throwable(Throwable cause) {}
    public String getMessage() {}
    public String getLocalizedMessage() {}
    public Throwable getCause() {}
    public Throwable initCause(Throwable cause) {}
    public String toString() {}
    public void printStackTrace() {}
    public void printStackTrace(PrintStream s) {}
    public void printStackTrace(PrintWriter pw) {}
    private static class StaticData {

        static {}
    }
    private String stackTraceString() {}
    private static void stackTraceStringBuffer(StringBuffer sb, String name,
                                        StackTraceElement[] stack, int equal) {}
    public Throwable fillInStackTrace() {}
    public StackTraceElement[] getStackTrace() {}
    public void setStackTrace(StackTraceElement[] stackTrace) {}
}
