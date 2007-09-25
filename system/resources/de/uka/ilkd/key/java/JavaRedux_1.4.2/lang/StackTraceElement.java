


package java.lang;

import java.io.Serializable;
public class StackTraceElement implements Serializable {
    StackTraceElement(String fileName, int lineNumber, String className,
                    String methodName, boolean isNative) {}
    public String getFileName() {}
    public int getLineNumber() {}
    public String getClassName() {}
    public String getMethodName() {}
    public boolean isNativeMethod() {}
    public String toString() {}
    public boolean equals(Object o) {}
    public int hashCode() {}
    private static final boolean equals(Object o1, Object o2) {}
    private static final int hashCode(Object o) {}
}
