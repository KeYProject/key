

package java.lang;

import java.io.Serializable;
public final class StringBuffer implements Serializable, CharSequence {
    int count;
    char[] value;
    boolean shared;
    public StringBuffer() {}
    public StringBuffer(int capacity) {}
    public StringBuffer(String str) {}
    public synchronized int length() {}
    public synchronized int capacity() {}
    public synchronized void ensureCapacity(int minimumCapacity) {}
    public synchronized void setLength(int newLength) {}
    public synchronized char charAt(int index) {}
    public synchronized void getChars(int srcOffset, int srcEnd,
                                    char[] dst, int dstOffset) {}
    public synchronized void setCharAt(int index, char ch) {}
    public StringBuffer append(Object obj) {}
    public synchronized StringBuffer append(String str) {}
    public synchronized StringBuffer append(StringBuffer stringBuffer) {}
    public StringBuffer append(char[] data) {}
    public synchronized StringBuffer append(char[] data, int offset, int count) {}
    public StringBuffer append(boolean bool) {}
    public synchronized StringBuffer append(char ch) {}
    public StringBuffer append(int inum) {}
    public StringBuffer append(long lnum) {}
    public StringBuffer append(float fnum) {}
    public StringBuffer append(double dnum) {}
    public synchronized StringBuffer delete(int start, int end) {}
    public StringBuffer deleteCharAt(int index) {}
    public synchronized StringBuffer replace(int start, int end, String str) {}
    public String substring(int beginIndex) {}
    public CharSequence subSequence(int beginIndex, int endIndex) {}
    public synchronized String substring(int beginIndex, int endIndex) {}
    public synchronized StringBuffer insert(int offset,
                                          char[] str, int str_offset, int len) {}
    public StringBuffer insert(int offset, Object obj) {}
    public synchronized StringBuffer insert(int offset, String str) {}
    public StringBuffer insert(int offset, char[] data) {}
    public StringBuffer insert(int offset, boolean bool) {}
    public synchronized StringBuffer insert(int offset, char ch) {}
    public StringBuffer insert(int offset, int inum) {}
    public StringBuffer insert(int offset, long lnum) {}
    public StringBuffer insert(int offset, float fnum) {}
    public StringBuffer insert(int offset, double dnum) {}
    public int indexOf(String str) {}
    public synchronized int indexOf(String str, int fromIndex) {}
    public int lastIndexOf(String str) {}
    public synchronized int lastIndexOf(String str, int fromIndex) {}
    public synchronized StringBuffer reverse() {}
    public String toString() {}
    private void ensureCapacity_unsynchronized(int minimumCapacity) {}
    private boolean regionMatches(int toffset, String other) {}
}
