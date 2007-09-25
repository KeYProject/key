

package java.lang;

import java.util.Collections;
import java.util.Map;
import java.util.WeakHashMap;
public class ThreadLocal {
    static final Object NULL = new Object();
    Object value;
    final Map valueMap = Collections.synchronizedMap(new WeakHashMap());
    public ThreadLocal() {}
    protected Object initialValue() {}
    public Object get() {}
    public void set(Object value) {}
}
