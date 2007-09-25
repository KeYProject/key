

package java.lang;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.WeakHashMap;
public class InheritableThreadLocal extends ThreadLocal {
    public InheritableThreadLocal() {}
    protected Object childValue(Object parentValue) {}
    static void newChildThread(Thread childThread) {}
}
