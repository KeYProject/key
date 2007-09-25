

package java.lang;

import java.util.Vector;
public class ThreadGroup {
    static ThreadGroup root = new ThreadGroup();
    static boolean had_uncaught_exception;
    final String name;
    private ThreadGroup() {}
    public ThreadGroup(String name) {}
    public ThreadGroup(ThreadGroup parent, String name) {}
    public final String getName() {}
    public final ThreadGroup getParent() {}
    public final int getMaxPriority() {}
    public final boolean isDaemon() {}
    public synchronized boolean isDestroyed() {}
    public final void setDaemon(boolean daemon) {}
    public final synchronized void setMaxPriority(int maxpri) {}
    public final boolean parentOf(ThreadGroup group) {}
    public final void checkAccess() {}
    public int activeCount() {}
    public int enumerate(Thread[] array) {}
    public int enumerate(Thread[] array, boolean recurse) {}
    public int activeGroupCount() {}
    public int enumerate(ThreadGroup[] array) {}
    public int enumerate(ThreadGroup[] array, boolean recurse) {}
    public final synchronized void stop() {}
    public final synchronized void interrupt() {}
    public final synchronized void suspend() {}
    public final synchronized void resume() {}
    public final synchronized void destroy() {}
    public void list() {}
    public void uncaughtException(Thread thread, Throwable t) {}
    public boolean allowThreadSuspension(boolean allow) {}
    public String toString() {}
    private int enumerate(Thread[] list, int next, boolean recurse) {}
    private int enumerate(ThreadGroup[] list, int next, boolean recurse) {}
    private void list(String indentation) {}
    final synchronized void addThread(Thread t) {}
    final synchronized void removeThread(Thread t) {}
    final synchronized void removeGroup(ThreadGroup g) {}
}
