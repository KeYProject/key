

package java.lang;
public class Thread implements Runnable {
    public static final int MIN_PRIORITY = 1;
    public static final int NORM_PRIORITY = 5;
    public static final int MAX_PRIORITY = 10;
    volatile VMThread vmThread;
    volatile ThreadGroup group;
    final Runnable runnable;
    volatile String name;
    volatile boolean daemon;
    volatile int priority;
    Throwable stillborn;
    public Thread() {}
    public Thread(Runnable target) {}
    public Thread(String name) {}
    public Thread(ThreadGroup group, Runnable target) {}
    public Thread(ThreadGroup group, String name) {}
    public Thread(Runnable target, String name) {}
    public Thread(ThreadGroup group, Runnable target, String name) {}
    public Thread(ThreadGroup group, Runnable target, String name, long size) {}
    Thread(VMThread vmThread, String name, int priority, boolean daemon) {}
    public static int activeCount() {}
    public final void checkAccess() {}
    public int countStackFrames() {}
    public static Thread currentThread() {}
    public void destroy() {}
    public static void dumpStack() {}
    public static int enumerate(Thread[] array) {}
    public final String getName() {}
    public final synchronized int getPriority() {}
    public final ThreadGroup getThreadGroup() {}
    public static boolean holdsLock(Object obj) {}
    public synchronized void interrupt() {}
    public static boolean interrupted() {}
    public boolean isInterrupted() {}
    public final boolean isAlive() {}
    public final boolean isDaemon() {}
    public final void join() throws InterruptedException {}
    public final void join(long ms) throws InterruptedException {}
    public final void join(long ms, int ns) throws InterruptedException {}
    public final synchronized void resume() {}
    public void run() {}
    public final synchronized void setDaemon(boolean daemon) {}
    public synchronized ClassLoader getContextClassLoader() {}
    public synchronized void setContextClassLoader(ClassLoader classloader) {}
    public final synchronized void setName(String name) {}
    public static void yield() {}
    public static void sleep(long ms) throws InterruptedException {}
    public static void sleep(long ms, int ns) throws InterruptedException {}
    public synchronized void start() {}
    public final void stop() {}
    public final synchronized void stop(Throwable t) {}
    public final synchronized void suspend() {}
    public final synchronized void setPriority(int priority) {}
    public String toString() {}
    synchronized void die() {}
}
