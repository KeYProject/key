

package java.util;
public class Timer {
    private static final class TaskQueue {
        public TaskQueue() {}
        private void add(TimerTask task) {}
        private void remove() {}
        public synchronized void enqueue(TimerTask task) {}
        private TimerTask top() {}
        public synchronized TimerTask serve() {}
        public synchronized void setNullOnEmpty(boolean nullOnEmpty) {}
        public synchronized void stop() {}
    }
    private static final class Scheduler implements Runnable {
        public Scheduler(TaskQueue queue) {}

        public void run() {}
    }
    public Timer() {}
    public Timer(boolean daemon) {}
    private Timer(boolean daemon, int priority) {}
    private Timer(boolean daemon, int priority, String name) {}
    public void cancel() {}
    private void schedule(TimerTask task, long time, long period, boolean fixed) {}

    private static void positiveDelay(long delay) {}

    private static void positivePeriod(long period) {}
    public void schedule(TimerTask task, Date date) {}
    public void schedule(TimerTask task, Date date, long period) {}
    public void schedule(TimerTask task, long delay) {}
    public void schedule(TimerTask task, long delay, long period) {}
    public void scheduleAtFixedRate(TimerTask task, Date date, long period) {}
    public void scheduleAtFixedRate(TimerTask task, long delay, long period) {}
    protected void finalize() throws Throwable {}
}
