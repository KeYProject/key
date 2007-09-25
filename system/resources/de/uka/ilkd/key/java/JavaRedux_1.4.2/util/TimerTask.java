

package java.util;
public abstract class TimerTask implements Runnable {
    long scheduled;
    long lastExecutionTime;
    long period;
    boolean fixed;
    protected TimerTask() {}
    public boolean cancel() {}
    public abstract void run();
    public long scheduledExecutionTime() {}
}
