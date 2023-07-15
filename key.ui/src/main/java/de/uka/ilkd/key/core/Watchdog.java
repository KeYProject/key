package de.uka.ilkd.key.core;

import java.awt.*;
import java.util.Set;

import de.uka.ilkd.key.util.ThreadUtilities;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Watchdog to monitor the state of the KeY system. If all worker and UI threads
 * are waiting / blocked, a deadlock is reported.
 *
 * @author Arne Keller
 */
public final class Watchdog {
    private static final Logger LOGGER = LoggerFactory.getLogger(Watchdog.class);
    /**
     * Threads that are ignored by the watchdog when checking for a deadlock.
     * These are not relevant for that use case since they are always runnable.
     */
    private static final Set<String> IGNORED_THREADS = Set.of("Watchdog", "Reference Handler",
        "Signal Dispatcher", "Notification Thread", "AWT-XAWT", "DestroyJavaVM");
    /**
     * These modules are ignored when printing stacktraces.
     */
    private static final Set<String> IGNORED_MODULES = Set.of("java.desktop", "java.base");

    private Watchdog() {

    }

    public static void start() {
        new Thread(Watchdog::run, "Watchdog").start();
    }

    private static void run() {
        while (true) {
            try {
                Thread.sleep(10000);
            } catch (InterruptedException e) {
                return;
            }
            var threads = ThreadUtilities.getThreads();
            var anyProgress = false;

            /*
             * example of UI deadlock:
             *
             * Reference Handler RUNNABLE
             * Finalizer WAITING
             * Signal Dispatcher RUNNABLE
             * Notification Thread RUNNABLE
             * Java2D Disposer WAITING
             * AWT-XAWT RUNNABLE
             * AWT-Shutdown WAITING
             * process reaper TIMED_WAITING
             * TimerQueue WAITING
             * Thread-0 RUNNABLE
             * Timer-0 TIMED_WAITING
             * AWT-EventQueue-0 TIMED_WAITING
             * DestroyJavaVM RUNNABLE
             * SwingWorker-pool-1-thread-1 WAITING
             * ForkJoinPool.commonPool-worker-1 TIMED_WAITING
             * Common-Cleaner TIMED_WAITING
             */

            for (int i = 0; i < threads.length; i++) {
                var thread = threads[i];
                if (thread == null || IGNORED_THREADS.contains(thread.getName())) {
                    continue;
                }
                switch (thread.getState()) {
                case NEW:
                case RUNNABLE:
                    anyProgress = true;
                    break;
                case WAITING:
                    if (thread.getName().equals("AWT-EventQueue-0")
                            && EventQueue.getCurrentEvent() == null) {
                        anyProgress = true; // nothing to do
                    }
                case BLOCKED:
                case TIMED_WAITING:
                case TERMINATED:
                    break;
                }
            }

            if (!anyProgress) {
                // print error to console
                // unfortunately, we cannot display a dialog since the UI thread is blocked...
                LOGGER.error("Watchdog detected deadlock!");
                LOGGER.info("Current thread state:");
                for (int i = 0; i < threads.length; i++) {
                    var thread = threads[i];
                    if (thread == null || IGNORED_THREADS.contains(thread.getName())) {
                        continue;
                    }
                    LOGGER.info("{} {}", thread.getName(), thread.getState());
                    var trace = thread.getStackTrace();
                    for (int j = 0; j < trace.length; j++) {
                        var el = trace[j];
                        if (j > 0 && el.getModuleName() != null
                                && IGNORED_MODULES.contains(el.getModuleName())) {
                            continue;
                        }
                        LOGGER.info(" {}", el);
                    }
                }
                return;
            }
        }
    }
}
