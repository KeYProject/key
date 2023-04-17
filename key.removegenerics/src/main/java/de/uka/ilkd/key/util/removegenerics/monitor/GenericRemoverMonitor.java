package de.uka.ilkd.key.util.removegenerics.monitor;

public interface GenericRemoverMonitor {
    void taskStarted(String message);

    void warningOccurred(String message);
}
