package de.uka.ilkd.key.gui;

public interface ProgressStateListener<T> {
    public void started(T sender);
    public void stopped(T sender, boolean successfully);
    public void reportStatus(String status, int progress);
    public void reportStatus(String status);
    
    
}
