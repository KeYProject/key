


package java.util;
public class Observable {
    public Observable() {}
    public synchronized void addObserver(Observer observer) {}
    protected synchronized void clearChanged() {}
    public synchronized int countObservers() {}
    public synchronized void deleteObserver(Observer victim) {}
    public synchronized void deleteObservers() {}
    public synchronized boolean hasChanged() {}
    public void notifyObservers() {}
    public void notifyObservers(Object obj) {}
    protected synchronized void setChanged() {}
}
