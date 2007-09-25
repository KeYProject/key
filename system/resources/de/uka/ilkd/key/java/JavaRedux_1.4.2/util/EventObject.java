


package java.util;

import java.io.Serializable;
public class EventObject implements Serializable {
    protected transient Object source;
    public EventObject(Object source) {}
    public Object getSource() {}
    public String toString() {}
}
