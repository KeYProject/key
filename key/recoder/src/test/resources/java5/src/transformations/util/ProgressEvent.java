package recoder.util;

import java.util.EventObject;

/**
 * Event indicating a processing progress.
 * 
 * @since 0.72
 * @author AL
 */
public class ProgressEvent extends EventObject {

    private int workCount;

    private int workMax;

    private Object state;

    public ProgressEvent(Object source, int workDone, int workToDo) {
        this(source, workDone, workToDo, null);
    }

    public ProgressEvent(Object source, int workDone, int workToDo, Object state) {
        super(source);
        setWork(workDone, workToDo, state);
    }

    public int getWorkToDoCount() {
        return workMax;
    }

    public int getWorkDoneCount() {
        return workCount;
    }

    public Object getState() {
        return state;
    }

    protected void setWorkDoneCount(int count) {
        this.workCount = count;
    }

    protected void setWorkToDoCount(int count) {
        this.workMax = count;
    }

    protected void setState(Object state) {
        this.state = state;
    }

    protected void setWork(int workDone, int workToDo, Object state) {
        this.workCount = workDone;
        this.workMax = workToDo;
        this.state = state;
    }

}