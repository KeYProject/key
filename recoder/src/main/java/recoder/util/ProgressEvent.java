/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.util;

import java.util.EventObject;

/**
 * Event indicating a processing progress.
 *
 * @author AL
 * @since 0.72
 */
public class ProgressEvent extends EventObject {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -8564312802396719743L;

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

    protected void setWorkToDoCount(int count) {
        this.workMax = count;
    }

    public int getWorkDoneCount() {
        return workCount;
    }

    protected void setWorkDoneCount(int count) {
        this.workCount = count;
    }

    public Object getState() {
        return state;
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
