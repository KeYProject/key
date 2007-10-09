package de.uka.ilkd.key.visualdebugger;

public class DebuggerEvent {
    public static final int EXEC_FINISHED = 8;

    public static final int EXEC_STARTED = 7;

    public static final int NODE_SELECTED = 1;

    public static final int PROJECT_LOADED_SUCCESSFUL = 5;

    public static final int RED_PC_REMOVED = 3;

    public static final int STATUS_EVENT = 4;

    public static final int TEST_RUN_FAILED = 6;

    public static final int TREE_CHANGED = 0;

    public static final int VIS_STATE = 2;

    private final Object subject;

    private final int type;

    public DebuggerEvent(int type, Object subject) {
        this.type = type;
        this.subject = subject;

    }

    public Object getSubject() {
        return subject;
    }

    public int getType() {
        return type;
    }
}
