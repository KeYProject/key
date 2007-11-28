// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
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
