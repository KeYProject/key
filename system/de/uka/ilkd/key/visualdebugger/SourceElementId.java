// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.visualdebugger;

import java.io.File;

/**
 * A source element id identifies an occurrence of a source code element
 * unambigously. In the current implementation an occurrence is identified by
 * labeling programs (up to now only statement labels are supported). the
 * labelling is performed by inserting a pseudo method call
 * <tt>Debug.sep(id)</tt> before and after each statement.
 * 
 * An isnatnce of this class refers to exact one such label.
 */
public class SourceElementId {
    private String className = "";

    private File file;

    private int id;

    private boolean isBoolean = false;

    private boolean isStatement = true;

    public SourceElementId(String id) {
        this("", new Integer(id).intValue());
    }

    public SourceElementId(String cl, int id) {
        this.id = id;
        this.className = cl;

    }

    public SourceElementId(String cl, String id) {
        this(id);
        this.className = cl;

    }

    public SourceElementId(String cl, String id, boolean isStatement,
            boolean isBoolean) {
        this(cl, id);
        this.isStatement = isStatement;
        this.isBoolean = isBoolean;
    }

    public boolean equals(Object o) {
        if (o instanceof SourceElementId) {
            SourceElementId id2 = (SourceElementId) o;
            return id == id2.getId();
        }
        return false;
    }

    public String getClassName() {
        return className;
    }

    public File getFile() {
        return file;
    }

    public int getId() {
        return id;
    }

    public int hashCode() {
        return id;
    }

    public boolean isBoolean() {
        return isBoolean;
    }

    public boolean isStatement() {
        return isStatement;
    }

    public String toString() {
        return "Class Name: " + className + " Statement: " + id + " File"
                + file;
    }

}
