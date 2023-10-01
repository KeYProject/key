/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.service;

import recoder.convenience.Format;
import recoder.java.CompilationUnit;
import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;
import recoder.util.Debug;

/**
 * A detachment change of a syntax tree.
 */
public class DetachChange extends TreeChange {

    /**
     * The former parent of the root.
     */
    private final NonTerminalProgramElement parent;

    /**
     * The former position code in the former parent.
     */
    private int position;

    /**
     * An attach change that effectively replaced this This information may be redundant, but is not
     * in general.
     */
    private AttachChange replacement;

    DetachChange(ProgramElement root, NonTerminalProgramElement parent, int position) {
        super(root);
        this.parent = parent;
        this.position = position;
        if (position < 0) {
            throw new IllegalChangeReportException("Illegal position code in " + this);
        }
    }

    DetachChange(ProgramElement root, AttachChange replacement) {
        super(root);
        Debug.assertNonnull(replacement);
        this.replacement = replacement;
        ProgramElement rep = replacement.getChangeRoot();
        this.parent = rep.getASTParent();
        if (parent != null) {
            // could be a compilation unit!
            this.position = parent.getChildPositionCode(rep);
            if (position < 0) {
                throw new IllegalChangeReportException("Illegal position code in " + replacement);
            }
        }
    }

    public final NonTerminalProgramElement getChangeRootParent() {
        return parent;
    }

    public final int getChangePositionCode() {
        return position;
    }

    public final AttachChange getReplacement() {
        return replacement;
    }

    // currently unused
    final void setReplacement(AttachChange ac) {
        replacement = ac;
    }

    public String toString() {
        StringBuilder buf = new StringBuilder();
        if (isMinor()) {
            buf.append("Minor ");
        }
        buf.append("Detached: ");
        if (getChangeRoot() instanceof CompilationUnit) {
            buf.append(Format.toString("%c %u", getChangeRoot()));
        } else {
            buf.append(Format.toString("%c %n", getChangeRoot()));
            buf.append(Format.toString(" from %c %n in %u @%p", getChangeRootParent()));
            /*
             * buf.append(" in role "); buf.append(getChangePositionCode() & 15);
             * buf.append(" at index "); buf.append(getChangePositionCode() >> 4);
             */
        }
        return buf.toString();
    }
}
