/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.service;

import recoder.java.CompilationUnit;
import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;

/**
 * An atomic change of a syntax tree represented by the root of the corresponding subtree. These
 * changes are used for change reports.
 */
public abstract class TreeChange {

    /**
     * The root of the change.
     */
    private final ProgramElement root;

    /**
     * The unit of the change. Initialized later on.
     */
    private CompilationUnit unit;

    /**
     * Flag indicating if this change is a minor one.
     */
    private boolean isMinor;

    /**
     * Constructor for the change.
     *
     * @param root the root of the change.
     */
    TreeChange(ProgramElement root) {
        this.root = root;
    }

    /**
     * Checks if this change is included in a bigger one and may be considered redundant for sake of
     * information update. Minor changes are important for the undo mechanism.
     *
     * @return <CODE>true</CODE>, if the changed tree is contained within another changed tree that
     *         occured in the same update period.
     */
    public boolean isMinor() {
        return isMinor;
    }

    final void setMinor(boolean isMinor) {
        this.isMinor = isMinor;
    }

    /**
     * Returns the root of the tree that has changed. Note that the "root" is not necessarily a non
     * terminal.
     *
     * @return the root element of the change.
     */
    public final ProgramElement getChangeRoot() {
        return root;
    }

    /**
     * Returns the parent of the root of the tree that has changed. The parent may differ from the
     * current parent of the root, if the root has been detached and reattached somewhere else.
     *
     * @return the parent of the root element of the change.
     */
    public abstract NonTerminalProgramElement getChangeRootParent();

    /**
     * Returns the compilation unit that has changed. The unit may differ from the current unit of
     * the root, if the root has been detached and reattached somewhere else. The unit can be equals
     * the change root.
     *
     * @return the compilation unit that has changed.
     */
    public final CompilationUnit getCompilationUnit() {
        return unit;
    }

    final void setCompilationUnit(CompilationUnit cu) {
        unit = cu;
    }

}
