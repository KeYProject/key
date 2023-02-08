/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
// This file is part of the RECODER library and protected by the LGPL.

package recoder.service;

import recoder.convenience.Format;
import recoder.java.CompilationUnit;
import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;

/**
 * An attachment change of a syntax tree.
 */
public class AttachChange extends TreeChange {

    AttachChange(ProgramElement root) {
        super(root);
    }

    public final NonTerminalProgramElement getChangeRootParent() {
        return getChangeRoot().getASTParent();
    }

    public String toString() {
        StringBuffer buf = new StringBuffer();
        if (isMinor()) {
            buf.append("Minor ");
        }
        buf.append("Attached: ");
        if (getChangeRoot() instanceof CompilationUnit) {
            buf.append(Format.toString("%c %u", getChangeRoot()));
        } else {
            buf.append(Format.toString("%c %n", getChangeRoot()));
            buf.append(Format.toString(" to %c %n in %u @%p", getChangeRootParent()));
        }
        return buf.toString();
    }
}
