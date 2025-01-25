/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic;

public interface TerminalSyntaxElement extends SyntaxElement {
    @Override
    default SyntaxElement getChild(int n) {
        throw new IndexOutOfBoundsException(this.getClass() + " " + this + " has no children");
    }

    @Override
    default int getChildCount() {
        return 0;
    }
}
