/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.convenience;

import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;

/**
 * the "default" implementation for iterator listeners. This class may serve as a base class for
 * derived specialized versions.
 *
 * @author RN
 */
@SuppressWarnings("unused")
public class ASTIteratorAdapter implements ASTIteratorListener {

    public void enteringNode(ASTIterator it, ProgramElement node) {
        // defaults to nothing
    }

    public void leavingNode(ASTIterator it, ProgramElement node) {
        // defaults to nothing
    }

    public int enterChildren(ASTIterator it, NonTerminalProgramElement thisNode) {
        return ENTER_ALL;
    }

    public boolean enterChildNode(ASTIterator it, NonTerminalProgramElement thisNode,
            ProgramElement childNode) {
        return true;
    }

    public void returnedFromChildNode(ASTIterator it, NonTerminalProgramElement thisNode,
            ProgramElement childNode) {
        // defaults to nothing
    }

}
