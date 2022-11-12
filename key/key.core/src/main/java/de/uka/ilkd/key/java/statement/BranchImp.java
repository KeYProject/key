/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.java.statement;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.PositionInfo;

/**
 * Branch.
 *
 * @author <TT>AutoDoc</TT>
 */

public abstract class BranchImp extends JavaNonTerminalProgramElement implements Branch {

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children the children of this AST element as KeY classes. May contain: Comments
     */
    public BranchImp(ExtList children) {
        super(children);
    }


    public BranchImp() {
        super();
    }


    public BranchImp(ExtList children, PositionInfo pos) {
        super(children, pos);
    }


}
