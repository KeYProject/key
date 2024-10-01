/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.visitor;

import java.util.Map;

import org.key_project.rusty.Services;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.util.ExtList;

/**
 * Walks through a java AST in depth-left-first-order. This visitor replaces a number of program
 * variables by others or new ones.
 */
public class ProgVarReplaceVisitor extends CreatingASTVisitor {
    protected boolean replaceallbynew = true;

    /**
     * stores the program variables to be replaced as keys and the new program variables as values
     */
    protected final Map<ProgramVariable, ProgramVariable> replaceMap;

    private RustyProgramElement result = null;

    /**
     * creates a visitor that replaces the program variables in the given statement by new ones with
     * the same name
     *
     * @param st the statement where the prog vars are replaced
     * @param map the HashMap with the replacements
     * @param services the services instance
     */
    public ProgVarReplaceVisitor(RustyProgramElement st, Map<ProgramVariable, ProgramVariable> map,
            boolean replaceallbynew,
            Services services) {
        super(st, true, services);
        this.replaceallbynew = replaceallbynew;
        this.replaceMap = map;
        assert services != null;
    }

    /**
     * the action that is performed just before leaving the node the last time
     *
     * @param node the node described above
     */
    @Override
    protected void doAction(RustyProgramElement node) {
        node.visit(this);
    }

    /** starts the walker */
    @Override
    public void start() {
        stack.push(new ExtList());
        walk(root());
        ExtList el = stack.peek();
        int i = 0;
        while (!(el.get(i) instanceof RustyProgramElement)) {
            i++;
        }
        result = (RustyProgramElement) stack.peek().get(i);
    }

    public RustyProgramElement result() {
        return result;
    }

    @Override
    public void performActionOnProgramVariable(ProgramVariable x) {
        RustyProgramElement newPV = replaceMap.get(x);
        if (newPV != null) {
            addChild(newPV);
            changed();
        } else {
            doDefaultAction(x);
        }
    }
}
