/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.visitor;

import java.util.LinkedHashSet;

import org.key_project.rusty.Services;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.logic.op.ProgramVariable;

public class ProgramVariableCollector extends RustyASTVisitor {
    private final LinkedHashSet<ProgramVariable> result = new LinkedHashSet<>();

    /**
     * collects all program variables occurring in the AST <tt>root</tt> using this constructor is
     * equivalent to <tt>ProggramVariableCollector(root, false)</tt>
     *
     * @param root the ProgramElement which is the root of the AST
     * @param services the Services object
     */
    public ProgramVariableCollector(RustyProgramElement root, Services services) {
        super(root, services);
        assert services != null;
    }

    @Override
    public void start() {
        walk(root());
    }

    public LinkedHashSet<ProgramVariable> result() {
        return result;
    }

    @Override
    protected void doDefaultAction(RustyProgramElement x) {
    }

    @Override
    public void performActionOnProgramVariable(ProgramVariable x) {
        result.add(x);
    }
}
