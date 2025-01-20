/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.rusty.logic.op.sv.ProgramSV;

public class LoopScope implements LoopExpression {
    private final ProgramSV index;
    private final BlockExpression block;

    public LoopScope(ProgramSV index, BlockExpression block) {
        this.index = index;
        this.block = block;
    }

    @Override
    public Type type(Services services) {
        return null;
    }

    @Override
    public void visit(Visitor v) {

    }

    @Override
    public SyntaxElement getChild(int n) {
        return null;
    }

    @Override
    public int getChildCount() {
        return 0;
    }
}
