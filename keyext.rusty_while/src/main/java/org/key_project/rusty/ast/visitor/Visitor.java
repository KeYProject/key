/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.visitor;

import org.key_project.rusty.ast.expr.*;
import org.key_project.rusty.ast.stmt.EmptyStatement;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.logic.op.sv.SchemaVariable;

/**
 * This class is implemented by visitors/walkers. Each AST node implements a visit(Visitor) method
 * that calls the doActionAt<NodeType> method. Similar to the pretty print mechanism.
 */
public interface Visitor {
    void performActionOnArithLogicalExpression(ArithLogicalExpression x);

    void performActionOnAssignmentExpression(AssignmentExpression x);

    void performActionOnBlockExpression(BlockExpression x);

    void performActionOnBooleanLiteralExpression(BooleanLiteralExpression x);

    void performActionOnContextBlockExpression(ContextBlockExpression x);

    void performActionOnIntegerLiteralExpression(IntegerLiteralExpression x);

    void performActionOnNegationExpression(NegationExpression x);

    void performActionOnSchemaVariable(SchemaVariable x);

    void performActionOnProgramVariable(ProgramVariable x);

    void performActionOnEmptyStatement(EmptyStatement x);
}
