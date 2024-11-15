/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty;

import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.ast.expr.BlockExpression;
import org.key_project.rusty.ast.stmt.ExpressionStatement;
import org.key_project.rusty.logic.PossibleProgramPrefix;
import org.key_project.rusty.logic.RustyBlock;

public class RustTools {
    /**
     * Returns the active statement of the passed a rust block.
     */
    public static RustyProgramElement getActiveStatement(RustyBlock rb) {
        assert rb.program() != null;

        RustyProgramElement result = (RustyProgramElement) rb.program().getChild(0);
        while ((result instanceof PossibleProgramPrefix)
                && !(result instanceof BlockExpression be && be.getChildCount() == 0)) {
            if (result instanceof ExpressionStatement es) {
                result = es.getExpression();
            } else {
                result = (RustyProgramElement) result.getChild(0);
            }
        }
        return result;
    }

}
