/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.expression.annotation;

import de.uka.ilkd.key.java.ast.*;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.expression.*;

public class MarkerAnnotation extends AnnotationExpression {
    public MarkerAnnotation(KeYJavaType kjt) {
        super(kjt);
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public ProgramElement getChildAt(int index) {
        throw new ArrayIndexOutOfBoundsException();
    }

    @Override
    public int getExpressionCount() {
        return 0;
    }

    @Override
    public Expression getExpressionAt(int index) {
        throw new ArrayIndexOutOfBoundsException();
    }
}
