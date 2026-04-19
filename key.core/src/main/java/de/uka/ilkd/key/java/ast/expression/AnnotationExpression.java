/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.expression;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.ast.*;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.visitor.Visitor;

public abstract class AnnotationExpression extends JavaNonTerminalProgramElement
implements Expression, ExpressionContainer {

    protected final KeYJavaType kjt;
    
    public AnnotationExpression(KeYJavaType kjt) {
        this.kjt = kjt;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnAnnotationExpression(this);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;
        return ((AnnotationExpression) o).kjt.equals(kjt) && super.equals(o);
    }

    @Override
    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
        return kjt;
    }

    public KeYJavaType getKeYJavaType() {
        return kjt;
    }
}
