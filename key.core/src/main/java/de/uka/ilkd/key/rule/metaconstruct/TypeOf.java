/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class TypeOf extends ProgramTransformer {

    /**
     * creates a typeof ProgramTransformer
     *
     * @param pe the instance of expression contained by the meta construct
     */
    public TypeOf(ProgramElement pe) {
        super("#typeof", pe);

    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations insts) {

        ExecutionContext ec = null;

        if (insts.getContextInstantiation() != null) {
            ec = insts.getContextInstantiation().activeStatementContext();
        }
        KeYJavaType kjt = null;
        if (pe instanceof Expression) {
            kjt = services.getTypeConverter().getKeYJavaType((Expression) pe, ec);
        } else {
            kjt = ((TypeRef) pe).getKeYJavaType();
        }

        assert kjt != null;

        if (!(kjt.getJavaType() instanceof PrimitiveType)) {
            if (kjt.getJavaType() instanceof ArrayType) {
                return new ProgramElement[] { KeYJavaASTFactory.typeRef(kjt,
                    ((ArrayType) kjt.getJavaType()).getDimension()) };
            }
        }

        return new ProgramElement[] { KeYJavaASTFactory.typeRef(kjt) };
    }
}
