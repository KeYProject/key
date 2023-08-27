/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.recoderext.CreateObjectBuilder;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * If an allocation expression <code>new Class(...)</code> occurs, a new object has to be created,
 * in KeY this is quite similar to take it out of a list of objects and setting the implicit flag
 * <code> &lt;created&gt; </code> to <code>true</code> as well as setting all fields of the object
 * to their default values. For the complete procedure, the method creates the implicit method
 * <code>&lt;createObject&gt;</code> which on its part calls another implicit method
 * <code>lt;prepare&gt;</code> for setting the fields values.
 */
public class CreateObject extends ProgramTransformer {

    /**
     * @param newExpr The {@link ProgramElement}
     */
    public CreateObject(ProgramElement newExpr) {
        super("create-object", newExpr);
    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {

        TypeReference classReference = ((New) pe).getTypeReference();

        if (!(classReference.getKeYJavaType().getJavaType() instanceof ClassDeclaration)) {
            // no implementation available
            return new ProgramElement[] { pe };
        }

        return new ProgramElement[] { KeYJavaASTFactory.methodCall(classReference,
            CreateObjectBuilder.IMPLICIT_OBJECT_CREATE) };
    }
}
