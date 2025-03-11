/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * creates an assignment instantiationOf(#newObjectsV).<initialized> = true
 */
public class PostWork extends ProgramTransformer {

    private final static String POST_WORK = "post-work";

    /**
     * Whether this transformer is used schematically (i.e., in taclets).
     */
    private final boolean schema;

    public PostWork(SchemaVariable newObjectSV) {
        super(POST_WORK, (Expression) newObjectSV);
        schema = true;
    }

    /**
     * Used to create this Java statement programmatically. Do not use in taclet meta constructs!
     *
     * @param pv The {@link ProgramVariable}
     */
    public PostWork(ProgramVariable pv) {
        super(POST_WORK, pv);
        schema = false;
    }

    /**
     * performs the program transformation needed for symbolic program transformation
     *
     * @return the transformated program
     */
    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {
        final ProgramVariable newObject =
            schema ? (ProgramVariable) svInst.getInstantiation((SchemaVariable) body())
                    : (ProgramVariable) body();

        final ProgramVariable initialized = services.getJavaInfo().getAttribute(
            ImplicitFieldAdder.IMPLICIT_INITIALIZED, services.getJavaInfo().getJavaLangObject());
        return new ProgramElement[] { KeYJavaASTFactory.assign(
            KeYJavaASTFactory.fieldReference(newObject, initialized), BooleanLiteral.TRUE) };
    }
}
