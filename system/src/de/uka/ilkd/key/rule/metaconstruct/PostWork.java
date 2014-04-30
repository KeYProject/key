// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

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
	super(POST_WORK, (Expression)newObjectSV);
	schema = true;
    }

    /**
     * Used to create this Java statement programmatically.
     * Do not use in taclet meta constructs!
     */
    public PostWork (ProgramVariable pv) {
        super(POST_WORK, pv);
        schema = false;
    }

    /**
     * performs the program transformation needed for symbolic
     * program transformation
     * @return the transformated program
     */
    public ProgramElement transform(ProgramElement pe,
					    Services services,
					    SVInstantiations svInst) {
	final ProgramVariable newObject =
	        schema ?
	                (ProgramVariable) svInst.getInstantiation((SchemaVariable)body())
	                : (ProgramVariable)body();

	final ProgramVariable initialized = services.getJavaInfo().getAttribute
	    (ImplicitFieldAdder.IMPLICIT_INITIALIZED,
             services.getJavaInfo().getJavaLangObject());
	return KeYJavaASTFactory.assign(
		KeYJavaASTFactory.fieldReference(newObject, initialized),
		BooleanLiteral.TRUE);
    }
}