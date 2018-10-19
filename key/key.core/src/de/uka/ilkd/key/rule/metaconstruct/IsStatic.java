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

import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.VariableReference;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Creates a true or false literal if the given program element is or is not a
 * static variable reference.
 *
 * @author N/A
 */
public class IsStatic extends ProgramTransformer {

    /**
     * creates a typeof ProgramTransformer
     *
     * @param pe
     *            the instance of expression contained by the meta construct
     */
    public IsStatic(ProgramElement pe) {
        super("#isstatic", pe);
    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {
        if (pe instanceof VariableReference) {
            if (((VariableReference) pe).getProgramVariable().isStatic()) {
                return new ProgramElement[] { KeYJavaASTFactory.trueLiteral() };
            }
        }
        return new ProgramElement[] { KeYJavaASTFactory.falseLiteral() };
    }
}