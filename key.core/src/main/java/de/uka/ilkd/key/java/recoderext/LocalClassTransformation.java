/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import java.util.List;

import recoder.CrossReferenceServiceConfiguration;
import recoder.abstraction.Variable;
import recoder.java.ProgramElement;
import recoder.java.declaration.ClassDeclaration;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.reference.FieldReference;
import recoder.java.reference.ThisReference;
import recoder.java.reference.VariableReference;
import recoder.kit.ProblemReport;
import recoder.service.CrossReferenceSourceInfo;

/**
 * Local and anonymous classes may access variables from the creating context if they are declared
 * final and initialised.
 *
 * This transformation searches for such final variables and replaces them by an implicit variable.
 *
 * Additionally a pseudo name is assigned to anonymous classes to allow to access them despite all.
 *
 * @author engelc
 */
public class LocalClassTransformation extends RecoderModelTransformer {

    public LocalClassTransformation(CrossReferenceServiceConfiguration services,
            TransformerCache cache) {
        super(services, cache);
    }

    public ProblemReport analyze() {
        for (final ClassDeclaration cd : classDeclarations()) {
            if (cd.getName() == null || cd.getStatementContainer() != null) {
                (new FinalOuterVarsCollector()).walk(cd);
            }
        }
        return super.analyze();
    }

    protected void makeExplicit(TypeDeclaration td) {
        List<Variable> outerVars = getLocalClass2FinalVar().get(td);
        CrossReferenceSourceInfo si = services.getCrossReferenceSourceInfo();

        if (outerVars != null) {
            for (final Variable v : outerVars) {
                for (final VariableReference vr : si.getReferences(v)) {
                    if (si.getContainingClassType(vr) != si
                            .getContainingClassType((ProgramElement) v)) {
                        FieldReference fr =
                            new FieldReference(new ThisReference(), new ImplicitIdentifier(
                                ImplicitFieldAdder.FINAL_VAR_PREFIX + v.getName()));
                        vr.getASTParent().replaceChild(vr, fr);
                        td.makeAllParentRolesValid();
                    }
                }
            }
        }
    }

}
