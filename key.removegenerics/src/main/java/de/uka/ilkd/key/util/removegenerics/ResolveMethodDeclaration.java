/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util.removegenerics;

import recoder.CrossReferenceServiceConfiguration;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.declaration.TypeParameterDeclaration;
import recoder.kit.ProblemReport;
import recoder.list.generic.ASTList;

class ResolveMethodDeclaration extends GenericResolutionTransformation {

    private final MethodDeclaration declaration;

    public ResolveMethodDeclaration(MethodDeclaration declaration,
            CrossReferenceServiceConfiguration sc) {
        super(sc);
        this.declaration = declaration;
    }

    @Override
    public ProblemReport analyze() {
        ASTList<TypeParameterDeclaration> typeParameters = declaration.getTypeParameters();
        if (typeParameters == null || typeParameters.isEmpty()) {
            setProblemReport(IDENTITY);
        } else {
            setProblemReport(EQUIVALENCE);
        }

        return getProblemReport();
    }

    @Override
    public void transform() {

        if (getProblemReport() == IDENTITY) {
            return;
        }

        declaration.setTypeParameters(null);

    }
}
