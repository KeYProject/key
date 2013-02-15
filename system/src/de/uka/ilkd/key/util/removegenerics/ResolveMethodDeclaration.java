// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.util.removegenerics;

import recoder.CrossReferenceServiceConfiguration;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.declaration.TypeParameterDeclaration;
import recoder.kit.ProblemReport;
import recoder.list.generic.ASTList;

class ResolveMethodDeclaration extends GenericResolutionTransformation {

    private MethodDeclaration declaration;

    public ResolveMethodDeclaration(MethodDeclaration declaration, CrossReferenceServiceConfiguration sc) {
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

        if(getProblemReport() == IDENTITY)
            return;
        
        declaration.setTypeParameters(null);
        
    }
}
