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

package de.uka.ilkd.key.util.removegenerics;

import recoder.CrossReferenceServiceConfiguration;
import recoder.abstraction.Type;
import recoder.java.declaration.TypeArgumentDeclaration;
import recoder.java.reference.TypeReference;
import recoder.kit.ProblemReport;
import recoder.kit.TypeKit;
import recoder.list.generic.ASTList;
import recoder.service.CrossReferenceSourceInfo;

/**
 * Handle a type reference in the generic deletion process.
 * 
 * If the type reference references a type avar or an array over tv, it must be
 * replaced. if the type var is ("extends"-) bounded than <b>with the first
 * boundary(!)</b> otherwise with java.lang.Object.
 * 
 * @author MU
 * 
 */

public class ResolveTypeReference extends GenericResolutionTransformation {

    private TypeReference reference;

    private TypeReference replaceWith;

    private CrossReferenceSourceInfo sourceInfo;

    public ResolveTypeReference(TypeReference reference, CrossReferenceServiceConfiguration sc) {
        super(sc);
        this.reference = reference;
        sourceInfo = sc.getCrossReferenceSourceInfo();
    }

    @Override
    public ProblemReport analyze() {
        ASTList<TypeArgumentDeclaration> typeArguments = reference.getTypeArguments();
        if (typeArguments != null && !typeArguments.isEmpty()) {
            return EQUIVALENCE;
        }

        Type type = sourceInfo.getType(reference);

        Type replaceType = targetType(type);
        
        if(replaceType != null && !replaceType.equals(type)) {
            replaceWith = TypeKit.createTypeReference(getProgramFactory(), replaceType);
            return EQUIVALENCE;
        }

        return IDENTITY;
    }

    @Override
    public void transform() {
        if (replaceWith != null) {
            replace(reference, replaceWith);
        } else {
            reference.setTypeArguments(null);
        }
    }

}