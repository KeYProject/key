//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang.ocl.translation;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.speclang.translation.*;


class OCLResolverManager extends SLResolverManager {
    
    public OCLResolverManager(Services services,
                              KeYJavaType specInClass,
                              ParsableVariable selfVar,
                              FormulaBoolConverter fbc,
                              ParsableVariable excVar,
                              SLTranslationExceptionManager eManager) {
        super(eManager, specInClass, selfVar, true);
        JavaInfo javaInfo = services.getJavaInfo();
        addResolver(new SLAttributeResolver(javaInfo, this));
        addResolver(new SLMethodResolver(javaInfo, this));
        addResolver(new SLTypeResolver(javaInfo, this));        
        addResolver(new OCLAttributeResolver(services, this));
        addResolver(new OCLMethodResolver(services, fbc, this));
        addResolver(new BuiltInPropertyResolver(services, excVar, this));
        // AssociationResolver does not work without Together! (needs UMLInfo)
        //addResolver(new AssociationResolver(services, this));
    }
    
   
    public SLExpression createSLExpression(Term t) {
        return new OCLExpression(t);
    }


    public SLExpression createSLExpression(KeYJavaType t) {
        return new OCLExpression(t);
    }


    public SLExpression createSLExpression(SLCollection c) {
        return new OCLExpression(OCLCollection.convertToOCLCollection(c));
    }
}
