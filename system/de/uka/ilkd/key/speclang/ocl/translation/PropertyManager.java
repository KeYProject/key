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

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.speclang.translation.SLResolverManager;
import de.uka.ilkd.key.speclang.translation.SLCollection;
import de.uka.ilkd.key.speclang.translation.SLExpression;


/**
 * Resolves property calls of any kind. 
 * Keeps a stack of namespaces to deal with several levels of local variables 
 * (e.g. "self", or iterator variables in forall() or select() subtrees).
 */
class PropertyManager extends SLResolverManager {
    
    public PropertyManager(Services services, KeYJavaType specInClass, FormulaBoolConverter fbc, ParsableVariable excVar) {
        super(services.getJavaInfo(), specInClass, true, true, true);
        resolvers = resolvers.append(new OCLAttributeResolver(services, this));
        resolvers = resolvers.append(new OCLMethodResolver(services, fbc, this));
        resolvers = resolvers.append(new BuiltInPropertyResolver(services, excVar, this));
        // AssociationResolver does not work without Together! (needs UMLInfo)
        //resolvers = resolvers.append(new AssociationResolver(services, this));
    }
    
   
    public SLExpression createSLExpression(Term t) {
        return new OCLEntity(t);
    }


    public SLExpression createSLExpression(KeYJavaType t) {
        return new OCLEntity(t);
    }


    public SLExpression createSLExpression(SLCollection c) {
        return new OCLEntity(OCLCollection.convertToOCLCollection(c));
    }
}
