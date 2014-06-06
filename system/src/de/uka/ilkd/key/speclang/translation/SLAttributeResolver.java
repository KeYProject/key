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

package de.uka.ilkd.key.speclang.translation;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.FieldDeclaration;
import de.uka.ilkd.key.java.declaration.FieldSpecification;
import de.uka.ilkd.key.java.declaration.MemberDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;

/**
 * Resolver for attributes (i.e., fields). 
 */
public final class SLAttributeResolver extends SLExpressionResolver {
    
    public SLAttributeResolver(JavaInfo javaInfo, 
	    		       SLResolverManager manager,
	    		       KeYJavaType specInClass) {
        super(javaInfo, manager, specInClass);
    }
    
    
    private ProgramVariable lookupVisibleAttribute(String name,
	    					   KeYJavaType containingType) {
	final TypeDeclaration td
		= (TypeDeclaration) containingType.getJavaType();
	//lookup locally
	for(MemberDeclaration md : td.getMembers()) {
	    if(md instanceof FieldDeclaration
		    && isVisible(md, containingType)) {
		for(FieldSpecification fs
			: ((FieldDeclaration)md).getFieldSpecifications()) {
		    if(fs.getProgramName().equals(name)) {
			return (ProgramVariable) fs.getProgramVariable();
		    }
		}
	    }
	}

	//recursively lookup in supertypes
	ImmutableList<KeYJavaType> sups = td.getSupertypes();
	if(sups.isEmpty()
		&& !containingType.equals(javaInfo.getJavaLangObject())) {
	    sups = sups.prepend(javaInfo.getJavaLangObject());
	}
	for(KeYJavaType sup : sups) {
	    final ProgramVariable res = lookupVisibleAttribute(name, sup);
	    if(res != null) {
		return res;
	    }
	}

	//not found
	return null;
    }    
    

    @Override
    protected boolean canHandleReceiver(SLExpression receiver) {
        return receiver != null;
    }    
    
    
    @Override
    protected SLExpression doResolving(SLExpression receiver, 
	    			       String name,
	    			       SLParameters parameters) 
    		throws SLTranslationException {
	
        if(parameters != null) {
            return null;
        }
        
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT(); 
        
        Term recTerm = receiver.getTerm(); 
        
        //<inv> is special case (because it's really a predicate, not a boolean attribute)
        if(name.equals("<inv>") && receiver.isTerm()) {
            return new SLExpression(services.getTermBuilder().inv(receiver.getTerm()));
        }
        
        ProgramVariable attribute = null;
        try {
            //try as fully qualified name
            attribute = javaInfo.getAttribute(name);
        } catch(IllegalArgumentException e){
            //try as short name and in enclosing classes
            KeYJavaType containingType = receiver.getType();
            while(attribute == null) {
                attribute = lookupVisibleAttribute(name, containingType);
                if(attribute == null) {
                    attribute 
                    	= lookupVisibleAttribute(
                    		ImplicitFieldAdder.FINAL_VAR_PREFIX + name, 
                    		containingType);
                }
                final LocationVariable et 
                	= (LocationVariable) javaInfo.getAttribute(
                		ImplicitFieldAdder.IMPLICIT_ENCLOSING_THIS, 
                		containingType);
                if(et != null && attribute == null){
                    containingType = et.getKeYJavaType();
                    if(recTerm != null){
                	final Function thisFieldSymbol 
                		= heapLDT.getFieldSymbolForPV(et, services);
                        recTerm = services.getTermBuilder().dot(et.sort(), recTerm, thisFieldSymbol);
                    }
                } else {
                    break;
                }
            }
        }
        
        if(attribute != null) {
            if(recTerm == null && !attribute.isStatic()) {
                throw manager.excManager.createException(
                        "Reference to non-static field without receiver: " +
                        attribute.name());
            } else if(attribute instanceof ProgramConstant) {
        	return new SLExpression(services.getTermBuilder().var(attribute), 
        				attribute.getKeYJavaType());
            } else if(attribute == javaInfo.getArrayLength()) {
        	return new SLExpression(services.getTermBuilder().dotLength(recTerm), 
        		                attribute.getKeYJavaType());
            } else {
        	try {
        	    final Function fieldSymbol 
        	    	= heapLDT.getFieldSymbolForPV((LocationVariable)
        	    		                         attribute, 
        	    		                       services);
        	    Term attributeTerm;
        	    if(attribute.isStatic()) {
        		attributeTerm = services.getTermBuilder().staticDot(attribute.sort(), 
        					     fieldSymbol);
        	    } else {
        		attributeTerm = services.getTermBuilder().dot(attribute.sort(), 
        				       recTerm, 
        				       fieldSymbol);
        	    }
        	    return new SLExpression(attributeTerm, 
        		    		    attribute.getKeYJavaType());
        	} catch (TermCreationException e) {
        	    throw manager.excManager.createException(
        		    "Wrong attribute reference \"" + name + "\": " + e.getMessage());
        	}
            }
        }   
    
        return null;
    }
}