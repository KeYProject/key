// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.speclang.translation;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;

public final class SLAttributeResolver extends SLExpressionResolver {

    
    public SLAttributeResolver(JavaInfo javaInfo, SLResolverManager manager) {
        super(javaInfo, manager);
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
            return new SLExpression(TB.inv(services, receiver.getTerm()));
        }
        
        ProgramVariable attribute = null;
        try {
            //try as fully qualified name
            attribute = javaInfo.getAttribute(name);
        } catch(IllegalArgumentException e){
            //try as short name and in enclosing classes
            KeYJavaType containingType = receiver.getType();
            while(attribute == null){
                attribute = javaInfo.lookupVisibleAttribute(name, 
                	                                    containingType);
                if(attribute == null){
                    attribute 
                    	= javaInfo.lookupVisibleAttribute(ImplicitFieldAdder.FINAL_VAR_PREFIX+name, containingType);
                }
                LocationVariable et 
                	= (LocationVariable) javaInfo.getAttribute(ImplicitFieldAdder.IMPLICIT_ENCLOSING_THIS, 
                					           containingType);
                if(et != null && attribute == null){
                    containingType = et.getKeYJavaType();
                    if(recTerm != null){
                	final Function thisFieldSymbol 
                		= heapLDT.getFieldSymbolForPV(et, services);
                        recTerm = TB.dot(services, et.sort(), recTerm, thisFieldSymbol);
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
        	return new SLExpression(TB.var(attribute), 
        				attribute.getKeYJavaType());
            } else {
        	try {
        	    final Function fieldSymbol 
        	    	= heapLDT.getFieldSymbolForPV((LocationVariable)
        	    		                         attribute, 
        	    		                       services);
        	    Term attributeTerm;
        	    if(attribute.isStatic()) {
        		attributeTerm = TB.staticDot(services, 
        					     attribute.sort(), 
        					     fieldSymbol);
        	    } else {
        		attributeTerm = TB.dot(services, 
        				       attribute.sort(), 
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
