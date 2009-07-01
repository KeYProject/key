// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.speclang.translation;

import de.uka.ilkd.key.explicitheap.ExplicitHeapConverter;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;

public class SLAttributeResolver extends SLExpressionResolver {

    private static final ExplicitHeapConverter EHC = ExplicitHeapConverter.INSTANCE;

    
    public SLAttributeResolver(JavaInfo javaInfo, SLResolverManager manager) {
        super(javaInfo, manager);
    }
    
    protected SLExpression doResolving(SLExpression receiver, String name,
            SLParameters parameters) throws SLTranslationException {

        if (parameters != null) {
            return null;
        }
        Term recTerm = receiver.getTerm();        
        ProgramVariable attribute=null;
        try {
            //try as fully qualified name
            attribute = javaInfo.getAttribute(name);
        } catch(IllegalArgumentException e){
            //try as short name and in enclosing classes
            KeYJavaType containingType = receiver.getKeYJavaType(javaInfo);
            while(attribute==null){
                attribute = javaInfo.lookupVisibleAttribute(name, containingType);
                if(attribute==null){
                    attribute = javaInfo.lookupVisibleAttribute(
                            ImplicitFieldAdder.FINAL_VAR_PREFIX+name, containingType);
                }
                ProgramVariable et = javaInfo.getAttribute(
                        ImplicitFieldAdder.IMPLICIT_ENCLOSING_THIS, containingType);
                if(et!=null && attribute==null){
                    containingType = et.getKeYJavaType();
                    if(recTerm!=null){
                	final Function fieldSymbol = EHC.getFieldSymbol(et, services);
                        recTerm = TB.dot(services, et.sort(), recTerm, fieldSymbol);
                    }
                }else{
                    break;
                }
            }
        }
        
        if(attribute != null) {
            if(recTerm == null && !attribute.isStatic()) {
                throw manager.excManager.createException(
                        "Reference to non-static field without receiver: " +
                        attribute.name());
            }
            try {
        	final Function fieldSymbol = EHC.getFieldSymbol(attribute, services);
        	Term attributeTerm;
        	if(attribute.isStatic()) {
        	    attributeTerm = TB.staticDot(services, attribute.sort(), fieldSymbol);
        	} else {
        	    attributeTerm = TB.dot(services, attribute.sort(), recTerm, fieldSymbol);
        	}
                return manager.createSLExpression(attributeTerm);
            } catch (TermCreationException e) {
                throw manager.excManager.createException(
                        "Wrong attribute reference " + name + ".");
            }
        }   
    
        return null;

    }

    public boolean canHandleReceiver(SLExpression receiver) {
        return receiver != null && (receiver.isTerm() || receiver.isType());
    }

    public boolean needVarDeclaration(String name) {
        return false;
    }

}
