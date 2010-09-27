// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.speclang.translation;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.logic.op.ProgramVariable;

public class SLTypeResolver extends SLExpressionResolver {

    public SLTypeResolver(JavaInfo javaInfo, 
	    		  SLResolverManager manager,
	    		  KeYJavaType specInClass) {
        super(javaInfo, manager, specInClass);
    }

    protected boolean canHandleReceiver(SLExpression receiver) {
        return true;
    }

    protected SLExpression doResolving(SLExpression receiver,
                                       String name,
                                       SLParameters parameters)
                                   throws SLTranslationException {
        try {
            KeYJavaType type = javaInfo.getTypeByClassName(name);
            return manager.createSLExpression(type);
        } catch (RuntimeException e) {
            try{
                if(receiver != null){ 
                    KeYJavaType containingType = receiver.getKeYJavaType(javaInfo);
                    while(true){
                        String typeName = containingType.getSort().name().toString();
                        if(typeName.substring(typeName.lastIndexOf(".")+1).equals(name)){
                            return manager.createSLExpression(containingType);
                        }
                        ProgramVariable et = javaInfo.getAttribute(
                                ImplicitFieldAdder.IMPLICIT_ENCLOSING_THIS, containingType);
                        if(et!=null){
                            containingType = et.getKeYJavaType();
                        }else{
                            break;
                        }
                    }
                }
            }catch(RuntimeException ex){ }
            // Type not found
            return null;
        }
    }

    public boolean needVarDeclaration(String name) {
        return false;
    }
}
