// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang.translation;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.TermBuilder;


public abstract class SLExpressionResolver {
    
    protected static final TermBuilder TB = TermBuilder.DF;

    protected final JavaInfo javaInfo;
    protected final Services services;
    protected final SLResolverManager manager;
    

    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    public SLExpressionResolver(JavaInfo javaInfo, SLResolverManager manager) {
        assert javaInfo != null;
        assert manager  != null;
        
        this.javaInfo = javaInfo;
        this.services = javaInfo.getServices();
        this.manager = manager;
    }
    
    

    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    protected abstract boolean canHandleReceiver(SLExpression receiver);    

    protected abstract SLExpression doResolving(SLExpression receiver,
                                		String name, 
                                		SLParameters parameters) 
    	throws SLTranslationException;
    
    


    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    /**
     * Resolves property calls on explicit receivers.
     * @param receiver receiver (may *not* be null)
     * @param name name of the property
     * @param parameters the actual parameters, or null if not applicable
     * @return a suitable term or collection if successful, null otherwise
     * @throws SLTranslationException 
     */    
    public SLExpression resolve(SLExpression receiver,
                                String name,
                                SLParameters parameters) throws SLTranslationException {
        if (!canHandleReceiver(receiver)) {
            return null;
        }
        return doResolving(receiver, name, parameters);
    }
}
