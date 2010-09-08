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
import de.uka.ilkd.key.java.declaration.MemberDeclaration;
import de.uka.ilkd.key.java.declaration.modifier.Private;
import de.uka.ilkd.key.java.declaration.modifier.Protected;
import de.uka.ilkd.key.java.declaration.modifier.Public;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.java.reference.PackageReference;

public abstract class SLExpressionResolver {

    protected final JavaInfo javaInfo;
    protected final SLResolverManager manager;
    protected final KeYJavaType specInClass;
    
    public SLExpressionResolver(JavaInfo javaInfo, 
	    			SLResolverManager manager,
	    			KeYJavaType specInClass) {
        assert javaInfo != null;
        assert manager != null;
        assert specInClass != null;
        
        this.javaInfo = javaInfo;
        this.manager = manager;
        this.specInClass = specInClass;
    }
    
    
    private boolean areInSamePackage(KeYJavaType kjt1, KeYJavaType kjt2) {
	final PackageReference p1 = kjt1.createPackagePrefix();
	final PackageReference p2 = kjt2.createPackagePrefix();
	if(p1 == null) {
	    return p2 == null;
	} else if(p2 == null) {
	    return false;
	} else {
	    return p1.equals(p2);
	}
    }    
    
    
    /** 
     * Checks whether the passed member, contained in the passed type, 
     * is visible in specInClass.
     */
    protected final boolean isVisible(MemberDeclaration md, 
	    			      KeYJavaType containingType) {
	//use spec visibility
	VisibilityModifier mod = manager.getSpecVisibility(md);
	
	//no spec visibility? -> use ordinary Java visibility
	if(mod == null) {
	    if(md.isPublic()) {
		mod = new Public();
	    } else if(md.isProtected()) {
		mod = new Protected();
	    } else if(md.isPrivate()) {
		mod = new Private();
	    }
	}
	
	//check according to visibility rules
	if(mod instanceof Public) {
	    return true;
	} else if(mod instanceof Protected) {
	    return specInClass.getSort().extendsTrans(containingType.getSort())
	           || areInSamePackage(specInClass, containingType);
	} else if(mod instanceof Private) {
	    return specInClass.equals(containingType);
	} else {
	    return areInSamePackage(specInClass, containingType);
	}	
    }
    
    
    /**
     * Resolves property calls on explicit receivers.
     * @param receiver receiver (may *not* be null)
     * @param name name of the property
     * @param parameters the actual parameters, or null if not applicable
     * @return a suitable term or collection if successful, null otherwise
     * @throws SLTranslationException 
     */
    protected abstract SLExpression doResolving(SLExpression receiver,
                                String name, 
                                SLParameters parameters) throws SLTranslationException;
    
    
    public final SLExpression resolve(SLExpression receiver,
                                String name,
                                SLParameters parameters) throws SLTranslationException {
        if (!canHandleReceiver(receiver)) {
            return null;
        }
        return doResolving(receiver, name, parameters);
    }
    
    
    protected abstract boolean canHandleReceiver(SLExpression receiver);    
    public abstract boolean needVarDeclaration(String name);
}
