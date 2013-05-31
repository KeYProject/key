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


package de.uka.ilkd.key.speclang.translation;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.MemberDeclaration;
import de.uka.ilkd.key.java.declaration.modifier.Private;
import de.uka.ilkd.key.java.declaration.modifier.Protected;
import de.uka.ilkd.key.java.declaration.modifier.Public;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.java.reference.PackageReference;
import de.uka.ilkd.key.logic.TermBuilder;

/**
 * Expression resolvers are used by specification parsers (e.g. for JML
 * or OCL) to translate complex expressions to terms. Subclasses of this
 * abstract base class deal with specific operators that may occur in
 * specification expressions.
 */
public abstract class SLExpressionResolver {
    
    protected static final TermBuilder TB = TermBuilder.DF;        

    protected final JavaInfo javaInfo;
    protected final Services services;
    protected final SLResolverManager manager;
    protected final KeYJavaType specInClass;
    
    public SLExpressionResolver(JavaInfo javaInfo, 
	    			SLResolverManager manager,
	    			KeYJavaType specInClass) {
        assert javaInfo != null;
        assert manager != null;
        assert specInClass != null;
        
        this.javaInfo = javaInfo;
        this.services = javaInfo.getServices();
        this.manager = manager;
        this.specInClass = specInClass;
    }
    

    /**
     * Cuts off names of enclosing classes from a "package reference". 
     * Helper for areInSamePackage().
     */
    private String trimPackageRef(String ref) {
        if(ref == null || javaInfo.isPackage(ref)) {
	    return ref;
        }
	
        int i = ref.lastIndexOf(".");
        if(i < 0) { 
            return null;
        } else {
	    return trimPackageRef(ref.substring(0, i));
        }
    }
    
    
    /**
     * Helper for isVisible().
     */
    private boolean areInSamePackage(KeYJavaType kjt1, KeYJavaType kjt2) {
	final PackageReference p1 = kjt1.createPackagePrefix();
	final PackageReference p2 = kjt2.createPackagePrefix();
        final String ps1 = trimPackageRef(p1 == null ? null : p1.toString());
        final String ps2 = trimPackageRef(p2 == null ? null : p2.toString());

	if(ps1 == null) {
	    return ps2 == null;
	} else if(ps2 == null) {
	    return false;
	} else {
	    return ps1.equals(ps2);
	}
    }
    
    
    /**
     * Helper for isVisible().
     */
    private final boolean isVisibleHelper(MemberDeclaration md,
	                                  KeYJavaType containingType,
	                                  KeYJavaType inType) {
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
	    return inType.getSort().extendsTrans(containingType.getSort())
	           || areInSamePackage(inType, containingType);
	} else if(mod instanceof Private) {
	    return inType.equals(containingType);
	} else {
	    return areInSamePackage(inType, containingType);
	}	
    }
    
    
    /** 
     * Checks whether the passed member, contained in the passed type, 
     * is visible in specInClass.
     */
    protected final boolean isVisible(MemberDeclaration md, 
	    			      KeYJavaType containingType) {
	//visible in specInClass directly?
	KeYJavaType inType = specInClass;
	boolean result = isVisibleHelper(md, containingType, inType);
	
	//visible in enclosing classes of specInClass?
	while(!result) {
	    final PackageReference p = inType.createPackagePrefix();
	    if(p == null || javaInfo.isPackage(p.toString())) {
		break;
	    }
	    inType = javaInfo.getTypeByClassName(p.toString());
	    assert inType != null;
	    result = isVisibleHelper(md, containingType, inType);
	}
	
	return result;
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
}
