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


package de.uka.ilkd.key.speclang.jml;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.FieldDeclaration;
import de.uka.ilkd.key.java.declaration.FieldSpecification;
import de.uka.ilkd.key.java.declaration.MemberDeclaration;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.declaration.Modifier;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.util.MiscTools;

/**
 * Helper class used by the JML translation. Provides methods that look for
 * certain keywords (such as "pure") in comments, and that help in desugaring
 * such keywords.
 */
public final class JMLInfoExtractor {
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    /**
     * Checks whether "comment" is a JML comment containing "key".
     * see bugreport #1166
     */
    private static boolean checkFor(String key, String comment) {
        int index = comment.indexOf(key);
	boolean result = MiscTools.isJMLComment(comment) && index >= 0;
	return result;
    }    
    
    
    /**
     * Checks whether one of the passed comments is a JML comment 
     * containing "key".
     */    
    private static boolean checkFor(String key, ImmutableList<Comment> coms) {
        for(Comment c : coms) {
            if(checkFor(key, c.getText())) {
                return true;
            }
        }
        return false;
    }
    
    
    
    private static boolean hasJMLModifier(TypeDeclaration td, String mod) {
        ImmutableList<Comment> coms = ImmutableSLList.<Comment>nil();
        
        // Either mod is attached to the declaration itself ...
        coms = coms.prepend(td.getComments());
        
        // ... or to a modifier ...
        for(Modifier m : td.getModifiers()) {
            coms = coms.prepend(m.getComments());
        } 
        
        // ... or to the name
        if(td.getProgramElementName() != null) {
            coms = coms.prepend(td.getProgramElementName().getComments());
        }
        
        return checkFor(mod, coms);
    }    
    

    
    private static boolean hasJMLModifier(IProgramMethod pm, String mod) {
        ImmutableList<Comment> coms = ImmutableSLList.<Comment>nil();
        final MethodDeclaration method = pm.getMethodDeclaration();
        
        // Either mod is attached to the method itself ...
        Comment[] methodComments = method.getComments();
        if(methodComments.length > 0) {
            coms = coms.prepend(methodComments[methodComments.length - 1]);
        }        
        
        // ... or to a modifier ...
        for(Modifier m : method.getModifiers()) {
            coms = coms.prepend(m.getComments());
        }
        
        // ... or to the return type ...
        if(!pm.isVoid() && !pm.isConstructor()) {
            coms = coms.prepend(method.getTypeReference().getComments());
        }
        
        // ... or to 'void' ...
        if(method.getVoidComments() != null) {
            coms = coms.prepend(method.getVoidComments());
        }
        
        // ... or to the method name
        coms = coms.prepend(method.getProgramElementName().getComments());        
        
        return checkFor(mod, coms);
    }    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    public static boolean hasJMLModifier(FieldDeclaration fd, String mod) {
        ImmutableList<Comment> coms = ImmutableSLList.<Comment>nil();
	
	// Either mod is attached to the declaration itself ...
        coms = coms.prepend(fd.getComments());
                
        // ... or to a modifier ...
        for(Modifier m : fd.getModifiers()) {
            coms = coms.prepend(m.getComments());
        } 
        
        // ... or to the type
        coms = coms.prepend(fd.getTypeReference().getComments());
        
        return checkFor(mod, coms);
    }
    
    
    /**
     * Returns true iff the given type is specified as pure, i.e. all
     * methods and constructors are by default specified "pure"
     * 
     * If t is not a reference type, false is returned.
     */
    public static boolean isPureByDefault(KeYJavaType t) {
        if(!(t.getJavaType() instanceof TypeDeclaration)) {
            return false;
        } else {
            return hasJMLModifier((TypeDeclaration)t.getJavaType(), "pure");
        }
    }
    
    /**
     * Returns true iff the given type is specified as pure, i.e. all
     * methods and constructors are by default specified "strictly_pure"
     * 
     * If t is not a reference type, false is returned.
     */
    public static boolean isStrictlyPureByDefault(KeYJavaType t) {
        if(!(t.getJavaType() instanceof TypeDeclaration)) {
            return false;
        } else {
            return hasJMLModifier((TypeDeclaration)t.getJavaType(), "strictly_pure");
        }
    }

    
    /**
     * Returns true if the given type is specified as nullable, i.e. all fields
     * and method parameters are by default specified "nullable"
     * 
     * If t is not a reference type, false is returned.
     */
    public static boolean isNullableByDefault(KeYJavaType t) {
        if(!(t.getJavaType() instanceof TypeDeclaration)) {
            return false;
        } else{
            return hasJMLModifier((TypeDeclaration)t.getJavaType(), 
        	    	          "nullable_by_default");
        }
    }    
    

    /**
     * Returns true, if <tt>containingClass</tt> is a reference Type and has a 
     * field declaration with name <tt>fieldName</tt>, which is explicitly or 
     * implicitly declared "nullable"
     */
    public static boolean isNullable(String fieldName,
	    			     KeYJavaType containingClass) {

        if(!(containingClass.getJavaType() instanceof TypeDeclaration)) {
            return false;
        }

        TypeDeclaration td = (TypeDeclaration) containingClass.getJavaType();
        FieldDeclaration fd = null;
        int position = 0;

        for(final MemberDeclaration md : td.getMembers()) {
            if (md instanceof FieldDeclaration) {
                FieldDeclaration tmp = (FieldDeclaration) md;
                ImmutableArray<FieldSpecification> aofs 
                	= tmp.getFieldSpecifications();
                for(int j = 0; j < aofs.size(); j++) {
                    if(aofs.get(j).getProgramName().equals(fieldName)) {
                        fd = tmp;
                        position = j;
                    }
                }
            }
        }

        if(fd == null) {
            // Field not found
            return false;
        }

        ImmutableList<Comment> comments = ImmutableSLList.<Comment>nil();

        comments = comments.prepend(fd.getComments());
        comments = comments.prepend(fd.getTypeReference().getComments());
        comments = comments.prepend(fd.getFieldSpecifications()
        	                      .get(position).getComments());
        
        for(Modifier mod : fd.getModifiers()) {
            comments = comments.prepend(mod.getComments());
        }

        boolean non_null = checkFor("non_null", comments);
        boolean nullable = checkFor("nullable", comments);

        if(!non_null && !nullable) {
            return isNullableByDefault(containingClass);
        } else {
            return nullable;
        }
    }
    
    
   
    /**
     * Returns true iff the <code>pos</code>-th parameter of the given method
     * is declared "nullable" (implicitly or explicitly). 
     */
    public static boolean parameterIsNullable(IProgramMethod pm, int pos) {
        MethodDeclaration md = pm.getMethodDeclaration();
        ParameterDeclaration pd = md.getParameterDeclarationAt(pos);

        return parameterIsNullable(pm, pd);
    }


    /**
     * Returns true iff the parameter of the given method
     * is declared "nullable" (implicitly or explicitly). 
     * Warning: weird things may happen if the parameter doesn't belong to the method.
     */
    public static boolean parameterIsNullable(IProgramMethod pm,
            ParameterDeclaration pd) {
	assert pm.getMethodDeclaration().getParameters().contains(pd): "parameter "+pd+" does not belong to method declaration "+pm;
	ImmutableList<Comment> comments = ImmutableSLList.<Comment>nil();
        comments = comments.prepend(pd.getComments());
        comments = comments.prepend(pd.getTypeReference().getComments());
        comments = comments.prepend(pd.getVariableSpecification()
        	                      .getComments());
        for(Modifier mod : pd.getModifiers()) {
            comments = comments.prepend(mod.getComments());
        }
        
        boolean non_null = checkFor("non_null", comments);
        boolean nullable = checkFor("nullable", comments);
        
        if(!non_null && !nullable) {
            return isNullableByDefault(pm.getContainerType());
        } else {
            return nullable;
        }
    }
    
    
    public static boolean resultIsNullable(IProgramMethod pm) {
        MethodDeclaration md = pm.getMethodDeclaration();
        
        ImmutableList<Comment> comments = ImmutableSLList.<Comment>nil();
        for(Modifier mod : md.getModifiers()) {
            comments = comments.prepend(mod.getComments());
        }
        if(!pm.isVoid() && !pm.isConstructor()) {
            comments = comments.prepend(md.getTypeReference().getComments());
        }
        Comment[] methodComments = md.getComments();
        if(methodComments.length > 0) {
            comments
            	= comments.prepend(methodComments[methodComments.length - 1]);
        }
        
        boolean non_null = checkFor("non_null", comments);
        boolean nullable = checkFor("nullable", comments);
        
        if(!non_null && !nullable) {
            return isNullableByDefault(pm.getContainerType());
        } else {
            return nullable;
        }
    }
    
    
    /**
     * Returns true iff the given method is specified "pure".
     */
    public static boolean isPure(IProgramMethod pm) {
        return hasJMLModifier(pm, "pure") 
               || isPureByDefault(pm.getContainerType());
    }
    
    
    /**
     * Returns true iff the given method is specified "helper".
     */
    public static boolean isHelper(IProgramMethod pm) {
	return hasJMLModifier(pm, "helper");
    }

    /**
     * Returns true iff the given method is specified "strictly_pure"
     * or the containing type is specified so.
     */
    public static boolean isStrictlyPure(IProgramMethod pm) {
        return hasJMLModifier(pm, "strictly_pure") 
                || isStrictlyPureByDefault(pm.getContainerType());
    }
}
