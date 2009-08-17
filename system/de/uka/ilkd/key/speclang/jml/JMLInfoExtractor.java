// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang.jml;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.logic.op.ProgramMethod;

class JMLInfoExtractor {

    // Information about Fields...
    
    /**
     * Returns true, if <tt>containingClass</tt> is a reference Type and has a field
     * declaration with name <tt>fieldName</tt>, which is explicitly or implicitly
     * declared "nullable"
     */
    public static boolean isNullable(String fieldName,
            KeYJavaType containingClass) {

        if (!(containingClass.getJavaType() instanceof TypeDeclaration)) {
            return false;
        }

        TypeDeclaration td = (TypeDeclaration) containingClass.getJavaType();
        ImmutableArray<MemberDeclaration> md = td.getMembers();
        FieldDeclaration fd = null;
        int position = 0;

        for (int i = 0; i < md.size(); i++) {
            if (md.get(i) instanceof FieldDeclaration) {
                FieldDeclaration tmp = (FieldDeclaration) md.get(i);
                ImmutableArray<FieldSpecification> aofs = tmp.getFieldSpecifications();
                for (int j = 0; j < aofs.size(); j++) {
                    if (aofs.get(j).getProgramName().equals(fieldName)) {
                        fd = tmp;
                        position = j;
                    }
                }
            }
        }

        if (fd == null) {
            // Field not found
            return false;
        }

        ImmutableList<Comment> comments = ImmutableSLList.<Comment>nil();

        comments = comments.prepend(fd.getComments());
        comments = comments.prepend(fd.getTypeReference().getComments());
        comments = comments.prepend(fd.getFieldSpecifications().get(position).getComments());
        ImmutableArray<Modifier> mods = fd.getModifiers();
        for (int i = 0; i < mods.size(); i++) {
            comments = comments.prepend(mods.get(i).getComments());
        }

        boolean non_null = false;
        boolean nullable = false;

        for (Iterator<Comment> it = comments.iterator(); it.hasNext();) {
            Comment c = it.next();
            if (checkFor("non_null", c.getText()))
                non_null = true;
            if (checkFor("nullable", c.getText()))
                nullable = true;
        }

        if (!non_null && !nullable)
            return isNullableByDefault(containingClass);

        if (nullable)
            return true;
        else
            return false;
    }
    
    
    // Information about Methods...
   
    /**
     * Returns true, iff the <code>pos</code>-th parameter of the given method
     * is declared "nullable" (implicit or explicit). 
     */
    public static boolean parameterIsNullable(ProgramMethod pm, int pos) {

        MethodDeclaration md = pm.getMethodDeclaration();
        ParameterDeclaration pd = md.getParameterDeclarationAt(pos);

        ImmutableList<Comment> comments = ImmutableSLList.<Comment>nil();
        comments = comments.prepend(pd.getComments());
        comments = comments.prepend(pd.getTypeReference().getComments());
        comments = comments.prepend(pd.getVariableSpecification().getComments());
        for (int j=0; j < pd.getModifiers().size(); j++) {
            comments = comments.prepend(pd.getModifiers().get(j).getComments());
        }
        for (Iterator<Comment> it = comments.iterator(); it.hasNext(); ) {
            Comment c = it.next();
            if (checkFor("nullable",c.getText()))
                return true;
            else if (checkFor("non_null",c.getText())) {
                return false;
            }
        }
        
        return isNullableByDefault(pm.getContainerType());
    }
    
    
    public static boolean resultIsNullable(ProgramMethod pm) {
        MethodDeclaration md = pm.getMethodDeclaration();
        
        ImmutableList<Comment> comments = ImmutableSLList.<Comment>nil();
        ImmutableArray<Modifier> mods = md.getModifiers();
        for (int i=0; i < mods.size(); i++) {
            comments = comments.prepend(mods.get(i).getComments());
        }        
        if (md.getTypeReference() != null) {
            comments = comments.prepend(md.getTypeReference().getComments());
        }
        Comment[] methodComments = md.getComments();
        if(methodComments.length > 0) {
            comments = comments.prepend(methodComments[methodComments.length - 1]);
        }

        for(Iterator<Comment> it = comments.iterator(); it.hasNext(); ) {
            Comment c = it.next();
            if(checkFor("nullable", c.getText())) {
                return true;
            } else if(checkFor("non_null", c.getText())) {
                return false;
            }
        }
        
        return isNullableByDefault(pm.getContainerType());
    }
    
    
    /**
     * Returns true, if the given method is specified "pure".
     */
    public static boolean isPure(ProgramMethod pm) {
        ImmutableList<Comment> coms = ImmutableSLList.<Comment>nil();
        MethodDeclaration method = pm.getMethodDeclaration();
        
        // Either "pure" is attached to a modifier ....
        ImmutableArray<Modifier> mods = method.getModifiers();
        for (int i=0; i < mods.size(); i++) {
            coms = coms.prepend(mods.get(i).getComments());
        }       
        
        // .... or to the return type ....
        if (method.getTypeReference() != null) {
            coms = coms.prepend(method.getTypeReference().getComments());
        }
        
        // .... or to the method itself
        Comment[] methodComments = method.getComments();
        if(methodComments.length > 0) {
            coms = coms.prepend(methodComments[methodComments.length - 1]);
        }
        
        // .... or to the method name
        coms = coms.prepend(method.getProgramElementName().getComments());
        
        for (Iterator<Comment> it = coms.iterator(); it.hasNext(); ) {
            if (checkFor("pure", it.next().getText()))
                return true;
        }
        
        return isPureByDefault(pm.getContainerType());
    }
    
    
    // Information about Types
    
    
    /**
     * Returns true if the given type is specified as pure, i.e. all
     * methods and constructors are by default specified "pure"
     * 
     * If t is not a reference type, false is returned.
     */
    public static boolean isPureByDefault(KeYJavaType t) {
        
        if (!(t.getJavaType() instanceof TypeDeclaration)) {
            return false;
        }
        
        TypeDeclaration td = (TypeDeclaration) t.getJavaType();
        
        // Collect all comments preceding the type declaration or the modifiers.
        ImmutableList<Comment> coms = ImmutableSLList.<Comment>nil();
        coms = coms.prepend(td.getComments());
        if(td.getProgramElementName() != null) {
            coms = coms.prepend(td.getProgramElementName().getComments());
        }
        ImmutableArray<Modifier> mods = td.getModifiers();
        for (int i=0; i < mods.size(); i++) {
            coms = coms.prepend(mods.get(i).getComments());
        }
        
        // Check if a comment is a JML annotation containing
        // "nullable_by_default"
        for (Iterator<Comment> it = coms.iterator(); it.hasNext(); ) {
            if (checkFor("pure", it.next().getText()))
                return true;
        }
    
        return false;
    }

    
    /**
     * Returns true if the given type is specified as nullable, i.e. all fields
     * and method parameters are by default specified "nullable"
     * 
     * If t is not a reference type, false is returned.
     */
    public static boolean isNullableByDefault(KeYJavaType t) {
        
        if (!(t.getJavaType() instanceof TypeDeclaration)) {
            return false;
        }
        
        TypeDeclaration td = (TypeDeclaration) t.getJavaType();
        
        // Collect all comments preceding the type declaration or the modifiers.
        ImmutableList<Comment> coms = ImmutableSLList.<Comment>nil();
        coms = coms.prepend(td.getComments());
        if(td.getProgramElementName() != null) {
            coms = coms.prepend(td.getProgramElementName().getComments());
        }
        ImmutableArray<Modifier> mods = td.getModifiers();
        for (int i=0; i < mods.size(); i++) {
            coms = coms.prepend(mods.get(i).getComments());
        }
        
        // Check if a comment is a JML annotation containing
        // "nullable_by_default"
        for (Iterator<Comment> it = coms.iterator(); it.hasNext(); ) {
            if (checkFor("nullable_by_default", it.next().getText()))
                return true;
        }
    
        return false;
    }
    
    
    //---------------- Helper methods ----------------------//
    
    /**
     * Checks whether <code>comment</code> is a JML comment of the form
     * \/* <code>key</code> *\/.
     */
    private static boolean checkFor(String key, String comment) {
        if (comment.length() < key.length() + 3 )
            return false;
        
        String c;
        // Check if it is a JML comment
        if (comment.startsWith("/*@"))
            c = comment.substring(3);
        else
            return false;
        
        // Check for the key
        if (c.trim().indexOf(key) >= 0)
            return true;
        
        return false;
    }

}
