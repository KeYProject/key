// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang.ocl;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.speclang.*;
import de.uka.ilkd.key.speclang.ocl.translation.OCLSpecFactory;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;


/**
 * Extracts OCL class invariants and operation contracts from OCL comments.
 * This is the public interface to the ocl package. 
 */
public class OCLSpecExtractor implements SpecExtractor {
    
    private final Services services;
    private final OCLSpecFactory osf;
    

    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    public OCLSpecExtractor(Services services) {
        this.services = services;
        this.osf = new OCLSpecFactory(services);
    }
    
    

    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private String shorten(String s) {
        int lineEndIndex = s.indexOf("\n");
        if(lineEndIndex >= 0) {
            String startString = s.substring(0, lineEndIndex);
            String restString = s.substring(lineEndIndex).trim();
            if(restString.startsWith("*")) {
                restString = restString.substring(1).trim();
            }
            if(restString.startsWith("@") | restString.startsWith("/")) {
                return startString;
            } else {
                return startString.concat(" " + shorten(restString));
            }
        } else {
            int commentEndIndex = s.indexOf("*/");
            if(commentEndIndex >= 0) {
                return s.substring(0, commentEndIndex);
            } else {
                return s;
            }
        }        
    }
    
    
    private String extractProperty(String comment, String keyword) { 
        int beginIndex = comment.indexOf(keyword);
        if(beginIndex >= 0) {
            comment = comment.substring(beginIndex + keyword.length());
            comment = shorten(comment);
            return comment;
        } else {
            return null;
        }
    }
    
    

    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
   
    public ImmutableSet<OperationContract> extractOperationContracts(ProgramMethod pm) 
            throws SLTranslationException {
        if(((TypeDeclaration) pm.getContainerType()
                                .getJavaType()).isLibraryClass()) {
            return DefaultImmutableSet.<OperationContract>nil();
        }
        
        ImmutableSet<OperationContract> result = DefaultImmutableSet.<OperationContract>nil();

        Comment[] comments = pm.getComments();
        for (Comment comment : comments) {
            String originalPre = extractProperty(comment.getText(),
                    "@preconditions");
            String originalPost = extractProperty(comment.getText(),
                    "@postconditions");
            String originalModifies = extractProperty(comment.getText(),
                    "@modifies");
            if (originalPre != null
                    || originalPost != null
                    || originalModifies != null) {
                ImmutableSet<OperationContract> contracts
                        = osf.createOCLOperationContracts(pm,
                        originalPre,
                        originalPost,
                        originalModifies);
                result = result.union(contracts);
            }
        }

        return result;          
    }
    
    

    public ImmutableSet<ClassInvariant> extractClassInvariants(KeYJavaType kjt) 
            throws SLTranslationException {
        if(!(kjt.getJavaType() instanceof TypeDeclaration)) {
            return DefaultImmutableSet.<ClassInvariant>nil();
        }
        TypeDeclaration td = (TypeDeclaration) kjt.getJavaType(); 
        if(td.isLibraryClass()) {
            return DefaultImmutableSet.<ClassInvariant>nil();
        } 
                
        ImmutableSet<ClassInvariant> result = DefaultImmutableSet.<ClassInvariant>nil();
        
        int numChildren = td.getChildCount();        
        for(int i = 0; i < numChildren; i++) {
            Comment[] comments = ((TypeDeclaration)kjt.getJavaType()).getChildAt(i).getComments();
            for (Comment comment : comments) {
                String originalInv = extractProperty(comment.getText(),
                        "@invariants");

                if (originalInv != null) {
                    ClassInvariant inv
                            = osf.createOCLClassInvariant(kjt, originalInv);
                    result = result.add(inv);
                }
            }
        }

        return result; 
    }
    
    
    public LoopInvariant extractLoopInvariant(ProgramMethod pm, LoopStatement loop) 
            throws SLTranslationException {
        return null; //OCL has no loop invariants
    }



    public ImmutableSet<PositionedString> getWarnings() {
        //graceful treatment of unsupported features for OCL not implemented
        return DefaultImmutableSet.<PositionedString>nil(); 
    }
}
