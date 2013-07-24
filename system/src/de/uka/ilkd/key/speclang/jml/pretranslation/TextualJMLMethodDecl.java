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


package de.uka.ilkd.key.speclang.jml.pretranslation;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.speclang.PositionedString;

/**
 * A JML model method declaration in textual form.
 */
public final class TextualJMLMethodDecl extends TextualJMLConstruct {
    
    private final PositionedString decl;
    private final String methodName;
    private final PositionedString methodDefinition;
    
    
    public TextualJMLMethodDecl(ImmutableList<String> mods, 
                                PositionedString decl, 
                                String methodName,
                                PositionedString methodDefinition) {
        super(mods);
        assert decl != null;
        this.decl = decl;
        this.methodName = methodName;
        this.methodDefinition = methodDefinition;
    }
    
    
    public PositionedString getDecl() {
        return decl;
    }
    
    
    public String getMethodName() {
        return methodName;
    }

    public PositionedString getMethodDefinition() {
    	return methodDefinition;
    }
    
    @Override
    public String toString() {
        return decl.toString();
    }
    
    
    @Override
    public boolean equals(Object o) {
        if(!(o instanceof TextualJMLMethodDecl)) {
            return false;
        }
        TextualJMLMethodDecl md = (TextualJMLMethodDecl) o;
        return mods.equals(md.mods) 
               && decl.equals(md.decl) 
               && methodDefinition.equals(md.methodDefinition) 
               && methodName.equals(md.methodName);
    }
    
    
    @Override
    public int hashCode() {
        return mods.hashCode() + decl.hashCode() + methodName.hashCode() + methodDefinition.hashCode();
    }

    public int getStateCount() {
        if(mods.contains("two_state")) { return 2; }
        if(mods.contains("no_state")) { return 0; }
        return 1;
    }

}
