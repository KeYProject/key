// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.


package de.uka.ilkd.key.speclang.jml.pretranslation;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.speclang.PositionedString;


public class TextualJMLLoopSpec extends TextualJMLConstruct {

    private ImmutableList<PositionedString> invariant          
            = ImmutableSLList.<PositionedString>nil();
    private ImmutableList<PositionedString> skolemDeclarations 
            = ImmutableSLList.<PositionedString>nil();
    private ImmutableList<PositionedString> predicates         
            = ImmutableSLList.<PositionedString>nil();
    private ImmutableList<PositionedString> assignable         
            = ImmutableSLList.<PositionedString>nil();
    private PositionedString variant                  
            = null;
    
    
    public TextualJMLLoopSpec(ImmutableList<String> mods) {
        super(mods);
    }

       
    public void addInvariant(PositionedString ps) {
        invariant = invariant.append(ps);
    }
    
    
    public void addSkolemDeclaration(PositionedString ps) {
        skolemDeclarations = skolemDeclarations.append(ps);
    }
    
    
    public void addPredicates(PositionedString ps) {
        predicates = predicates.append(ps);
    }

    
    public void addAssignable(PositionedString ps) {
        assignable = assignable.append(ps);
    }
    
    
    public void setVariant(PositionedString ps) {
        assert variant == null;
        variant = ps;
    }
    
    
    public ImmutableList<PositionedString> getInvariant() {
        return invariant;
    }
    
    
    public ImmutableList<PositionedString> getSkolemDeclarations() {
        return skolemDeclarations;
    }
    
    
    public ImmutableList<PositionedString> getPredicates() {
        return predicates;
    }
    
    
    public ImmutableList<PositionedString> getAssignable() {
        return assignable;
    }
    
    
    public PositionedString getVariant() {
        return variant;
    }
    
    
    public String toString() {
        StringBuffer sb = new StringBuffer();
        Iterator<PositionedString> it;
        
        it = invariant.iterator();
        while(it.hasNext()) {
            sb.append("invariant: " + it.next() + "\n");
        }
        it = skolemDeclarations.iterator();
        while(it.hasNext()) {
            sb.append("skolem_constant: " + it.next() + "\n");
        }
        it = predicates.iterator();
        while(it.hasNext()) {
            sb.append("loop_predicate: " + it.next() + "\n");
        }
        it = assignable.iterator();
        while(it.hasNext()) {
            sb.append("assignable: " + it.next() + "\n");
        }
        if(variant != null) {
            sb.append("decreases: " + variant);
        }
        
        return sb.toString();
    }
    
    
    
    public boolean equals(Object o) {
        if(!(o instanceof TextualJMLLoopSpec)) {
            return false;
        }
        TextualJMLLoopSpec ls = (TextualJMLLoopSpec) o;
        return mods.equals(ls.mods)
               && invariant.equals(ls.invariant)
               && skolemDeclarations.equals(ls.skolemDeclarations)
               && predicates.equals(ls.predicates)
               && assignable.equals(ls.assignable)
               && (variant == null && ls.variant == null
                   || variant != null && variant.equals(ls.variant));
    }
    
    
    public int hashCode() {
        return mods.hashCode()
                + invariant.hashCode() 
                + skolemDeclarations.hashCode() 
                + predicates.hashCode() 
                + assignable.hashCode();
    }
}
