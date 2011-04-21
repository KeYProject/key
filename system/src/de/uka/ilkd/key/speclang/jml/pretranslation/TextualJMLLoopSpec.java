// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.speclang.jml.pretranslation;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.speclang.PositionedString;


/**
 * A JML loop specification (invariant, assignable clause, decreases 
 * clause, ...) in textual form.
 */
public final class TextualJMLLoopSpec extends TextualJMLConstruct {

    private ImmutableList<PositionedString> invariant          
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
    
    
    public ImmutableList<PositionedString> getAssignable() {
        return assignable;
    }
    
    
    public PositionedString getVariant() {
        return variant;
    }
    
    
    @Override
    public String toString() {
        StringBuffer sb = new StringBuffer();
        Iterator<PositionedString> it;
        
        it = invariant.iterator();
        while(it.hasNext()) {
            sb.append("invariant: " + it.next() + "\n");
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
    
    
    @Override
    public boolean equals(Object o) {
        if(!(o instanceof TextualJMLLoopSpec)) {
            return false;
        }
        TextualJMLLoopSpec ls = (TextualJMLLoopSpec) o;
        return mods.equals(ls.mods)
               && invariant.equals(ls.invariant)
               && assignable.equals(ls.assignable)
               && (variant == null && ls.variant == null
                   || variant != null && variant.equals(ls.variant));
    }
    
    
    @Override
    public int hashCode() {
        return mods.hashCode()
                + invariant.hashCode() 
                + assignable.hashCode();
    }
}
