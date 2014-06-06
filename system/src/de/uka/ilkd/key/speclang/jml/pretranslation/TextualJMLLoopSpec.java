// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.speclang.jml.pretranslation;

import java.util.*;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.speclang.PositionedString;


/**
 * A JML loop specification (invariant, assignable clause, decreases 
 * clause, ...) in textual form.
 */
public final class TextualJMLLoopSpec extends TextualJMLConstruct {

    private PositionedString variant                  
            = null;

    private Map<String, ImmutableList<PositionedString>>
      assignables = new LinkedHashMap<String, ImmutableList<PositionedString>>();

    private Map<String, ImmutableList<PositionedString>>
      invariants = new LinkedHashMap<String, ImmutableList<PositionedString>>();
    
    
    public TextualJMLLoopSpec(ImmutableList<String> mods) {
        super(mods);
        for(Name heap : HeapLDT.VALID_HEAP_NAMES) {
          assignables.put(heap.toString(), ImmutableSLList.<PositionedString>nil());
          invariants.put(heap.toString(), ImmutableSLList.<PositionedString>nil());          
        }
    }

       
    public void addInvariant(PositionedString ps) {
        addGeneric(invariants, ps);
    }

    public void addAssignable(PositionedString ps) {
        addGeneric(assignables, ps);
    }
    
    
    public void setVariant(PositionedString ps) {
        assert variant == null;
        variant = ps;
    }

    public ImmutableList<PositionedString> getInvariant(String hName) {
        return invariants.get(hName);
    }    
    
    public ImmutableList<PositionedString> getInvariant() {
        return invariants.get(HeapLDT.BASE_HEAP_NAME.toString());
    }
    
    public ImmutableList<PositionedString> getAssignable() {
        return assignables.get(HeapLDT.BASE_HEAP_NAME.toString());
    }

    public ImmutableList<PositionedString> getAssignable(String hName) {
        return assignables.get(hName);
    }

    public Map<String,ImmutableList<PositionedString>> getAssignables() {
        return assignables;
    }

    public Map<String,ImmutableList<PositionedString>> getInvariants() {
        return invariants;
    }

    public PositionedString getVariant() {
        return variant;
    }
    
    
    @Override
    public String toString() {
        StringBuffer sb = new StringBuffer();
        Iterator<PositionedString> it;
        
        for(Name heap : HeapLDT.VALID_HEAP_NAMES) {
          it = invariants.get(heap.toString()).iterator();
          while(it.hasNext()) {
            sb.append("invariant<"+heap+">: " + it.next() + "\n");
          }
        }
        for(Name heap : HeapLDT.VALID_HEAP_NAMES) {
          it = assignables.get(heap.toString()).iterator();
          while(it.hasNext()) {
            sb.append("assignable<"+heap+">: " + it.next() + "\n");
          }
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
               && invariants.equals(ls.invariants)
               && assignables.equals(ls.assignables)
               && (variant == null && ls.variant == null
                   || variant != null && variant.equals(ls.variant));
    }
        
    @Override
    public int hashCode() {
        return mods.hashCode()
                + invariants.hashCode() 
                + assignables.hashCode();
    }
}