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
import java.util.List;
import java.util.ArrayList;
import java.util.Map;
import java.util.LinkedHashMap;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.logic.TermBuilder;


/**
 * A JML loop specification (invariant, assignable clause, decreases 
 * clause, ...) in textual form.
 */
public final class TextualJMLLoopSpec extends TextualJMLConstruct {

    private ImmutableList<PositionedString> invariant          
            = ImmutableSLList.<PositionedString>nil();
    private ImmutableList<PositionedString> transaction_invariant          
            = ImmutableSLList.<PositionedString>nil();
    private PositionedString variant                  
            = null;
    private Map<String, ImmutableList<PositionedString>>
      assignables = new LinkedHashMap<String, ImmutableList<PositionedString>>();
    
    
    public TextualJMLLoopSpec(ImmutableList<String> mods) {
        super(mods);
        for(String hName : TermBuilder.VALID_HEAP_NAMES) {
          assignables.put(hName, ImmutableSLList.<PositionedString>nil());
        }
    }

       
    public void addInvariant(PositionedString ps) {
        invariant = invariant.append(ps);
    }

    public void addTransactionInvariant(PositionedString ps) {
        transaction_invariant = transaction_invariant.append(ps);
    }
    
    
    public void addAssignable(PositionedString ps) {
        String t = ps.text;
        if(!t.startsWith("<")) {
           ImmutableList<PositionedString> l = assignables.get(TermBuilder.BASE_HEAP_NAME);
           l = l.append(ps);
           assignables.put(TermBuilder.BASE_HEAP_NAME, l);
           return; 
        }
        List<String> hs = new ArrayList<String>();
        for(String hName : TermBuilder.VALID_HEAP_NAMES) {
          String h = "<" + hName + ">";
          if(t.startsWith(h)) {
            hs.add(hName);
            t = t.substring(h.length());
          }
        }
        ps = new PositionedString(t, ps.fileName, ps.pos);
        for(String h : hs) {
           ImmutableList<PositionedString> l = assignables.get(h);
           l = l.append(ps);
           assignables.put(h, l); 
        }
    }
    
//    public void addAssignableBackup(PositionedString ps) {
//        assignable_backup = assignable_backup.append(ps);
//    }
    
    public void setVariant(PositionedString ps) {
        assert variant == null;
        variant = ps;
    }
    
    
    public ImmutableList<PositionedString> getInvariant() {
        return invariant;
    }
    
    public ImmutableList<PositionedString> getTransactionInvariant() {
        return transaction_invariant;
    }
    
    public ImmutableList<PositionedString> getAssignable() {
        return assignables.get(TermBuilder.BASE_HEAP_NAME);
    }

    public ImmutableList<PositionedString> getAssignable(String hName) {
        return assignables.get(hName);
    }

    public Map<String,ImmutableList<PositionedString>> getAssignables() {
        return assignables;
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
        it = transaction_invariant.iterator();
        while(it.hasNext()) {
            sb.append("transaction_invariant: " + it.next() + "\n");
        }
        for(String h : TermBuilder.VALID_HEAP_NAMES) {
          it = assignables.get(h).iterator();
          while(it.hasNext()) {
            sb.append("assignable<"+h+">: " + it.next() + "\n");
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
               && invariant.equals(ls.invariant)
               && transaction_invariant.equals(ls.transaction_invariant)
               && assignables.equals(ls.assignables)
               && (variant == null && ls.variant == null
                   || variant != null && variant.equals(ls.variant));
    }
        
    @Override
    public int hashCode() {
        return mods.hashCode()
                + invariant.hashCode() 
                + transaction_invariant.hashCode() 
                + assignables.hashCode();
    }
}
