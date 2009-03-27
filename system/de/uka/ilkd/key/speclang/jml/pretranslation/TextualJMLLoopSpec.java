// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang.jml.pretranslation;

import de.uka.ilkd.key.collection.ListOfString;
import de.uka.ilkd.key.speclang.IteratorOfPositionedString;
import de.uka.ilkd.key.speclang.ListOfPositionedString;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.SLListOfPositionedString;


public class TextualJMLLoopSpec extends TextualJMLConstruct {

    private ListOfPositionedString invariant          
            = SLListOfPositionedString.EMPTY_LIST;
    private ListOfPositionedString skolemDeclarations 
            = SLListOfPositionedString.EMPTY_LIST;
    private ListOfPositionedString predicates         
            = SLListOfPositionedString.EMPTY_LIST;
    private ListOfPositionedString assignable         
            = SLListOfPositionedString.EMPTY_LIST;
    private PositionedString variant                  
            = null;
    
    
    public TextualJMLLoopSpec(ListOfString mods) {
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
    
    
    public ListOfPositionedString getInvariant() {
        return invariant;
    }
    
    
    public ListOfPositionedString getSkolemDeclarations() {
        return skolemDeclarations;
    }
    
    
    public ListOfPositionedString getPredicates() {
        return predicates;
    }
    
    
    public ListOfPositionedString getAssignable() {
        return assignable;
    }
    
    
    public PositionedString getVariant() {
        return variant;
    }
    
    
    public String toString() {
        StringBuffer sb = new StringBuffer();
        IteratorOfPositionedString it;
        
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
                   || variant.equals(ls.variant));
    }
    
    
    public int hashCode() {
        return mods.hashCode()
                + invariant.hashCode() 
                + skolemDeclarations.hashCode() 
                + predicates.hashCode() 
                + assignable.hashCode();
    }
}
