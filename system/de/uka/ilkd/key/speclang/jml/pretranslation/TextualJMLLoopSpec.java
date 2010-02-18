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

    private ImmutableList<PositionedString> parametrizedWS        
            = ImmutableSLList.<PositionedString>nil();
    private PositionedString workingSpaceLocal = null;
    private PositionedString workingSpaceConstructed = null;
    private PositionedString workingSpaceReentrant = null;

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
    
    public void addParametrizedWorkingspace(PositionedString ps){
        parametrizedWS = parametrizedWS.append(ps);
    }
    
    public void setWorkingSpaceLocal(PositionedString ps) {
        assert workingSpaceLocal == null;
        workingSpaceLocal = ps;
    }
    
    public void setWorkingSpaceConstructed(PositionedString ps) {
        assert workingSpaceConstructed == null;
        workingSpaceConstructed = ps;
    }
    
    public void setWorkingSpaceReentrant(PositionedString ps) {
        assert workingSpaceReentrant == null;
        workingSpaceReentrant = ps;
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
    
    public ListOfPositionedString getParametrizedWorkingspace(){
        return parametrizedWS;
    }
    
    public PositionedString getWorkingSpaceLocal() {
        return workingSpaceLocal;
    }
    
    public PositionedString getWorkingSpaceConstructed() {
        return workingSpaceConstructed;
    }
    
    public PositionedString getWorkingSpaceReentrant() {
        return workingSpaceReentrant;
    }
    
    
    public String toString() {
        StringBuffer sb = new StringBuffer();
        Iterator<PositionedString> it;
        
        it = invariant.iterator();
        while(it.hasNext()) {
            sb.append("invariant: ").append(it.next()).append("\n");
        }
        it = skolemDeclarations.iterator();
        while(it.hasNext()) {
            sb.append("skolem_constant: ").append(it.next()).append("\n");
        }
        it = predicates.iterator();
        while(it.hasNext()) {
            sb.append("loop_predicate: ").append(it.next()).append("\n");
        }
        it = assignable.iterator();
        while(it.hasNext()) {
            sb.append("assignable: ").append(it.next()).append("\n");
        }
        if(variant != null) {
            sb.append("decreases: ").append(variant);
        }
        
        it = parametrizedWS.iterator();
        while(it.hasNext()){
            sb.append("workingSpace"+it.next()+"\n");
        }
        
        if(workingSpaceLocal != null){
            sb.append("working_space_single_iteration_local: "+workingSpaceLocal);
        }
        
        if(workingSpaceConstructed != null){
            sb.append("working_space_single_iteration_constructed: "+workingSpaceConstructed);
        }
        
        if(workingSpaceReentrant != null){
            sb.append("working_space_single_iteration_reentrant: "+workingSpaceReentrant);
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
                   || variant.equals(ls.variant))
               && (workingSpaceLocal == null && ls.workingSpaceLocal == null ||
                       workingSpaceLocal.equals(ls.workingSpaceLocal))
               && (workingSpaceConstructed == null && ls.workingSpaceConstructed == null ||
                       workingSpaceConstructed.equals(ls.workingSpaceConstructed))
               && (workingSpaceReentrant == null && ls.workingSpaceReentrant == null ||
                       workingSpaceReentrant.equals(ls.workingSpaceReentrant));
    }
    
    
    public int hashCode() {
        return mods.hashCode()
                + invariant.hashCode() 
                + skolemDeclarations.hashCode() 
                + predicates.hashCode() 
                + assignable.hashCode();
    }
}
