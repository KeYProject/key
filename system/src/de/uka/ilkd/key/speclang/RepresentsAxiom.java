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


package de.uka.ilkd.key.speclang;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGenerator;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;


/**
 * A class axiom corresponding to a JML* represents clause.
 */
public final class RepresentsAxiom extends ClassAxiom {
    
    
    private final String name;
    private final IObserverFunction target;
    private final KeYJavaType kjt;
    private final VisibilityModifier visibility;
    private final Term originalRep;
    private final ProgramVariable originalSelfVar;
    
    public RepresentsAxiom(String name,
	    		   IObserverFunction target, 
	                   KeYJavaType kjt,
	                   VisibilityModifier visibility,
	                   Term rep,
	                   ProgramVariable selfVar) {
        this(name,null,target,kjt,visibility,rep,selfVar);
    }
    
    
    public RepresentsAxiom(String name,
            String displayName,
            IObserverFunction target, 
                KeYJavaType kjt,
                VisibilityModifier visibility,
                Term rep,
                ProgramVariable selfVar) {

        assert name != null;
        assert kjt != null;
        assert target != null;
        assert rep.sort() == Sort.FORMULA;
        assert (selfVar == null) == target.isStatic();
        this.name = name;
        this.target = target;
        this.kjt = kjt;
        this.visibility = visibility;
        this.originalRep = rep;
        this.originalSelfVar = selfVar;
        this.displayName = displayName;
    }
    
    private boolean isFunctional() {
	return originalRep.op() instanceof Equality
	       && originalRep.sub(0).op() == target
	       && (target.isStatic() 
		   || originalRep.sub(0).sub(1).op().equals(originalSelfVar));
    }
    
    private Term instance(boolean finalClass, SchemaVariable selfSV, Services services){
        return target.isStatic() || finalClass || VisibilityModifier.allowsInheritance(visibility)
        ? TB.tt() :TB.exactInstance(services, kjt.getSort(), TB.var(selfSV));
    }

    
    private Term getAxiom(ParsableVariable heapVar, 
	    		  ParsableVariable selfVar,
	    		  Services services) {
	assert heapVar != null;
	assert (selfVar == null) == target.isStatic();
	final Map<ProgramVariable, ParsableVariable> map = new HashMap<ProgramVariable, ParsableVariable>();
	map.put(services.getTypeConverter().getHeapLDT().getHeap(), heapVar);	
	if(selfVar != null) {
	    map.put(originalSelfVar, selfVar);
	}
	final OpReplacer or = new OpReplacer(map);
	return or.replace(originalRep);
    }
    
    
    public String getName() {
	return name;
    }
    
    
    public IObserverFunction getTarget() {
	return target;
    }    
    

    public KeYJavaType getKJT() {
	return kjt;
    }
    
    
    public VisibilityModifier getVisibility() {
	return visibility;
    }

    
    public ImmutableSet<Taclet> getTaclets(
            ImmutableSet<Pair<Sort, IObserverFunction>> toLimit,
            Services services) {
        LocationVariable heap =
                services.getTypeConverter().getHeapLDT().getHeap();
        ProgramVariable self = (!target.isStatic() ? originalSelfVar : null);
//	        ifSemiSeq.insertFirst(ifCf).semisequent();
//	    } else ifSeq = null;

        Name tacletName = MiscTools.toValidTacletName(name);
        TacletGenerator TG = TacletGenerator.getInstance();
        if (isFunctional()) {
            ImmutableSet<Taclet> res = DefaultImmutableSet.<Taclet>nil();
            res = res.union(TG.generateFunctionalRepresentsTaclets(tacletName, originalRep, kjt, target, heap, self, toLimit, true, services));
            res = res.union(TG.generateFunctionalRepresentsTaclets(tacletName, originalRep, kjt, target, heap, self, toLimit, false, services));
            return res;
        } else {
            Taclet tacletWithShowSatisfiability =
                    TG.generateRelationalRepresentsTaclet(tacletName,
                                                          originalRep,
                                                          kjt,
                                                          target,
                                                          heap,
                                                          self,
                                                          true,
                                                          services);
            Taclet tacletWithTreatAsAxiom =
                    TG.generateRelationalRepresentsTaclet(tacletName,
                                                          originalRep,
                                                          kjt,
                                                          target,
                                                          heap,
                                                          self,
                                                          false,
                                                          services);
            return DefaultImmutableSet.<Taclet>nil().add(tacletWithShowSatisfiability).add(tacletWithTreatAsAxiom);
        }
    }
    
    
    public ImmutableSet<Pair<Sort, IObserverFunction>> getUsedObservers(
	    						Services services) {
	if(!isFunctional()) {
	    return DefaultImmutableSet.nil();
	} else {
	    return MiscTools.collectObservers(originalRep.sub(1));
	}
    }    
    
    
    @Override
    public String toString() {
	return originalRep.toString();
    }


    public RepresentsAxiom setKJT(KeYJavaType newKjt) {
        String newName = "JML represents clause for " + target
        		+ " (subclass " + newKjt.getName()+ ")";
        return new RepresentsAxiom(newName, displayName, target, newKjt, visibility, originalRep, originalSelfVar);
    }
    
    /** Conjoins two represents clauses with minimum visibility. 
     *  An exception is thrown if the targets or types are different.
     *  <b>Known issue</b>: public clauses in subclasses are hidden by protected clauses in superclasses;
     *  this only applies to observers outside the package of the subclass (whenever package-privacy is implemented).
     */
    public RepresentsAxiom conjoin (RepresentsAxiom ax) {
        if (!target.equals(ax.target) || !kjt.equals(ax.kjt)){
            throw new RuntimeException("Tried to conjoin incompatible represents axioms.");
        }
        VisibilityModifier minVisibility = visibility == null ? (VisibilityModifier.isPrivate(ax.visibility) ? ax.visibility : null) : (visibility.compareTo(ax.visibility) >= 0 ? visibility : ax.visibility);
        Term newRep = TB.and(originalRep, ax.originalRep);
        return new RepresentsAxiom(name, displayName, target, kjt, minVisibility, newRep, originalSelfVar);
    }

}
