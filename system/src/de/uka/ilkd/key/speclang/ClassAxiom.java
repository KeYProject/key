// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.Pair;


/**
 * An axiom originating from a (JML) specification, belonging to a particular
 * class, and constraining a particular observer symbol. A class axiom always
 * has an associated visibility. The visibility determines in which proofs the 
 * axiom is available, in accordance with the visibility rules of Java. If 
 * visible, it is made available not as a formula, but as one or many taclets 
 * (for performance reasons).
 */
public abstract class ClassAxiom implements SpecificationElement {
        

    protected static final TermBuilder TB = TermBuilder.DF;
    protected String displayName;
    
    public static Pair<Term, ImmutableSet<Taclet>> limitTerm(Term t, ImmutableSet<Pair<Sort, ObserverFunction>> toLimit, Services services) {
        ImmutableSet<Taclet> taclets = DefaultImmutableSet.nil();
        
        //recurse to subterms
        Term[] subs = new Term[t.arity()];
        for(int i = 0; i < subs.length; i++) {
             Pair<Term,ImmutableSet<Taclet>> pair 
             	= limitTerm(t.sub(i), toLimit, services);
             subs[i] = pair.first;
             taclets = taclets.union(pair.second);
        }
        
        //top level operator
        Operator newOp = t.op();
        if(t.op() instanceof ObserverFunction) {
            final ObserverFunction obs = (ObserverFunction) t.op();
            for(Pair<Sort, ObserverFunction> pair : toLimit) {
        	if(pair.second.equals(t.op())
                   && (obs.isStatic() 
                       || t.sub(1).sort().extendsTrans(pair.first))) {
        	    Pair<ObserverFunction,ImmutableSet<Taclet>> limited
        	    	= services.getSpecificationRepository().limitObs(obs); 
        	    newOp = limited.first;
        	    taclets = taclets.union(limited.second);
        	}
            }
        }
        
        //reassemble, return
        final Term term 
        	= TB.tf().createTerm(newOp, subs, t.boundVars(), t.javaBlock());
        return new Pair<Term,ImmutableSet<Taclet>>(term, taclets);
    }


    private static Pair<Term,ImmutableSet<VariableSV>> replaceBoundLVsWithSVsHelper(Term t) {
        ImmutableSet<VariableSV> svs = DefaultImmutableSet.<VariableSV>nil();
        
        //prepare op replacer, new bound vars
        final Map<Operator,Operator> map = new HashMap<Operator,Operator>();
        final ImmutableArray<QuantifiableVariable> boundVars 
        	= t.boundVars();
        final QuantifiableVariable[] newBoundVars 
        	= new QuantifiableVariable[boundVars.size()];	
        for(int i = 0; i < newBoundVars.length; i++) {
            final QuantifiableVariable qv = boundVars.get(i);
            if(qv instanceof LogicVariable) {
        	final VariableSV sv 
        		= SchemaVariableFactory.createVariableSV(qv.name(), 
        						         qv.sort());
        	svs = svs.add(sv);
        	newBoundVars[i] = sv;
        	map.put(qv, sv);
            } else {
        	newBoundVars[i] = qv;
            }
        }
        final OpReplacer or = new OpReplacer(map);	
        
        //handle subterms
        final Term[] newSubs = new Term[t.arity()];
        boolean changedSub = false;
        for(int i = 0; i < newSubs.length; i++) {
            if(t.op().bindVarsAt(i)) {
        	newSubs[i] = or.replace(t.sub(i));
            } else {
        	newSubs[i] = t.sub(i);
            }
            final Pair<Term,ImmutableSet<VariableSV>> subPair 
            	= replaceBoundLVsWithSVsHelper(newSubs[i]);
            newSubs[i] = subPair.first;
            svs = svs.union(subPair.second);
            if(newSubs[i] != t.sub(i)) {
        	changedSub = true;
            }
        }
        
        //build overall term
        final Term newTerm;
        if(map.isEmpty() && !changedSub) {
            newTerm = t;
        } else {
            newTerm = TB.tf().createTerm(
        	    	t.op(), 
        	    	newSubs, 
        	    	new ImmutableArray<QuantifiableVariable>(newBoundVars),
        	        t.javaBlock());
        }
        
        return new Pair<Term,ImmutableSet<VariableSV>>(newTerm, svs);
    }


    /**
     * Replaces any bound logical variables in t with schema variables
     * (necessary for proof saving/loading, if t occurs as part of a taclet). 
     */
    public static Pair<Term,ImmutableSet<VariableSV>> replaceBoundLVsWithSVs(Term t) {
        //recursive replacement process
        final Pair<Term,ImmutableSet<VariableSV>> intermediateRes 
        	= replaceBoundLVsWithSVsHelper(t);
        
        //Post-processing: different bound variables with the same name 
        //(but non-overlapping scopes) may be used in t; in contrast, the 
        //schema variables in this method's result must have names that are 
        //unique within the term.
        
        //collect all operator names used in t
        final OpCollector oc = new OpCollector();
        oc.visit(t);
        final Set<Name> usedNames = new HashSet<Name>();
        for(Operator op : oc.ops()) {
            usedNames.add(op.name());
        }
        
        //find and resolve name conflicts between schema variables
        ImmutableSet<VariableSV> newSVs 
        	= DefaultImmutableSet.<VariableSV>nil();
        final Set<Name> namesOfNewSVs = new HashSet<Name>();
        final Map<VariableSV,VariableSV> replaceMap 
        	= new HashMap<VariableSV,VariableSV>(); 
        for(VariableSV sv : intermediateRes.second) {
            if(namesOfNewSVs.contains(sv.name())) {
                //choose alternative name
                final String baseName = sv.name().toString();
                int i = 0;
                Name newName;
                do {
                    newName = new Name(baseName + "_" + i++);
                } while(usedNames.contains(newName));

                //create new SV, register in replace map
                final VariableSV newSV 
                = SchemaVariableFactory.createVariableSV(newName, 
                        sv.sort());
                newSVs = newSVs.add(newSV);
                namesOfNewSVs.add(newSV.name());
                usedNames.add(newSV.name());
                replaceMap.put(sv, newSV);
            } else {
                newSVs = newSVs.add(sv);
                namesOfNewSVs.add(sv.name());
            }
        }
        final OpReplacer or = new OpReplacer(replaceMap);
        final Term newTerm = or.replace(intermediateRes.first);	
        
        return new Pair<Term,ImmutableSet<VariableSV>>(newTerm, newSVs);
    }


    /**
     * Returns the axiomatised function symbol. 
     */
    public abstract ObserverFunction getTarget();
 
    
    /**
     * Returns the pairs (kjt, obs) for which there is an occurrence of
     * o.obs in the axiom, where kjt is the type of o (excluding the
     * defining occurrence of the axiom target). 
     */
    public abstract ImmutableSet<Pair<Sort, ObserverFunction>> getUsedObservers(
	    						Services services);
    
    /**
     * The axiom as one or many taclets, where the non-defining occurrences of
     * the passed observers are replaced by their "limited" counterparts.
     */
    public abstract ImmutableSet<Taclet> getTaclets(
	    		ImmutableSet<Pair<Sort, ObserverFunction>> toLimit,
	    		Services services);    

    @Override
    public String getDisplayName() {
        return displayName == null ? getName() : displayName;
    }
}
