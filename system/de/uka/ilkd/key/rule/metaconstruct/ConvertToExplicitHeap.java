// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.AbstractSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.UpdateSimplifier;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.updatesimplifier.ArrayOfAssignmentPair;
import de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair;
import de.uka.ilkd.key.rule.updatesimplifier.AssignmentPairImpl;
import de.uka.ilkd.key.rule.updatesimplifier.Update;

public class ConvertToExplicitHeap extends AbstractMetaOperator {

    private static final TermBuilder TB = TermBuilder.DF;

    public ConvertToExplicitHeap() {
        super(new Name("#toExplicitHeap"), 1);
    }
    
    
    public static Function getAttributeSymbol(ProgramVariable attributePV, 
                                              Services services) {
        Name name = new Name(attributePV.toString());
        Function result 
            = (Function) services.getNamespaces().functions().lookup(name); 
        if(result == null) {
            result = new RigidFunction(name, 
                                       services.getJavaInfo().getFieldSort(), 
                                       new Sort[0]);
            services.getNamespaces().functions().add(result);
        }
        return result;
    }
    
    
    public static Update convert(Update u, Services services) {
        ArrayOfAssignmentPair pairs = u.getAllAssignmentPairs();
        AssignmentPair[] newPairs = new AssignmentPair[pairs.size()];
        
        for(int i = 0; i < newPairs.length; i++) {
            AssignmentPair pair = pairs.getAssignmentPair(i);
            Location lhsLoc = pair.location();
            Term[] lhsSubs  = pair.locationSubs();
            Term rhs        = pair.value();
            
            Location newLhsLoc;
            Term[] newLhsSubs;
            Term newRhs;
            
            if(lhsLoc instanceof AttributeOp) {
                ProgramVariable attributePV = (ProgramVariable)((AttributeOp)lhsLoc).attribute();
                Term objectTerm = lhsSubs[0];
                Function attr = getAttributeSymbol(attributePV, services);
                newLhsLoc = services.getJavaInfo().getHeap();
                newLhsSubs = new Term[0];
                newRhs = TB.store(services, 
                                  TB.heap(services), 
                                  convert(objectTerm, services), 
                                  attr, 
                                  convert(rhs, services));                
            } else {
                newLhsLoc  = lhsLoc;
                newLhsSubs = convert(lhsSubs, services);
                newRhs     = convert(rhs, services);
            }
            newPairs[i] = new AssignmentPairImpl(pair.boundVars(),
                                                 convert(pair.guard(), services),
                                                 newLhsLoc,
                                                 newLhsSubs,
                                                 newRhs);
        }
        
        return Update.createUpdate(newPairs);
    }
    
    
    public static Term convert(Term t, Services services) {
        if(t.op() instanceof IUpdateOperator) {
            IUpdateOperator uop = (IUpdateOperator) t.op();
            UpdateFactory uf = new UpdateFactory(services, new UpdateSimplifier());
            return uf.apply(convert(Update.createUpdate(t), services), 
                            convert(t.sub(uop.targetPos()), services));
        } else if(t.op() instanceof AttributeOp) {
            ProgramVariable attributePV 
                = (ProgramVariable)((AttributeOp)t.op()).attribute();
            Term objectTerm = convert(t.sub(0), services);
            Function attributeSymbol = getAttributeSymbol(attributePV, services);
            return TB.tf().createCastTerm(
                    (AbstractSort)attributePV.sort(), 
                    TB.dot(services, objectTerm, attributeSymbol));
        } else {
            final Term newSubTerms[] = new Term[t.arity()];
            final ArrayOfQuantifiableVariable[] boundVars 
                = new ArrayOfQuantifiableVariable[t.arity()];
    
            boolean changedSubTerm = false;            
            for(int i = 0, ar = t.arity(); i < ar; i++) {
                final Term subTerm = t.sub(i);
                newSubTerms[i] = convert(subTerm, services);
                if(newSubTerms[i] != subTerm) {
                    changedSubTerm = true;
                }
                boundVars[i] = t.varsBoundHere(i);
            }
            
            if(changedSubTerm) {                               
                return TermFactory.DEFAULT.createTerm(t.op(),
                                                      newSubTerms,
                                                      boundVars,
                                                      t.javaBlock());
            } else {
                return t;
            }
        }
    }
    
    
    public static Term[] convert(Term[] terms, Services services) {
        Term[] result = new Term[terms.length];
        for(int i = 0; i < terms.length; i++) {
            result[i] = convert(terms[i], services);
        }
        return result;
    }
    
    
    
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        return convert(term.sub(0), services);        
    }
                

    public boolean validTopLevel(Term term) {
        return true;
    }


    public Sort sort(Term[] term) {
        return term[0].sort();
    }
    

    public boolean isRigid(Term term) {
        return false;
    }

    
    public MatchConditions match(SVSubstitute subst, MatchConditions mc,
            Services services) {
        return null;
    }
    
}