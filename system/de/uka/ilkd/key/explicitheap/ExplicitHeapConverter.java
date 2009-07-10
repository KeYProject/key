// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.explicitheap;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.AbstractSort;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.ListOfGoal;
import de.uka.ilkd.key.proof.ProgVarReplacer;
import de.uka.ilkd.key.rule.OldUpdateSimplifier;
import de.uka.ilkd.key.rule.conditions.TypeResolver;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.updatesimplifier.ArrayOfAssignmentPair;
import de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair;
import de.uka.ilkd.key.rule.updatesimplifier.AssignmentPairImpl;
import de.uka.ilkd.key.rule.updatesimplifier.Update;


/** 
 * Called in:
 *   - ProblemInitializer::setUpProofHelper()
 *   - Goal::apply() 
 */
public class ExplicitHeapConverter {

    public static final ExplicitHeapConverter INSTANCE = new ExplicitHeapConverter();
    
    private static final TermBuilder TB = TermBuilder.DF;
    private static final String ARRAY_LENGTH_FIELD_NAME = "Array::length";

    
    private ExplicitHeapConverter() {
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private void warn(String s) {
        System.out.println("ExplicitHeapConverter WARNING: " + s);
    }
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    public Function getFieldSymbol(ProgramVariable fieldPV, Services services) {
	final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
	final Name name;
	if(fieldPV == services.getJavaInfo().getArrayLength()) {
	    name = new Name(ARRAY_LENGTH_FIELD_NAME);
	} else if(fieldPV.isStatic()) {
	    name = new Name(fieldPV.getContainerType().getSort().toString() 
		    	    + "::" 
		    	    + fieldPV.toString());
	} else {
	    name = new Name(fieldPV.toString());
	}
        Function result 
            = (Function) services.getNamespaces().functions().lookup(name); 
        if(result == null) {
            result 
                = new RigidFunction(name, 
                		    heapLDT.getFieldSort(), 
                		    new Sort[0], true);
            services.getNamespaces().functions().add(result);
        } else {
            if(!(result instanceof RigidFunction && ((RigidFunction)result).isUnique())) {
                warn("field symbol \"" + name + "\" is not unique!");
            }
        }
        return result;
    }
    
    
    public Sort getFieldTargetSort(Term objectTerm, 
	    			   Term fieldTerm, 
	    			   Services services) {
	final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();	
	assert fieldTerm.op() instanceof RigidFunction
	       && ((RigidFunction)fieldTerm.op()).isUnique();
	
	final RigidFunction fieldSymbol = (RigidFunction) fieldTerm.op();
	final String fieldSymbolName = fieldSymbol.name().toString();
	
	if(fieldSymbolName.equals(ARRAY_LENGTH_FIELD_NAME)) {
	    return services.getTypeConverter().getIntLDT().targetSort();
	} else if(fieldSymbol.arity() == 0) {
	    ProgramVariable fieldPV
	    	= services.getJavaInfo().getAttribute(fieldSymbol.name().toString());
	    assert fieldPV != null;
	    return fieldPV.sort();
	} else if(fieldSymbol == heapLDT.getArr()){
	    assert objectTerm.sort() instanceof ArraySort;
	    return ((ArraySort) objectTerm.sort()).elementSort();
	} else {
	    assert false;
	    return null;
	}
    }
    
        
    
//    public Update convert(Update u, Services services) {
//	final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();	
//        final ArrayOfAssignmentPair pairs = u.getAllAssignmentPairs();
//        final AssignmentPair[] newPairs = new AssignmentPair[pairs.size()];
//        
//        boolean changedPair = false;
//        Term heapTerm = TB.heap(services);
//        for(int i = 0; i < newPairs.length; i++) {
//            final AssignmentPair pair = pairs.getAssignmentPair(i);
//            final UpdateableOperator lhsLoc = pair.location();
//            final Term[] lhsSubs  = pair.locationSubs();
//            final Term rhs        = pair.value();
//            
//            if(pair.boundVars().size() > 0) {
//                warn("encountered quantified update: " + pair);
//            }
//
//            UpdateableOperator newLhsLoc;
//            Term[] newLhsSubs;
//            Term newRhs;
//            
//            if(lhsLoc instanceof ProgramVariable 
//        	      && ((ProgramVariable)lhsLoc).isStatic()) {
//        	final ProgramVariable fieldPV = (ProgramVariable) lhsLoc;
//        	final Function fieldSymbol = getFieldSymbol(fieldPV, services);
//        	
//        	newLhsLoc = heapLDT.getHeap();
//        	newLhsSubs = new Term[0];
//        	heapTerm = TB.store(services, 
//        			    heapTerm, 
//        			    TB.NULL(services), 
//        			    TB.func(fieldSymbol),
//        			    convert(rhs, services));
//        	newRhs = heapTerm;
//            } else {
//                newLhsLoc  = lhsLoc;
//                newLhsSubs = convert(lhsSubs, services);
//                newRhs     = convert(rhs, services);
//            }
//            
//            if(newLhsLoc != lhsLoc || newLhsSubs != lhsSubs || newRhs != rhs) {
//                newPairs[i] = new AssignmentPairImpl(pair.boundVars(),
//                                                     convert(pair.guard(), services),
//                                                     newLhsLoc,
//                                                     newLhsSubs,
//                                                     newRhs);
//                changedPair = true;
//            } else {
//                newPairs[i] = pair;
//            }
//        }
//        
//        return changedPair ? Update.createUpdate(newPairs) : u;
//    }
//    
//    
//    public Term convert(Term t, Services services) {
//        if(t.op() instanceof IUpdateOperator) {
//            final IUpdateOperator uop = (IUpdateOperator) t.op();
//            final UpdateFactory uf 
//                = new UpdateFactory(services, new OldUpdateSimplifier());
//            Update update = Update.createUpdate(t);
//            Term subTerm  = t.sub(uop.targetPos());
//            
//            Update newUpdate = convert(update, services);
//            Term newSubTerm  = convert(subTerm, services);
//            
//            if(newUpdate !=  update || newSubTerm != subTerm) {            
//                return uf.prepend(newUpdate, newSubTerm);
//            } else {
//                return t;
//            }
//        } else if(t.op() instanceof ProgramVariable 
//        	      && ((ProgramVariable)t.op()).isStatic()) {
//            final ProgramVariable fieldPV = (ProgramVariable)t.op();
//            final Function fieldSymbol 
//                = getFieldSymbol(fieldPV, services);
//            final Term dotTerm = TB.staticDot(services,
//        	    			      fieldPV.sort(),
//                                              fieldSymbol);
//            return TB.tf().createCastTerm((AbstractSort) t.sort(), 
//                                          dotTerm);
//        } else {
//            if(t.op() instanceof NonRigidFunction) {
//                warn("encountered an unexpected non rigid symbol: " + t.op());
//            }
//            
//            final Term newSubTerms[] = new Term[t.arity()];
//            final ArrayOfQuantifiableVariable[] boundVars 
//                = new ArrayOfQuantifiableVariable[t.arity()];
//    
//            boolean changedSubTerm = false;            
//            for(int i = 0, ar = t.arity(); i < ar; i++) {
//                final Term subTerm = t.sub(i);
//                newSubTerms[i] = convert(subTerm, services);
//                if(newSubTerms[i] != subTerm) {
//                    changedSubTerm = true;
//                }
//                boundVars[i] = t.varsBoundHere(i);
//            }
//            
//            if(changedSubTerm) {                               
//                return TermFactory.DEFAULT.createTerm(t.op(),
//                                                      newSubTerms,
//                                                      boundVars,
//                                                      t.javaBlock());
//            } else {
//                return t;                
//            }
//        }
//    }
//    
//    
//    public Term[] convert(Term[] terms, Services services) {
//        Term[] newTerms = new Term[terms.length];
//        
//        boolean changedTerm = false;
//        for(int i = 0; i < terms.length; i++) {
//            newTerms[i] = convert(terms[i], services);
//            if(newTerms[i] != terms[i]) {
//                changedTerm = true;
//            }
//        }
//        
//        return changedTerm ? newTerms : terms;
//    }
//    
//    
//    public ConstrainedFormula convert(ConstrainedFormula cf, Services services) {
//        Term formula = cf.formula();
//        Term newFormula = convert(formula, services);
//        return newFormula != formula 
//               ? new ConstrainedFormula(newFormula, cf.constraint())
//               : cf;
//    }
//    
//    
//    public SemisequentChangeInfo convert(Semisequent ss, Services services) {
//        final SemisequentChangeInfo sci = new SemisequentChangeInfo();
//        sci.setFormulaList(ss.toList());
//        sci.setSemisequent(ss);
//
//        boolean changedCf = false;
//        final IteratorOfConstrainedFormula it = ss.iterator();
//        for (int formulaNumber = 0; it.hasNext(); formulaNumber++) {            
//            final ConstrainedFormula oldcf = it.next();
//            final ConstrainedFormula newcf = convert(oldcf, services);
//
//            if(newcf != oldcf) {
//                SemisequentChangeInfo semiCI
//                    = sci.semisequent().replace(formulaNumber, newcf);
//                ProgVarReplacer.mergeSemiCIs(sci, semiCI, formulaNumber);
//                changedCf = true;
//            }
//        }
//
//        return changedCf ? sci : null;
//    }
//    
//    
//    public SequentChangeInfo convert(Sequent s, Services services) {
//        final SemisequentChangeInfo anteCI = convert(s.antecedent(), services);
//        final SemisequentChangeInfo succCI = convert(s.succedent(), services);
//        
//        if(anteCI != null || succCI != null) {
//            final Semisequent newAnte = anteCI != null 
//                                        ? anteCI.semisequent() 
//                                        : s.antecedent();
//            final Semisequent newSucc = succCI != null 
//                                        ? succCI.semisequent() 
//                                        : s.succedent();
//            final Sequent newSequent = Sequent.createSequent(newAnte, newSucc);
//            return SequentChangeInfo.createSequentChangeInfo(anteCI, 
//                                                             succCI, 
//                                                             newSequent, 
//                                                             s);
//        } else {
//            return null;
//        }
//    }
//    
//    
//    public void convertDestructive(Goal g, Services services) {
//        SequentChangeInfo sci = convert(g.sequent(), services);
//        if(sci != null) {            
//            g.setSequent(convert(g.sequent(), services));
//        } 
//    }
//    
//    
//    public void convertDestructive(ListOfGoal goals, Services services) {
//        if(goals != null){
//            for(Goal g : goals) {
//                convertDestructive(g, services);
//            }
//        }
//    }
//    
    //only converts heap locs
    public Term convert(LocationDescriptor loc, Services services) {
        HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
	if(loc instanceof BasicLocationDescriptor) {
            BasicLocationDescriptor bloc = (BasicLocationDescriptor) loc;
            Term locTerm = bloc.getLocTerm();
            if(!bloc.getFormula().equals(TB.tt())) {
        	warn("ignoring location descriptor guard: " + bloc.getFormula());
            }            
            assert locTerm.op() instanceof ProgramVariable;
            return TB.empty(services);
	} else {
	    assert loc instanceof EverythingLocationDescriptor;
	    return TB.everything(services);
	}
    }
    
    
    public Term convert(SetOfLocationDescriptor locs, Services services) {
	Term result = TB.empty(services);
	for(LocationDescriptor loc : locs) {
	    result = TB.union(services, result, convert(loc, services));
	}
	return result;
    }
    
    
    //-------------------------------------------------------------------------
    //inner classes
    //-------------------------------------------------------------------------
    
    public static final class FieldTargetTypeResolver extends TypeResolver {
                
	private final SchemaVariable objectSV;
        private final SchemaVariable fieldSV;

        public FieldTargetTypeResolver(SchemaVariable objectSV,
        			       SchemaVariable fieldSV) {
            this.objectSV = objectSV;
            this.fieldSV  = fieldSV;
        }

        public boolean isComplete(SchemaVariable sv,
                SVSubstitute instCandidate, SVInstantiations instMap,
                Services services) {            
            return sv == fieldSV || instMap.getInstantiation(fieldSV) != null;
        }

        public Sort resolveSort(SchemaVariable sv, SVSubstitute instCandidate,
                SVInstantiations instMap, Services services) {
            Term objectTerm = (Term) instMap.getInstantiation(objectSV);
            Term fieldTerm  = (Term) instMap.getInstantiation(fieldSV);

            return ExplicitHeapConverter.INSTANCE.getFieldTargetSort(objectTerm, 
        	    						     fieldTerm, 
        	    						     services);
        }

        public KeYJavaType resolveType(SchemaVariable sv,
                SVSubstitute instCandidate, SVInstantiations instMap,
                Services services) {
            Sort s = resolveSort(sv, instCandidate, instMap, services);
            return services.getJavaInfo().getKeYJavaType(s);
        }

        
        public String toString() {
            return "\\fieldTargetType(" + fieldSV  + ")";
        }
    }
}