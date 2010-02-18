// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

import java.util.Iterator;
import java.util.Map;

import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.visitor.ProgVarReplaceVisitor;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.inst.*;

/**
 * Replaces program variables.
 */
public class ProgVarReplacer {
    
    /**
     * map specifying the replacements to be done
     */
    protected final Map map;
    
    
    /**
     * The services object
     */
    private final Services services;


    /**
     * creates a ProgVarReplacer that replaces program variables as specified
     * by the map parameter
     */
    public ProgVarReplacer(Map map, Services services) {
        this.map = map;
        this.services = services;
    }


    /**
     * merges "next" into "base"
     * precondition:
     *   "next" is the result of replacing in "base" the formula at position
     *   "idx" by calling Semisequent.replace()
     *   (this implies that "next" contains exactly one removed and one added
     *   formula)
     */
    private void mergeSemiCIs(SemisequentChangeInfo base,
                              SemisequentChangeInfo next,
                              int idx) {
        assert next.modifiedFormulas().isEmpty();

        Iterator<ConstrainedFormula> remIt = next.removedFormulas().iterator();
        assert remIt.hasNext();
        ConstrainedFormula remCf = remIt.next();
        assert !remIt.hasNext();
        base.removedFormula(idx, remCf);

        Iterator<ConstrainedFormula> addIt = next.addedFormulas().iterator();
        assert addIt.hasNext();
        ConstrainedFormula addCf = addIt.next();
        assert !addIt.hasNext();
        base.addedFormula(idx, addCf);

        base.setFormulaList(next.getFormulaList());
        base.setSemisequent(next.semisequent());
    }


    /**
     * replaces in a goal
     */
    public void replace(Goal goal) {
	//globals
    	ImmutableSet<ProgramVariable> set = replace(goal.getGlobalProgVars());
	goal.setGlobalProgVars(set);

	//taclet apps
	replace(goal.ruleAppIndex().tacletIndex());

	//sequent
	SequentChangeInfo sci = replace(goal.sequent());
	goal.setSequent(sci);
    }


    /**
     * replaces in a set
     */
    public ImmutableSet<ProgramVariable> replace(ImmutableSet<ProgramVariable> vars) {
    	ImmutableSet<ProgramVariable> result = vars;

    	for (final ProgramVariable var : vars) {
	    ProgramVariable newVar = (ProgramVariable)map.get(var);
	    if(newVar != null) {
	    	result = result.remove(var);
	    	result = result.add(newVar);
	    }
	}

	return result;
    }


    /**
     * replaces in the partially instantiated apps of a taclet index
     */
    public void replace(TacletIndex tacletIndex) {
	ImmutableList<NoPosTacletApp> noPosTacletApps
		= tacletIndex.getPartialInstantiatedApps();
	ImmutableSet<NoPosTacletApp> appsToBeRemoved, appsToBeAdded;
	appsToBeRemoved = DefaultImmutableSet.<NoPosTacletApp>nil();
	appsToBeAdded   = DefaultImmutableSet.<NoPosTacletApp>nil();

        for (NoPosTacletApp noPosTacletApp1 : noPosTacletApps) {
            NoPosTacletApp noPosTacletApp = noPosTacletApp1;
            SVInstantiations insts = noPosTacletApp.instantiations();

            SVInstantiations newInsts = replace(insts);

            if (newInsts != insts) {
                NoPosTacletApp newNoPosTacletApp
                        = NoPosTacletApp.createNoPosTacletApp(
                        noPosTacletApp.taclet(),
                        newInsts,
                        noPosTacletApp.constraint(),
                        noPosTacletApp.newMetavariables(),
                        noPosTacletApp.ifFormulaInstantiations());
                appsToBeRemoved = appsToBeRemoved.add(noPosTacletApp);
                appsToBeAdded = appsToBeAdded.add(newNoPosTacletApp);
            }
        }

	tacletIndex.removeTaclets(appsToBeRemoved);
	tacletIndex.addTaclets(appsToBeAdded);
    }


    /**
     * replaces in an SVInstantiations
     */
    public SVInstantiations replace(SVInstantiations insts) {
   	SVInstantiations result = insts;

    	Iterator<ImmutableMapEntry<SchemaVariable,InstantiationEntry>> it;
	it = insts.pairIterator();
	while(it.hasNext()) {
	    ImmutableMapEntry<SchemaVariable,InstantiationEntry> e = it.next();
	    SchemaVariable sv     = e.key();
	    InstantiationEntry ie = e.value();
	    Object inst = ie.getInstantiation();

	    if(ie instanceof ContextInstantiationEntry) {
		ProgramElement pe = (ProgramElement) inst;
		ProgramElement newPe = replace(pe);
		if(newPe != pe) {
		    ContextInstantiationEntry cie = (ContextInstantiationEntry) ie;
		    result = result.replace(cie.prefix(),
					    cie.suffix(),
					    cie.activeStatementContext(),
					    newPe);
		}
	    } else if(ie instanceof OperatorInstantiation) {
	    	/*nothing to be done (currently)*/
	    } else if(ie instanceof ProgramInstantiation) {
		ProgramElement pe = (ProgramElement) inst;
		ProgramElement newPe = replace(pe);
		if(newPe != pe) {
		    result = result.replace(sv, newPe);
		}
	    } else if(ie instanceof ProgramListInstantiation) {
		ImmutableArray<ProgramElement> a = (ImmutableArray<ProgramElement>) inst;
		int size = a.size();
                ProgramElement[] array = new ProgramElement[size];

		boolean changedSomething = false;
		for(int i = 0; i < size; i++) {
                    ProgramElement pe = a.get(i);
		    array[i] = replace(pe);
		    if(array[i] != pe) {
		    	changedSomething = true;
		    }
		}

		if(changedSomething) {
		    ImmutableArray<ProgramElement> newA = new ImmutableArray<ProgramElement>(array);
		    result = result.replace(sv, newA);
		}
	    } else if(ie instanceof TermInstantiation) {
		Term t = (Term) inst;
		Term newT = replace(t);
		if(newT != t) {
		    result = result.replace(sv, newT);
		}
	    } else {
		assert false : "unexpected subtype of InstantiationEntry";
	    }
	}

	return result;
    }


    /**
     * replaces in a sequent
     */
    public SequentChangeInfo replace(Sequent s) {
        SemisequentChangeInfo anteCI = replace(s.antecedent());
        SemisequentChangeInfo succCI = replace(s.succedent());

        Semisequent newAntecedent = anteCI.semisequent();
        Semisequent newSuccedent  = succCI.semisequent();

        Sequent newSequent = Sequent.createSequent(newAntecedent,
                                                   newSuccedent);

        SequentChangeInfo result = SequentChangeInfo.createSequentChangeInfo
                                              (anteCI, succCI, newSequent, s);
        return result;
    }


    /**
     * replaces in a semisequent
     */
    public SemisequentChangeInfo replace(Semisequent s) {
    	SemisequentChangeInfo result = new SemisequentChangeInfo();
        result.setFormulaList(s.toList());
        result.setSemisequent(s);

        final Iterator<ConstrainedFormula> it = s.iterator();
        
        for (int formulaNumber = 0; it.hasNext(); formulaNumber++) {            
            final ConstrainedFormula oldcf = it.next();
            final ConstrainedFormula newcf = replace(oldcf);

            if(newcf != oldcf) {
                SemisequentChangeInfo semiCI
                                      = result.semisequent().
                                      replace(formulaNumber, newcf);
                mergeSemiCIs(result, semiCI, formulaNumber);
            }
        }

        return result;
    }


    /**
     * replaces in a constrained formula
     */
    public ConstrainedFormula replace(ConstrainedFormula cf) {
        ConstrainedFormula result = cf;

	final Term newFormula = replace(cf.formula());

	if(newFormula != cf.formula()) {
            result = new ConstrainedFormula(newFormula, cf.constraint());
	}
        return result;
    }
    
    public Term replaceProgramVariable(Term t) {
        final ProgramVariable pv = (ProgramVariable) t.op();
        Object o = map.get(pv);
        if (o instanceof ProgramVariable) {
            return TermFactory.DEFAULT.createVariableTerm((ProgramVariable)o);
        } else if (o instanceof Term) {
            return (Term) o;
        }
        return t;
    }
    
    protected Term replaceQuanUpdateTerm(Term t) {
        assert t.op() instanceof QuanUpdateOperator;
        
        Term result = t;
        boolean changed = false;
        
        final QuanUpdateOperator iuop = (QuanUpdateOperator) t.op();
        
        final Term locs[] = new Term[iuop.locationCount()];
        final Term vals[] = new Term[iuop.locationCount()];
        final Term guards[] = new Term[iuop.locationCount()];
        final ImmutableArray<QuantifiableVariable>[] qvars 
            = new ImmutableArray[iuop.locationCount()];
        
        for (int i=0; i<iuop.locationCount(); i++) {
            final Term location = iuop.location(t, i);
            locs[i]   = replace(location);
            changed   = changed || (locs[i] != location);
            final Term value = iuop.value(t, i);
            vals[i]   = replace(value);
            changed   = changed || vals[i] != value;
            final Term guard = iuop.guard(t, i);
            guards[i] = replace(guard);
            changed   = changed || guards[i] != guard;
            final ImmutableArray<QuantifiableVariable> boundVars = iuop.boundVars(t,i);
            qvars[i]  = boundVars;
            changed   = changed || qvars[i] != boundVars;
        }        
        final Term target =  replace(iuop.target(t));
        changed = changed || target != iuop.target(t);
        
        if (changed) {
            result = TermFactory.DEFAULT.createQuanUpdateTerm
            (qvars, guards, locs, vals, target);
        }        
        
        return result; 
    }
    
    /**
     * replaces in a term
     */
    public Term replace(Term t) {
        final Operator op = t.op();
        if(op instanceof QuanUpdateOperator) {
            return replaceQuanUpdateTerm(t);
        } else if (op instanceof ProgramVariable) {
            return replaceProgramVariable(t);       
        } else {
            return standardReplace(t);
        }    
    }

    /**
     * @param t the Term where to perform the replacement
     * @return the replaced term
     */
    protected Term standardReplace(Term t) {
        Term result = t;
        
        final Term newSubTerms[] = new Term[t.arity()];
        final ImmutableArray<QuantifiableVariable>[] boundVars =
            new ImmutableArray [t.arity ()];

        boolean changedSubTerm = false;
        
        for(int i = 0, ar = t.arity(); i < ar; i++) {
            final Term subTerm = t.sub(i);
            newSubTerms[i] = replace(subTerm);
            if(newSubTerms[i] != subTerm) {
                changedSubTerm = true;
            }
            boundVars[i] = t.varsBoundHere(i);
        }

        final JavaBlock jb = t.javaBlock();
        JavaBlock newJb = jb;
        if (!jb.isEmpty()) {
            Statement s = (Statement)jb.program();
            Statement newS = (Statement)replace(s);
            if(newS != s) {
                newJb = JavaBlock.createJavaBlock((StatementBlock)newS);
            }
        }

        if(changedSubTerm || newJb != jb) {                               
            result = TermFactory.DEFAULT.createTerm(t.op(),
                    newSubTerms,
                    boundVars,
                    newJb);
        }
        return result;
    }

    public LocationDescriptor replace(LocationDescriptor loc) {
        if(loc instanceof BasicLocationDescriptor) {
            BasicLocationDescriptor bloc = (BasicLocationDescriptor) loc;
            return new BasicLocationDescriptor(replace(bloc.getFormula()), 
                                               replace(bloc.getLocTerm()));
        } else {
            return loc;
        }
    }

    /**
     * replaces in a statement
     */
    public ProgramElement replace(ProgramElement pe) {
        ProgVarReplaceVisitor pvrv = new ProgVarReplaceVisitor(pe, 
                                                               map, 
                                                               false, 
                                                               services);
	pvrv.start();
	return pvrv.result();
    }

    public String toString(){
	return map.toString();
    }
}
