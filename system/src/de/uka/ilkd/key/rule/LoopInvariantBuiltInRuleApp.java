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

package de.uka.ilkd.key.rule;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.expression.operator.LessThan;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.speclang.LoopInvariantImpl;

/**
 * The built in rule app for the loop invariant rule.
 */
public class LoopInvariantBuiltInRuleApp extends AbstractBuiltInRuleApp {

    private final While loop;

    private final LoopInvariant inv;

    private final List<LocationVariable> heapContext;

    public LoopInvariantBuiltInRuleApp(BuiltInRule rule, PosInOccurrence pos) {
        this(rule, pos, null, null, null);
    }

    protected LoopInvariantBuiltInRuleApp(BuiltInRule rule,
            PosInOccurrence pio, ImmutableList<PosInOccurrence> ifInsts,
            LoopInvariant inv, List<LocationVariable> heapContext) {
        super(rule, pio, ifInsts);
        assert pio != null;
        this.loop = (While) JavaTools.getActiveStatement(programTerm()
                .javaBlock());
        assert loop != null;
        this.inv = instantiateIndexValues(inv);
        this.heapContext = heapContext;
    }
    
    /**
     * Replaces the function symbols "index" and "values" by actual program entities.
     * The index function symbol is a placeholder which stems from translating the <code>\index</code> keyword from JML.
     * The values function symbol is a placeholder which stems from translating the <code>\values</code> keyword from JML.
     * Both are used to refer to a runtime-generated variable.
     * If the loop guard has the form <code>i < x</code>, index is instantiated with <code>i</code>,
     * if the second statement in the loop body has the form <code>v = xxx</code>,
     * where <code>v</code> is a ghost variable of type sequence, values is instantiated with <code>v</code>,
     * otherwise <code>rawInv</code> is returned.
     */
    private LoopInvariant instantiateIndexValues(LoopInvariant rawInv){
    	if (rawInv == null) return null;
    	Map<LocationVariable,Term> invs = rawInv.getInternalInvariants();
    	Term var = rawInv.getInternalVariant();
        final TermBuilder tb = TermBuilder.DF;
    	boolean skipIndex = false;
    	boolean skipValues = false;
    	
    	
    	// try to retrieve a loop index variable
    	de.uka.ilkd.key.java.statement.IGuard guard = loop.getGuard();
    	// the guard is expected to be of the form "i < x" and we want to retrieve "i".
    	assert guard.getChildCount() == 1 : "child count: "+guard.getChildCount();
    	ProgramElement guardStatement = guard.getChildAt(0);
    	skipIndex = !(guardStatement instanceof LessThan);
    	Expression loopIndex = skipIndex? null: (Expression) ((LessThan)guard.getChildAt(0)).getChildAt(0);
    	skipIndex = skipIndex || !( loopIndex instanceof ProgramVariable);
		final Term loopIdxVar = skipIndex? null: tb.var((ProgramVariable)loopIndex);
    	
		// try to retrieve a sequence of values
		Statement body = loop.getBody();
		skipValues = !(body instanceof StatementBlock);
		StatementBlock block = skipValues? null: ((StatementBlock)body);
		Statement last = (skipValues || block.getStatementCount() < 2) ? null: block.getStatementAt(1); // get the second statement
		skipValues = skipValues || !(last instanceof CopyAssignment);
		CopyAssignment assignment = skipValues? null: ((CopyAssignment) last);
		ProgramElement lhs = skipValues? null: assignment.getChildAt(0);
		skipValues = skipValues || !(lhs instanceof ProgramVariable);
		final Term valuesVar = skipValues? null: tb.var((ProgramVariable)lhs);
    	
    	// set up replacement visitors
    	final class IndexTermReplacementVisitor extends DefaultVisitor {
    		
    		private Term result;

			@Override
			public void visit(Term visited) {
				result = replace(visited);
			}
			
			public Term getResult() {
				return result;
			}
			
			private Term replace(Term visited) {
			    ImmutableArray<Term> subs = visited.subs();
			    if (subs.isEmpty()) {
			    	if (visited.op().name().toString().equals("index"))
			    		return loopIdxVar;
			    	else return visited;
			    } else {
			    	Term[] newSubs = new Term[subs.size()];
			    	for (int i= 0; i < subs.size(); i++)
			    		newSubs[i] = replace(subs.get(i));
				return tb.tf().createTerm(
				        visited.op(), new ImmutableArray<Term>(newSubs),
				        visited.boundVars(), visited.javaBlock(),
				        visited.getLabels());
			    }
			}
		};
        final class ValuesTermReplacementVisitor extends DefaultVisitor {
            
            private Term result;

            @Override
            public void visit(Term visited) {
                result = replace(visited);
            }
            
            public Term getResult() {
                return result;
            }
            
            private Term replace(Term visited) {
                ImmutableArray<Term> subs = visited.subs();
                if (subs.isEmpty()) {
                    if (visited.op().name().toString().equals("values"))
                        return valuesVar;
                    else return visited;
                } else {
                    Term[] newSubs = new Term[subs.size()];
                    for (int i= 0; i < subs.size(); i++)
                        newSubs[i] = replace(subs.get(i));
                    return tb.tf().createTerm(visited.op(), new ImmutableArray<Term>(newSubs),
                            visited.boundVars(), visited.javaBlock(), visited.getLabels());
                }
            }
        };
		
		// replace index
        Map<LocationVariable,Term> newInvs = new LinkedHashMap<LocationVariable,Term>(invs);
		if (!skipIndex){
		IndexTermReplacementVisitor v = new IndexTermReplacementVisitor();
                for(LocationVariable heap : invs.keySet()) {
                   Term inv = invs.get(heap);
		   if (inv != null) {
		     v.visit(inv);
		     inv = v.getResult();
                     newInvs.put(heap, inv);
  		   }                   
                }
		if (var != null) {
		    v.visit(var);
		    var = v.getResult();
		}}
		
		// replace values
        if (!skipValues){
        ValuesTermReplacementVisitor v = new ValuesTermReplacementVisitor();
                for(LocationVariable heap : invs.keySet()) {
                   Term inv = invs.get(heap);
           if (inv != null) {
             v.visit(inv);
             inv = v.getResult();
                     newInvs.put(heap, inv);
           }                   
                }
        if (var != null) {
            v.visit(var);
            var = v.getResult();
        }}
		return new LoopInvariantImpl(rawInv.getLoop(), rawInv.getTarget(),
		                             rawInv.getKJT(), newInvs,
		                             rawInv.getInternalModifies(), var,
		                             rawInv.getInternalSelfTerm(),
		                             rawInv.getInternalAtPres());
    	
    }

    protected LoopInvariantBuiltInRuleApp(BuiltInRule rule,
            PosInOccurrence pio, LoopInvariant inv) {
        this(rule, pio, null, inv, null);

    }

    public boolean complete() {
        return inv != null && loop != null && invariantAvailable()
                && (!variantRequired() || variantAvailable());
    }

    public LoopInvariant getInvariant() {
        return inv;
    }

    public While getLoopStatement() {
        return loop;
    }

    public boolean invariantAvailable() {
        boolean result = inv != null && inv.getInternalInvariants() != null;
        if(result) {
          Map<LocationVariable,Term> invs = inv.getInternalInvariants();
          result = false;
          for(LocationVariable heap : heapContext) {
            if(invs.get(heap) != null) {
              result = true;
              break;
            }
          }
        }
        return result;
    }

    public boolean isSufficientlyComplete() {
        return pio != null && loop != null;
    }

    public Term programTerm() {
        if (posInOccurrence() != null) {
            return TermBuilder.DF.goBelowUpdates(posInOccurrence().subTerm());
        }
        return null;
    }

    @Override
    public LoopInvariantBuiltInRuleApp replacePos(PosInOccurrence newPos) {
        return new LoopInvariantBuiltInRuleApp(builtInRule, newPos, ifInsts, inv, heapContext);
    }

    public LoopInvariant retrieveLoopInvariantFromSpecification(
            Services services) {
        return services.getSpecificationRepository().getLoopInvariant(loop);
    }

    @Override
    public LoopInvariantBuiltInRuleApp setIfInsts(
            ImmutableList<PosInOccurrence> ifInsts) {
        setMutable(ifInsts);
        return this;

    }

    public LoopInvariantBuiltInRuleApp setLoopInvariant(LoopInvariant inv) {
        return new LoopInvariantBuiltInRuleApp(builtInRule, pio, ifInsts, inv, heapContext);
    }

    @Override
    public LoopInvariantBuiltInRuleApp tryToInstantiate(Goal goal) {
        if (inv != null) {
            return this;
        }
        final LoopInvariant inv = retrieveLoopInvariantFromSpecification(goal.proof().getServices());
        Modality m = (Modality)programTerm().op();
        boolean transaction = (m == Modality.DIA_TRANSACTION || m == Modality.BOX_TRANSACTION); 
        return new LoopInvariantBuiltInRuleApp(builtInRule, pio, ifInsts, inv, HeapContext.getModHeaps(goal.proof().getServices(), transaction));
    }

    public boolean variantAvailable() {
        return inv != null && inv.getInternalVariant() != null;
    }

    public boolean variantRequired() {
        return ((Modality) programTerm().op()).terminationSensitive();
    }

    @Override
    public List<LocationVariable> getHeapContext() {
      return heapContext;
    }   

}
