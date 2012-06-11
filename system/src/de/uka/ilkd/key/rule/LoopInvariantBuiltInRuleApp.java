package de.uka.ilkd.key.rule;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.operator.LessThan;
import de.uka.ilkd.key.java.reference.VariableReference;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.speclang.LoopInvariantImpl;
import de.uka.ilkd.key.util.MiscTools;

/**
 * The built in rule app for the loop invariant rule.
 */
public class LoopInvariantBuiltInRuleApp extends AbstractBuiltInRuleApp {

    private final While loop;

    private final LoopInvariant inv;

    public LoopInvariantBuiltInRuleApp(BuiltInRule rule, PosInOccurrence pos) {
        this(rule, pos, null, null);
    }

    protected LoopInvariantBuiltInRuleApp(BuiltInRule rule,
            PosInOccurrence pio, ImmutableList<PosInOccurrence> ifInsts,
            LoopInvariant inv) {
        super(rule, pio, ifInsts);
        assert pio != null;
        this.loop = (While) MiscTools.getActiveStatement(programTerm()
                .javaBlock());
        assert loop != null;
        this.inv = instantiateIndex(inv);
    }
    
    private LoopInvariant instantiateIndex(LoopInvariant rawInv){
    	if (rawInv == null) return null;
    	Map<LocationVariable,Term> invs = rawInv.getInternalInvariants();
    	Term var = rawInv.getInternalVariant();
    	
    	// try to retrieve a loop index variable
    	de.uka.ilkd.key.java.statement.IGuard guard = loop.getGuard();
    	// the guard is expected to be of the form "i < x" and we want to retrieve "i".
    	assert guard.getChildCount() == 1 : "child count: "+guard.getChildCount();
    	ProgramElement guardStatement = guard.getChildAt(0);
    	if (!(guardStatement instanceof LessThan)) 
    		return rawInv;
    	Expression loopIndex = (Expression) ((LessThan)guard.getChildAt(0)).getChildAt(0);
    	if (!( loopIndex instanceof ProgramVariable))
    		return rawInv;
    	final TermBuilder tb = TermBuilder.DF;
		final Term loopIdxVar = tb.var((ProgramVariable)loopIndex);
    	
    	
    	// set up replacement visitor
    	final class IndexTermReplacementVisitor extends Visitor {
    		
    		private Term result;

			@Override
			public void visit(Term visited) {
				result = replace(visited);
			}
			
			public Term getResult(){
				return result;
			}
			
			private Term replace(Term visited){
			    ImmutableArray<Term> subs = visited.subs();
			    if (subs.isEmpty()) {
			    	if (visited.op().name().toString().equals("index"))
			    		return loopIdxVar;
			    	else return visited;
			    } else {
			    	Term[] newSubs = new Term[subs.size()];
			    	for (int i= 0; i < subs.size(); i++)
			    		newSubs[i] = replace(subs.get(i));
			    	return tb.tf().createTerm(visited.op(), new ImmutableArray<Term>(newSubs),
			    			visited.boundVars(), visited.javaBlock());
			    }
			}
		};
		
		// replace it!
		IndexTermReplacementVisitor v = new IndexTermReplacementVisitor();
                Map<LocationVariable,Term> newInvs = new LinkedHashMap<LocationVariable,Term>();
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
		}
		return new LoopInvariantImpl(rawInv.getLoop(), newInvs, rawInv.getInternalModifies(),
				var, rawInv.getInternalSelfTerm(),
				rawInv.getInternalAtPres());
    	
    }

    protected LoopInvariantBuiltInRuleApp(BuiltInRule rule,
            PosInOccurrence pio, LoopInvariant inv) {
        this(rule, pio, null, inv);

    }

    public boolean complete(Services services, boolean isTransaction) {
        return inv != null && loop != null && invariantAvailable(services, isTransaction)
                && (!variantRequired() || variantAvailable());
    }

    public LoopInvariant getInvariant() {
        return inv;
    }

    public While getLoopStatement() {
        return loop;
    }

    public boolean invariantAvailable(Services services, boolean isTransaction) {
        boolean result = inv != null && inv.getInternalInvariants() != null;
        if(result && isTransaction) {
          result = result && (
            inv.getInternalInvariants().get(services.getTypeConverter().getHeapLDT().getHeap()) != null ||
            inv.getInternalInvariants().get(services.getTypeConverter().getHeapLDT().getSavedHeap()) != null);
        }else{
          result = result && 
            inv.getInternalInvariants().get(services.getTypeConverter().getHeapLDT().getHeap()) != null;
        }
        return result;
    }

    public boolean isSufficientlyComplete() {
        return pio != null && loop != null;
    }

    public Term programTerm() {
        if (posInOccurrence() != null) {
            return MiscTools.goBelowUpdates(posInOccurrence().subTerm());
        }
        return null;
    }

    @Override
    public LoopInvariantBuiltInRuleApp replacePos(PosInOccurrence newPos) {
        return new LoopInvariantBuiltInRuleApp(builtInRule, newPos, ifInsts, inv);
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
        // return new InvariantBuiltInRuleApp(builtInRule, newPos, ifInsts,
        // loop, inv);

    }

    public LoopInvariantBuiltInRuleApp setLoopInvariant(LoopInvariant inv) {
        return new LoopInvariantBuiltInRuleApp(builtInRule, pio, ifInsts, inv);
    }

    @Override
    public LoopInvariantBuiltInRuleApp tryToInstantiate(Goal goal) {
        if (inv != null) {
            return this;
        }
        final LoopInvariant inv = retrieveLoopInvariantFromSpecification(goal.proof().getServices());

        if (inv == null) {
            return this;
        }

        return new LoopInvariantBuiltInRuleApp(builtInRule, pio, ifInsts, inv);
    }

    public boolean variantAvailable() {
        return inv != null && inv.getInternalVariant() != null;
    }

    public boolean variantRequired() {
        return ((Modality) programTerm().op()).terminationSensitive();
    }

}
