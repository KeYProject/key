package de.uka.ilkd.key.rule.metaconstruct;

import java.util.*;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ArrayOfSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.VariableNameProposer;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.UpdateSimplifier;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.updatesimplifier.Update;

public class LocationDependentFunction extends AbstractMetaOperator {
    
    private static Term updTerm = null;
    private static Term heapDepFuncTerm = null;
    
    private Term getHeapDepFuncTermFor(Term term, Services services){        
        if (term.sub(0) == updTerm) {
            return heapDepFuncTerm;
        }
        updTerm = term.sub(0);

        final ListOfProgramVariable pvs = collectRelevantPVs(term, services);
        heapDepFuncTerm = createHeapDependentFunctionTerm(pvs, services);        
        Map map = AtPreEquations.getAtPreFunctions(updTerm, services);
        OpReplacer or = new OpReplacer(map);
        Term preUpdTerm = or.replace(updTerm);
        if ( !( updTerm.op () instanceof IUpdateOperator ) ) return heapDepFuncTerm;
        final Update upd = Update.createUpdate ( preUpdTerm );
        final UpdateFactory uf =
            new UpdateFactory ( services, new UpdateSimplifier () );
        return heapDepFuncTerm = uf.prepend(upd, heapDepFuncTerm);
    }
    
    public LocationDependentFunction() {
        super(new Name("#locDepFunc"), 2);
    }
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.op.MetaOperator#calculate(de.uka.ilkd.key.logic.Term, de.uka.ilkd.key.rule.inst.SVInstantiations, de.uka.ilkd.key.java.Services)
     */
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        return getHeapDepFuncTermFor(term, services);
    }
    
    private static Term createHeapDependentFunctionTerm(ListOfProgramVariable l,
                                                        Services services){
        Term[] subs = new Term[l.size()];
        Sort[] subSorts = new Sort[l.size()];
        int i=0;
        TermFactory tf = TermFactory.DEFAULT;
        IteratorOfProgramVariable it = l.iterator();
        while(it.hasNext()){
            ProgramVariable pv = it.next();
            subs[i] = tf.createVariableTerm(pv);
            subSorts[i++] = pv.sort();
        }
        ArrayOfSort aos = new ArrayOfSort(subSorts);
        Name anonName = VariableNameProposer.DEFAULT.getNewName(services,
                new Name("anon"));
        Function anon = new NonRigidHeapDependentFunction(anonName, Sort.FORMULA, aos);
        services.getNamespaces().functions().add(anon);
        services.getProof().addNameProposal(anonName);
        return tf.createFunctionTerm(anon, subs);
    }
    
    private static ListOfProgramVariable collectRelevantPVs(Term t, 
                                                            Services services){
        LoopStatement loop = getLoop(t.sub(1).javaBlock().program());
        FreePVCollector pc = new FreePVCollector(loop, services);
        pc.start();
        return pc.result();
    }
    
    private static LoopStatement getLoop(ProgramElement pe){
        if(pe instanceof LoopStatement){
            return (LoopStatement) pe;
        }
        if(pe instanceof StatementContainer){
            return getLoop(((StatementContainer) pe).getStatementAt(0));
        }
        //shouldn't happen.
        return null;
    }
                
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.op.Operator#validTopLevel(de.uka.ilkd.key.logic.Term)
     */
    public boolean validTopLevel(Term term) {
        return term.arity()==2 && term.sub(1).sort()==Sort.FORMULA;
    }

    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.op.Operator#sort(de.uka.ilkd.key.logic.Term[])
     */
    public Sort sort(Term[] term) {
        return Sort.FORMULA;
    }
    

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.op.Operator#isRigid(de.uka.ilkd.key.logic.Term)
     */
    public boolean isRigid(Term term) {
        return false;
    }

    
    /** (non-Javadoc)
     * by default meta operators do not match anything 
     * @see de.uka.ilkd.key.logic.op.Operator#match(SVSubstitute, de.uka.ilkd.key.rule.MatchConditions, de.uka.ilkd.key.java.Services)
     */
    public MatchConditions match(SVSubstitute subst, MatchConditions mc,
            Services services) {
        return null;
    }
    
    
    /**
      * Collects the local program variables which have free occurrences
      * in a program.
      */
     private static class FreePVCollector extends JavaASTVisitor {
         private ListOfProgramVariable declaredPVs
             = SLListOfProgramVariable.EMPTY_LIST;
         private ListOfProgramVariable freePVs
             = SLListOfProgramVariable.EMPTY_LIST;
         public FreePVCollector(ProgramElement root, Services services) {
             super(root, services);
         }
         protected void doDefaultAction(SourceElement node) {
             if(node instanceof ProgramVariable) {
                 ProgramVariable pv = (ProgramVariable) node;
                 if(!pv.isMember() && !declaredPVs.contains(pv)) {
                     freePVs = freePVs.prepend(pv);
                 }
             } else if(node instanceof VariableSpecification) {
                 VariableSpecification vs = (VariableSpecification) node;
                 ProgramVariable pv = (ProgramVariable) vs.getProgramVariable();
                 if(!pv.isMember()) {
                     assert !declaredPVs.contains(pv);
                     declaredPVs = declaredPVs.prepend(pv);
                     
                     //occurrence in the declaration itself does not count
                     assert freePVs.contains(pv); 
                     freePVs = freePVs.removeFirst(pv);
                 }
             }
         }
         public ListOfProgramVariable result() {
             //remove duplicates
             ListOfProgramVariable result = SLListOfProgramVariable.EMPTY_LIST;
             IteratorOfProgramVariable it = freePVs.iterator();
             while(it.hasNext()) {
                 ProgramVariable pv = it.next();
                 if(!result.contains(pv)) {
                     result = result.prepend(pv);
                 }
             }
             return result;
         }
     }    
}
