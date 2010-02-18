// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.rule.metaconstruct;

import java.util.Iterator;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementContainer;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.UpdateFactory;
import de.uka.ilkd.key.logic.op.*;
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

        final ImmutableList<ProgramVariable> pvs = collectRelevantPVs(term, services);
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
    
    private static Term createHeapDependentFunctionTerm(ImmutableList<ProgramVariable> l,
                                                        Services services){
        Term[] subs = new Term[l.size()];
        Sort[] subSorts = new Sort[l.size()];
        int i=0;
        TermFactory tf = TermFactory.DEFAULT;
        for (ProgramVariable aL : l) {
            ProgramVariable pv = aL;
            subs[i] = tf.createVariableTerm(pv);
            subSorts[i++] = pv.sort();
        }
        ImmutableArray<Sort> aos = new ImmutableArray<Sort>(subSorts);
        Name anonName = VariableNameProposer.DEFAULT.getNewName(services,
                new Name("anon"));
        Function anon = new NonRigidHeapDependentFunction(anonName, Sort.FORMULA, aos);
        services.getNamespaces().functions().add(anon);
        services.addNameProposal(anonName);
        return tf.createFunctionTerm(anon, subs);
    }
    
    private static ImmutableList<ProgramVariable> collectRelevantPVs(Term t, 
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
         private ImmutableList<ProgramVariable> declaredPVs
             = ImmutableSLList.<ProgramVariable>nil();
         private ImmutableList<ProgramVariable> freePVs
             = ImmutableSLList.<ProgramVariable>nil();
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
         public ImmutableList<ProgramVariable> result() {
             //remove duplicates
             ImmutableList<ProgramVariable> result = ImmutableSLList.<ProgramVariable>nil();
             for (ProgramVariable freePV : freePVs) {
                 ProgramVariable pv = freePV;
                 if (!result.contains(pv)) {
                     result = result.prepend(pv);
                 }
             }
             return result;
         }
     }    
}
