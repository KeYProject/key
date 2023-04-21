package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.ldt.DependenciesLDT;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.metaconstruct.CreateLocalAnonUpdate;
import de.uka.ilkd.key.rule.metaconstruct.ReplaceWhileLoop;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.Pair;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.util.HashSet;
import java.util.Set;

public class NestedLoopUsecaseRuleImp{

    private final Goal goal;
    private final Services services;
    private final TermBuilder tb;

    private final DependenciesLDT depLDT;
    private final HeapLDT heapLDT;

    public NestedLoopUsecaseRuleImp(Goal g) {
        goal = g;
        services = g.proof().getServices();
        tb = services.getTermBuilder();
        depLDT = services.getTypeConverter().getDependenciesLDT();
        heapLDT = services.getTypeConverter().getHeapLDT();
    }

    public void nestedLoopUsecase(Goal g, PosInOccurrence pos, LoopSpecification innerSpec, Term loopGuard) {
        final Term loopInvariant = innerSpec.getInvariant(services);
        final Term anonUpdate = creatUpdates(loopInvariant, pos);
        constructUsecase(loopInvariant, anonUpdate, loopGuard);
    }

    private Term findWPRed(Term innerLI, Term mod){

        final Term arr = tb.var((LocationVariable) services.getNamespaces().programVariables().lookup("a"));
        return tb.matrixRange(tb.getBaseHeap(),
                arr,
                tb.zero(), tb.dotLength(arr),
                tb.zero(), tb.dotLength(tb.dotArr(arr, tb.zero()))
        );
    }
    private Term findNoW(Term innerLI, Term mod){
        if (innerLI.op()==depLDT.getNoW()){
            mod = tb.setMinus(mod, innerLI.sub(0));
        } else {
            for (Term t:innerLI.subs()){
                mod = findNoW(t, mod);
            }
        }
        return mod;
    }
    private Term creatUpdates(Term innerLI, PosInOccurrence pos) {
        Term mod = findWPRed(innerLI, tb.allLocs());//findNoW

        //anonymizes the heap
        final Name heapPrimeName = new Name(tb.newName(tb.getBaseHeap()+"_Prime"));
        final Function heapPrimeFunc = new Function(heapPrimeName, heapLDT.targetSort(), true);
        services.getNamespaces().functions().addSafely(heapPrimeFunc);
        final Term heapPrime = tb.func(heapPrimeFunc);
        final Term heapAnonUpdate = tb.anonUpd(heapLDT.getHeap(), mod, heapPrime);

        //anonymizes the events
        Sort intS = services.getTypeConverter().getIntegerLDT().targetSort();
        final Name freshConsSymb = new Name(tb.newName("f_" + tb.newName(intS), services.getNamespaces()));
        final Function freshConsFunc = new Function(freshConsSymb, intS, true);
        services.getNamespaces().functions().addSafely(freshConsFunc);
        final Term freshCons = tb.func(freshConsFunc);
        final Term anonEv = tb.anonEventUpdate(freshCons);

        // creates the term transformer #createLocalAnonUpdate(\<{ while ... }\>true) which computes
        // the anonymizing update for the local variables potentially changed by the INNER while loop
        CreateLocalAnonUpdate clau = new CreateLocalAnonUpdate();
        final Term loopTerm = tb.goBelowUpdates(pos.sequentFormula().formula());
        final StatementBlock prg = (StatementBlock) loopTerm.javaBlock().program();
        final StatementBlock loop = new StatementBlock((Statement) prg.getStatementAt(0).getFirstElement());
        final Term termTransformerTerm = tb.tf().createTerm(clau, tb.dia(JavaBlock.createJavaBlock(loop), tb.tt()));
        final Term anonLocal = clau.transform(termTransformerTerm, SVInstantiations.EMPTY_SVINSTANTIATIONS, services);

        Term result = tb.parallel(anonLocal, heapAnonUpdate, anonEv);
        return result;
    }

    private void constructUsecase(Term innerLI, Term anonUpdAndEv, Term guard) {
        if(guard!=null) {
            //Ante:
            Term updatedLeft = tb.apply(anonUpdAndEv, tb.and(innerLI, tb.not(guard)));
            goal.addFormula(new SequentFormula(updatedLeft), true, true);
            //Succ:
            SequentFormula programFormula = null;// hand the sequent formula over and remove the code below
            for (SequentFormula sf : goal.sequent().succedent()) {
                if ((tb.goBelowUpdates(sf.formula()).op() instanceof Modality)) { // FIX check for correct formula
                    programFormula = sf;
                    break;
                }
            }

            Pair<ImmutableList<Term>, Term> updatesAndTarget = tb.goBelowUpdates2(programFormula.formula());

            Term target = updatesAndTarget.second;
            ReplaceWhileLoop rwl = new ReplaceWhileLoop(programFormula.formula().javaBlock().program(),
                    null, services);
            rwl.start();

            StatementBlock withoutInnerLoop  = (StatementBlock) rwl.result();
//            System.out.println("without: "+withoutInnerLoop);
            target = tb.prog((Modality) target.op(), JavaBlock.createJavaBlock(withoutInnerLoop), target.sub(0));

            Term updatedRight = tb.applySequential(updatesAndTarget.first,
                    tb.apply(anonUpdAndEv, target));

            SequentFormula updatedRightSF = new SequentFormula(updatedRight);

            goal.changeFormula(updatedRightSF,
                    new PosInOccurrence(programFormula, PosInTerm.getTopLevel(), false));
        }
    }
}
