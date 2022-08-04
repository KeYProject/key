package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.ldt.DependenciesLDT;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
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
        final Term anonUpdate = creatUpdates(loopInvariant);
        constructUsecase(loopInvariant, anonUpdate, loopGuard);
    }

    private Term findNoW(Term innerLI){
        Term mod = tb.allLocs();
        if (innerLI.op()==depLDT.getNoW()){
            mod = tb.setMinus(mod, innerLI.sub(0));
        } else {
            for (Term t:innerLI.subs()){
                findNoW(t);
            }
        }
        return mod;
    }
    private Term creatUpdates(Term innerLI) {
        Term mod = findNoW(innerLI);

        final Name heapPrimeName = new Name(tb.newName(tb.getBaseHeap()+"_Prime"));
        final Function heapPrimeFunc = new Function(heapPrimeName, heapLDT.targetSort(), true);
        services.getNamespaces().functions().addSafely(heapPrimeFunc);
        final Term heapPrime = tb.func(heapPrimeFunc);
        Term heapAnonUpdate = tb.anonUpd(heapLDT.getHeap(), mod, heapPrime);

        final Name freshConsSymb = new Name(tb.newName("f_" + tb.newName(Sort.ANY), services.getNamespaces()));
        final Function freshConsFunc = new Function(freshConsSymb, Sort.ANY, true);
        services.getNamespaces().functions().addSafely(freshConsFunc);
        final Term freshCons = tb.func(freshConsFunc);

        Term anonEv = tb.anonEventUpdate(freshCons);

        Term result = tb.parallel(heapAnonUpdate, anonEv);
        return result;
    }

    private void constructUsecase(Term innerLI, Term anonUpdAndEv, Term guard) {
        if(guard!=null) {
            //Ante:
            Term updatedLeft = tb.apply(anonUpdAndEv, tb.and(innerLI, tb.not(guard)));
            goal.addFormula(new SequentFormula(updatedLeft), true, true);
            //Succ:
            SequentFormula programFormula = null;// hand the sequentformula over and remove the code below
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

            target = tb.prog((Modality) target.op(), JavaBlock.createJavaBlock(withoutInnerLoop), target.sub(0));

            Term updatedRight = tb.applySequential(updatesAndTarget.first,
                    tb.apply(anonUpdAndEv, target));

            SequentFormula updatedRightSF = new SequentFormula(updatedRight);

            goal.changeFormula(updatedRightSF,
                    new PosInOccurrence(programFormula, PosInTerm.getTopLevel(), false));
        }
    }
}
