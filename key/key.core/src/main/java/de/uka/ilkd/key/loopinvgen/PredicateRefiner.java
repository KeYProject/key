package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.ldt.DependenciesLDT;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.util.Pair;

import java.util.Set;

public abstract class PredicateRefiner {
    protected final Services services;
    protected final TermBuilder tb;
    protected final DependenciesLDT depLDT;
    protected final IntegerLDT intLDT;
    protected final LocSetLDT locsetLDT;
    protected final Sequent sequent;
    protected final SideProof sProof;

    public PredicateRefiner(Sequent sequent, Services services) {
        this.services = services;
        this.tb = services.getTermBuilder();

        final TypeConverter typeConverter = services.getTypeConverter();
        this.intLDT = typeConverter.getIntegerLDT();
        this.depLDT = typeConverter.getDependenciesLDT();
        this.locsetLDT = typeConverter.getLocSetLDT();

        this.sequent = simplify(filter(sequent));
        this.sProof = new SideProof(services, this.sequent);
    }

    public abstract Pair<Set<Term>, Set<Term>> refine();

    protected Sequent filter(Sequent originalSequent) {
        Sequent sequent = Sequent.EMPTY_SEQUENT;
        for (SequentFormula sequentFormula : originalSequent.antecedent()) {
            sequent = sequent.addFormula(sequentFormula, true, false).sequent();
        }

        for (SequentFormula sequentFormula : originalSequent.succedent()) {
            if (!sequentFormula.formula().containsJavaBlockRecursive()) {
                sequent = sequent.addFormula(sequentFormula, false, false).sequent();
            }
        }
        return sequent;
    }

    protected boolean sequentImpliesPredicate(Term pred) {
//        System.out.println("sequentImpliesPredicate is called for: "+pred);

        final Sequent sideSeq = sequent.addFormula(new SequentFormula(pred), false, true).sequent();
        final boolean provable = SideProof.isProvable(sideSeq, 100000, true, services);
        if(!provable)
            System.out.println(pred+ " can't be proven in Seq: "+ sideSeq);
//        System.out.println(provable);
        return provable;
    }

    protected Sequent simplify(Sequent sequent) {
        try {
            ApplyStrategyInfo info = SideProof.isProvableHelper(sequent, 1000, true, false, services);
            if (info.getProof().openGoals().size() != 1) {
                throw new ProofInputException("Illegal number of goals. Open goals: " + info.getProof().openGoals().size());
            }
            sequent = info.getProof().openGoals().head().sequent();
        } catch (ProofInputException e) {
            e.printStackTrace();
        }
        return sequent;
    }
}
