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
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.util.Pair;

import java.util.HashMap;
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

    public Sequent filter(Sequent sequent) {
        return filter(sequent,services);
    }
    public static Sequent filter(Sequent originalSequent, Services services) {
        Sequent sequent = Sequent.EMPTY_SEQUENT;
        DependenciesLDT depLDT = services.getTypeConverter().getDependenciesLDT();
        IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        Function numberSymbol = integerLDT.getNumberSymbol();

        HashMap<Operator, HashMap<Term, Term>> labels = new HashMap<>();
        for (SequentFormula sf:originalSequent.antecedent()) {
            Operator op = sf.formula().op();
            if (depLDT.isHistoryPredicate(op)) {
                HashMap<Term, Term> loc2label = labels.get(op);
                Term loc = sf.formula().sub(0);
                if (loc2label == null) {
                    loc2label = new HashMap<>();
                    loc2label.put(loc, sf.formula().sub(1));
                    labels.put(op, loc2label);
                } else {
                    Term label = loc2label.get(loc);
                    if (label == null) {
                        loc2label.put(loc, sf.formula().sub(1));
                    } else if (label.op() == numberSymbol) {
                        Term currentLabel = sf.formula().sub(1);
                        Term minimalLabel = currentLabel;
                        if (currentLabel.op() == numberSymbol) {
                            Integer current = Integer.parseInt(integerLDT.toNumberString(currentLabel.sub(0)));
                            Integer inMap = Integer.parseInt(integerLDT.toNumberString(label.sub(0)));
                            if (inMap.compareTo(current) < 0) {
                                minimalLabel = label;
                            }
                        }
                        loc2label.put(loc, minimalLabel);
                    }
                }
            }
        }

        boolean doNotAdd = false;
        for (SequentFormula sequentFormula : originalSequent.antecedent()) {
            Operator sfOp = sequentFormula.formula().op();
            for (Operator op: strongestOp(sfOp,depLDT)) {
                if (labels.containsKey(op)) {
                    HashMap<Term, Term> loc2label = labels.get(op);
                    Term minLabel = loc2label.get(sequentFormula.formula().sub(0));
                    if (minLabel == null ||
                            (minLabel.op() != numberSymbol || minLabel.equalsModRenaming(sequentFormula.formula().sub(1)))) {
                        //sequent = sequent.addFormula(sequentFormula, true, false).sequent();
                        doNotAdd = (sfOp != op);
                        break;
                    }
                    doNotAdd = true;
                    //else {
                    // System.out.println("Discarding " + ProofSaver.printAnything(sequentFormula.formula(), null));
                    //}
                } else {
                    doNotAdd =
                            depLDT.isHistoryPredicate(op);
                }
            }
            if (!doNotAdd) {
                sequent = sequent.addFormula(sequentFormula, true, false).sequent();
            }
        }

        for (SequentFormula sequentFormula : originalSequent.succedent()) {
//            System.out.println("sequentFormula: " + sequentFormula);
            if (!sequentFormula.formula().containsJavaBlockRecursive()) {
                sequent = sequent.addFormula(sequentFormula, false, false).sequent();
//                System.out.println("added");
            }
        }
//        System.out.println("MMMMMM Sequent: " +
//                ProofSaver.printAnything(sequent, null));
        return sequent;
    }

    private static Operator[] strongestOp(Operator op, DependenciesLDT ldt) {
        if (op == ldt.getNoRaWAtHistory() || op == ldt.getNoWaRAtHistory()) {
            return new Operator[] { ldt.getNoRAtHistory(), ldt.getNoWAtHistory(), op };
        } else if (op == ldt.getNoWaWAtHistory()){
            return new Operator[] { ldt.getNoWAtHistory(), op };
        }
        return new Operator[] {op};
    }

    protected boolean sequentImpliesPredicate(Term pred) {
//        System.out.println("sequentImpliesPredicate is called for: "+pred);

//        Sequent sequent = Sequent.EMPTY_SEQUENT;



        final Sequent sideSeq =
                filter(sequent).addFormula(new SequentFormula(pred), false, true).sequent();



        final boolean provable = sProof.isProvable(sideSeq, services);
            //SideProof.isProvable(sideSeq, 100000, 3000, true, services);


//        if(!provable)
//            System.out.println(pred+ " can't be proven in Seq: "+ sideSeq);
//        System.out.println(provable);
        return provable;
    }

    protected Sequent simplify(Sequent sequent) {
        System.out.println("sequent " + sequent);
        try {
            ApplyStrategyInfo info =
                    SideProof.isProvableHelper(sequent, 1000, true, false, services);
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
