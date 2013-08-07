package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.Public;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.op.TransformerProcedure;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.speclang.ClassInvWellDefinedness;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.ClassInvariantImpl;
import de.uka.ilkd.key.speclang.WellDefinednessCheck;
import de.uka.ilkd.key.util.Triple;

public class WellDefinednessPO extends AbstractPO implements ContractPO {

    protected static final TermBuilder TB = TermBuilder.DF;

    private WellDefinednessCheck check;

    public WellDefinednessPO(InitConfig initConfig, WellDefinednessCheck check) {
        super(initConfig, check.getName());
        this.check = check;
    }

    protected IObserverFunction getTarget() {
        return getContract().getTarget();
     }

    protected KeYJavaType getCalleeKeYJavaType() {
        return getContract().getKJT();
    }

    @Override
    public void readProblem() throws ProofInputException {
        //final IProgramMethod pm = getProgramMethod();
        // TODO: Build problem here
        Triple<Term, ImmutableList<Term>, Term> po = check.createPOTerm();
        ImmutableList<Term> c = ImmutableSLList.<Term>nil();
        for (Term t: po.second) {
            c = c.append(wd(t));
        }
        Term poTerms = TB.and(wd(po.first),
                              TB.imp(po.first,
                                      TB.and(TB.and(c),
                                              wd(po.third))));
        assignPOTerms(poTerms);

        // add axioms
        collectClassAxioms(getCalleeKeYJavaType());
    }

    @Override
    public boolean implies(ProofOblInput po) {
        if (!(po instanceof WellDefinednessPO)) {
            return false;
        }
        WellDefinednessPO wPO = (WellDefinednessPO) po;
        return specRepos.getWdChecks(wPO.check.getKJT(), wPO.check.getTarget())
                .subset(specRepos.getWdChecks(check.getKJT(), check.getTarget()));
    }

    @Override
    public WellDefinednessCheck getContract() {
        return check;
    }

    /**
     * Returns the base heap.
     * @return The {@link LocationVariable} which contains the base heap.
     */
    private LocationVariable getHeap() {
       return services.getTypeConverter().getHeapLDT().getHeap();
    }

    public Term wd(Term t) {
        return WellDefinednessCheck.wd(t, services);
    }

    TransformerProcedure getTransformer(String nameString, Sort argSort) {
        Name name = new Name(nameString);
        Named f = services.getNamespaces().functions().lookup(name);
        if (f != null && f instanceof TransformerProcedure) {
            return (TransformerProcedure) f;
        } else {
            return new TransformerProcedure(name, Sort.FORMULA, argSort);
        }
    }

    @Override
    protected void collectClassAxioms(KeYJavaType selfKJT) {
        ImmutableSet<ClassInvWellDefinedness> invs =
                specRepos.getWdClassInvariants(selfKJT, getTarget());
        if(invs.isEmpty()) {
            Term inv = TB.tt();
            final SchemaVariable selfSV =
                    getTarget().isStatic()
                    ? null
                    : SchemaVariableFactory.createTermSV(new Name("self"),
                                                         getCalleeKeYJavaType().getSort());
            ClassInvariant ci = new ClassInvariantImpl(name, check.getDisplayName(), selfKJT,
                                                       new Public(), inv, selfSV);
            invs = invs.add(new ClassInvWellDefinedness(ci, getTarget(), services));
        }

        for (ClassInvWellDefinedness inv : invs) {
            for (Taclet invTaclet : inv.getTaclets(services)) {
                assert invTaclet != null : "class invariant (wd) returned null taclet: "
                        + inv.getName();
                taclets = taclets.add(NoPosTacletApp.createNoPosTacletApp(invTaclet));
                initConfig.getProofEnv().registerRule(invTaclet,
                                                      AxiomJustification.INSTANCE);
            }
        }
    }

    @Deprecated
    public Term getMbyAtPre() {
        return null;
    }

}
