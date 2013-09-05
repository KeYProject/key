package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;

public abstract class StatementWellDefinedness extends WellDefinednessCheck {

    private final static String PROOFS = "wdProofs";

    StatementWellDefinedness(String name, int id, IObserverFunction target,
            OriginalVariables origVars, Type type, Services services) {
        super(ContractFactory.generateContractTypeName(name, target.getContainerType(),
                                                       target, target.getContainerType()),
              id, target, origVars, type, services);
    }

    StatementWellDefinedness(String name, int id, Type type, IObserverFunction target,
                             LocationVariable heap, OriginalVariables origVars,
                             Condition requires, Term assignable, Term accessible,
                             Condition ensures, Term mby, Term rep) {
        super(name, id, type, target, heap, origVars, requires,
              assignable, accessible, ensures, mby, rep);
    }

    public abstract Term generatePO(ProgramVariable self, ProgramVariable exception,
                                    ProgramVariable result, LocationVariable heap,
                                    ProgramVariable heapAtPre, Term anonHeap,
                                    ImmutableSet<ProgramVariable> ps,
                                    Term leadingUpdate, Services services);

    public abstract SpecificationElement getStatement();

    final static ImmutableList<ProgramVariable> convertParams(ImmutableSet<ProgramVariable> set) {
        ImmutableList<ProgramVariable> list = ImmutableSLList.<ProgramVariable>nil();
        for (ProgramVariable pv: set) {
            list = list.append(pv);
        }
        return list;
    }

    @Override
    final TermAndFunc generateMbyAtPreDef(ParsableVariable self,
                                          ImmutableList<ParsableVariable> params,
                                          Services services) {
        return new TermAndFunc(TB.tt(), null);
    }

    @Override
    final ImmutableList<Term> getRest() {
        return super.getRest();
    }

    public static boolean checkOn() {
        final String setting =
                ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().getDefaultChoices().get(PROOFS);
        if (setting.equals(PROOFS + ":on")) {
            return true;
        } else if (setting.equals(PROOFS + ":off")) {
            return false;
        } else {
            throw new RuntimeException("The setting for the wdProofs-option is not valid: "
                    + setting);
        }
    }

    @Override
    public final String getBehaviour() {
        return "";
    }

    @Override
    public final Term getGlobalDefs() {
        throw new UnsupportedOperationException("Not applicable for well-definedness of statements.");
    }

    @Override
    public final boolean isModel() {
        return false;
    }
}