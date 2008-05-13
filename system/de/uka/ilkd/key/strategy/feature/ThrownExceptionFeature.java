package de.uka.ilkd.key.strategy.feature;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.Throw;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;

public class ThrownExceptionFeature extends BinaryFeature {

    public static Feature create(String[] blockedExceptions, Services services) {
        return new ThrownExceptionFeature(blockedExceptions, services);
    }

    private final Sort[] filteredExceptions;

    /**
     * creates a feature filtering first active throw statements where the
     * thrown exception is of one of the given types (or their subtypes)
     * 
     * @param p_filteredExceptions
     *            the String array with the types of the thrown exceptions
     * @param services
     *            the Services
     */
    private ThrownExceptionFeature(String[] p_filteredExceptions,
            Services services) {
        final List<Sort> filtered = new ArrayList<Sort>();

        final JavaInfo javaInfo = services.getJavaInfo();

        for (int i = 0; i < p_filteredExceptions.length; i++) {
            final KeYJavaType nullPointer = javaInfo
                    .getKeYJavaType(p_filteredExceptions[i]);
            if (nullPointer != null) {
                filtered.add(nullPointer.getSort());
            }
        }
        filteredExceptions = filtered.toArray(new Sort[filtered.size()]);
    }

    private boolean blockedExceptions(Sort excType) {
        for (int i = 0; i < filteredExceptions.length; i++) {
            if (excType.extendsTrans(filteredExceptions[i])) {
                return true;
            }
        }
        return false;
    }

    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
        return app instanceof TacletApp ? filter(pos.subTerm(), goal.proof()
                .getServices(), ((TacletApp) app).instantiations()
                .getExecutionContext()) : false;
    }

    protected boolean filter(Term term, Services services, ExecutionContext ec) {
        if (term.op() instanceof Modality) {
            final ProgramElement fstActive = getFirstExecutableStatement(term);
            return fstActive instanceof Throw
                    && blockedExceptions(((Throw) fstActive).getExpressionAt(0)
                            .getKeYJavaType(services, ec).getSort());
        }
        return false;
    }

    /**
     * returns the first executable statement (often identical with the first
     * active statement)
     * 
     * @param term
     *            the Term with the program at top level
     * @return the first executable statement
     */
    private ProgramElement getFirstExecutableStatement(Term term) {
        if (term.javaBlock().isEmpty())
            return null;

        final ProgramElement jb = term.javaBlock().program();
        final ProgramElement fstActive;

        if (jb instanceof ProgramPrefix) {
            final ProgramPrefix pp = ((ProgramPrefix) jb)
                    .getPrefixElementAt(((ProgramPrefix) jb).getPrefixLength() - 1);
            fstActive = (Statement) PosInProgram.getProgramAt(pp
                    .getFirstActiveChildPos(), pp);
        } else {
            fstActive = jb;
        }
        return fstActive;
    }

}
