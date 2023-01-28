package de.uka.ilkd.key.taclettranslation.assumptions;

import java.util.Collection;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.taclettranslation.IllegalTacletException;
import de.uka.ilkd.key.taclettranslation.TacletFormula;

public class AssumptionFormula implements TacletFormula {

    Taclet taclet;
    Collection<Term> formula;
    String status;
    TacletConditions conditions;

    public TacletConditions getConditions() {
        return conditions;
    }

    public AssumptionFormula(Taclet taclet, Collection<Term> formula, String status) {
        this.taclet = taclet;
        this.formula = formula;
        this.status = status;
    }



    public AssumptionFormula(Taclet taclet, Collection<Term> formula, String status,
            TacletConditions conditions) throws IllegalTacletException {
        super();
        this.taclet = taclet;
        this.formula = formula;
        this.status = status;
        this.conditions = conditions == null ? new TacletConditions(taclet) : conditions;

    }

    public Term getFormula(TermServices services) {
        return services.getTermBuilder().and(formula.toArray(new Term[formula.size()]));
        // return formula;
    }

    public Taclet getTaclet() {
        return taclet;
    }

    public String getStatus() {
        return status;
    }

    public Collection<Term> getInstantiations() {

        return formula;
    }

}
