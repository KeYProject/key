/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.taclettranslation.assumptions;

import java.util.Collection;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.taclettranslation.IllegalTacletException;
import de.uka.ilkd.key.taclettranslation.TacletFormula;

public class AssumptionFormula implements TacletFormula {

    final Taclet taclet;
    final Collection<Term> formula;
    final String status;
    final TacletConditions conditions;

    public TacletConditions getConditions() {
        return conditions;
    }

    public AssumptionFormula(Taclet taclet, Collection<Term> formula, String status) {
        this.taclet = taclet;
        this.formula = formula;
        this.status = status;
        this.conditions = null;
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
        return services.getTermBuilder().and(formula.toArray(new Term[0]));
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
