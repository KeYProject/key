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
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

public class AssumptionFormula implements TacletFormula {

    final Taclet taclet;
    final Collection<Term> formula;
    final String status;
    final @Nullable TacletConditions conditions;

    public @Nullable TacletConditions getConditions() {
        return conditions;
    }

    public AssumptionFormula(Taclet taclet, Collection<Term> formula, String status) {
        this.taclet = taclet;
        this.formula = formula;
        this.status = status;
        this.conditions = null;
    }



    public AssumptionFormula(@NonNull Taclet taclet, Collection<Term> formula, String status,
                             @Nullable TacletConditions conditions) throws IllegalTacletException {
        super();
        this.taclet = taclet;
        this.formula = formula;
        this.status = status;
        this.conditions = conditions == null ? new TacletConditions(taclet) : conditions;

    }

    public @NonNull Term getFormula(@NonNull TermServices services) {
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
