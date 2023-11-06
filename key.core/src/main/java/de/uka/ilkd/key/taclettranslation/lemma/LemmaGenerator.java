/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.taclettranslation.lemma;

import java.util.Collection;
import java.util.LinkedList;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.taclettranslation.TacletFormula;
import de.uka.ilkd.key.taclettranslation.TacletTranslator;

/**
 * A Lemma Generator translates a taclet to its corresponding first order logic formula thats
 * validity implies the validity of the taclet.
 */
public interface LemmaGenerator extends TacletTranslator {
    TacletFormula translate(Taclet taclet, TermServices services);
}


class LemmaFormula implements TacletFormula {
    private final Taclet taclet;
    private final LinkedList<Term> formula = new LinkedList<>();

    public LemmaFormula(Taclet taclet, Term formula) {
        this.taclet = taclet;
        this.formula.add(formula);
    }

    @Override
    public Taclet getTaclet() {
        return taclet;
    }

    @Override
    public Term getFormula(TermServices services) {
        return formula.getFirst();
    }

    @Override
    public String getStatus() {
        return "";
    }

    @Override
    public Collection<Term> getInstantiations() {
        return formula;
    }

}
