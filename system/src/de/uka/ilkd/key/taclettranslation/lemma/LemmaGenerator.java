// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.taclettranslation.lemma;

import java.util.Collection;
import java.util.LinkedList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.taclettranslation.TacletFormula;
import de.uka.ilkd.key.taclettranslation.TacletTranslator;

/**
 * A Lemma Generator translates a taclet to its corresponding 
 * first order logic formula thats validity implies the validity
 * of the taclet.
 */
public interface LemmaGenerator extends TacletTranslator {
         public TacletFormula translate(Taclet taclet, Services services);
}

class LemmaFormula implements TacletFormula {
        private Taclet taclet;
        private LinkedList<Term> formula = new LinkedList<Term>();

        public LemmaFormula(Taclet taclet, Term formula) {
                this.taclet = taclet;
                this.formula.add(formula);
        }

        @Override
        public Taclet getTaclet() {
                return taclet;
        }

        @Override
        public Term getFormula() {
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