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
