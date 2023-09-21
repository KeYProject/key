/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.mergerule.predicateabstraction;

import java.util.Optional;

import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractPredicateAbstractionDomainElement;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * Model class for the manual choice of an abstract domain element by the user.
 *
 * @author Dominic Steinhoefel
 */
public class AbstractDomainElemChoice {
    /**
     * The program variable for which an abstract domain element has been chosen.
     */
    private ProgramVariable progVar;

    /**
     * The chosen abstract domain element. May be null if no choice has been done for the program
     * variable {@link #progVar}.
     */
    private Optional<AbstractPredicateAbstractionDomainElement> abstrDomElem;

    public AbstractDomainElemChoice(ProgramVariable progVar,
            Optional<AbstractPredicateAbstractionDomainElement> abstrDomElem) {
        this.progVar = progVar;
        this.abstrDomElem = abstrDomElem;
    }

    public ProgramVariable getProgVar() {
        return progVar;
    }

    public void setProgVar(ProgramVariable progVar) {
        this.progVar = progVar;
    }

    public Optional<AbstractPredicateAbstractionDomainElement> getAbstrDomElem() {
        return abstrDomElem;
    }

    public void setAbstrDomElem(AbstractPredicateAbstractionDomainElement abstrDomElem) {
        this.abstrDomElem = Optional.of(abstrDomElem);
    }

    public void setAbstrDomElem(Optional<AbstractPredicateAbstractionDomainElement> abstrDomElem) {
        this.abstrDomElem = abstrDomElem;
    }

    /**
     * @return True iff a choice has been made, that is the chosen element is not Empty.
     */
    public boolean isChoiceMade() {
        return abstrDomElem.isPresent();
    }

    public String choiceToString() {
        return abstrDomElem.isPresent() ? abstrDomElem.toString() : "(no choice)";
    }
}
