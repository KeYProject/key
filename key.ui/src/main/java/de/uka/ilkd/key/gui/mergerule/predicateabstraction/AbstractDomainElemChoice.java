// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2016 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

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
     * The program variable for which an abstract domain element has been
     * chosen.
     */
    private ProgramVariable progVar;

    /**
     * The chosen abstract domain element. May be null if no choice has been
     * done for the program variable {@link #progVar}.
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

    public void setAbstrDomElem(
            AbstractPredicateAbstractionDomainElement abstrDomElem) {
        this.abstrDomElem = Optional.of(abstrDomElem);
    }

    public void setAbstrDomElem(
            Optional<AbstractPredicateAbstractionDomainElement> abstrDomElem) {
        this.abstrDomElem = abstrDomElem;
    }

    /**
     * @return True iff a choice has been made, that is the chosen element is
     *         not Empty.
     */
    public boolean isChoiceMade() {
        return abstrDomElem.isPresent();
    }
    
    public String choiceToString() {
        return abstrDomElem.isPresent() ? abstrDomElem.toString() : "(no choice)";
    }
}
