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

package de.uka.ilkd.key.gui.joinrule.predicateabstraction;

import java.util.Optional;

import javafx.beans.property.SimpleObjectProperty;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractPredicateAbstractionDomainElement;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * Model class for the manual choice of an abstract domain element by the user.
 *
 * @author Dominic Scheurer
 */
public class AbstractDomainElemChoice {
    /**
     * The program variable for which an abstract domain element has been
     * chosen.
     */
    private final SimpleObjectProperty<ProgramVariable> progVar;

    /**
     * The chosen abstract domain element. May be null if no choice has been
     * done for the program variable {@link #progVar}.
     */
    private final SimpleObjectProperty<Optional<AbstractPredicateAbstractionDomainElement>> abstrDomElem;

    public AbstractDomainElemChoice(ProgramVariable progVar,
            Optional<AbstractPredicateAbstractionDomainElement> abstrDomElem) {
        this.progVar = new SimpleObjectProperty<ProgramVariable>(progVar);
        this.abstrDomElem =
                new SimpleObjectProperty<Optional<AbstractPredicateAbstractionDomainElement>>(
                        abstrDomElem);
    }

    public SimpleObjectProperty<ProgramVariable> getProgVar() {
        return progVar;
    }

    public void setProgVar(ProgramVariable progVar) {
        this.progVar.set(progVar);
    }

    public SimpleObjectProperty<Optional<AbstractPredicateAbstractionDomainElement>> getAbstrDomElem() {
        return abstrDomElem;
    }

    public void setAbstrDomElem(
            Optional<AbstractPredicateAbstractionDomainElement> abstrDomElem) {
        this.abstrDomElem.set(abstrDomElem);
    }

    /**
     * @return True iff a choice has been made, that is the chosen element is
     *         not Empty.
     */
    public boolean isChoiceMade() {
        return abstrDomElem.get().isPresent();
    }
}
