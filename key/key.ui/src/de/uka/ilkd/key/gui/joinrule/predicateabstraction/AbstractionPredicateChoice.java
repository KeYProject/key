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
import de.uka.ilkd.key.axiom_abstraction.AbstractDomainElement;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * Model class for the manual choice of an abstraction predicate by the user.
 *
 * @author Dominic Scheurer
 */
public class AbstractionPredicateChoice {
    /**
     * The program variable for which an abstraction predicate has been chosen.
     */
    private final SimpleObjectProperty<ProgramVariable> progVar;

    /**
     * The chosen abstraction predicate. May be null if no choice has been done
     * for the program variable {@link #progVar}.
     */
    private final SimpleObjectProperty<Optional<AbstractDomainElement>> abstrPred;

    public AbstractionPredicateChoice(ProgramVariable progVar,
            Optional<AbstractDomainElement> abstrPred) {
        this.progVar = new SimpleObjectProperty<ProgramVariable>(progVar);
        this.abstrPred =
                new SimpleObjectProperty<Optional<AbstractDomainElement>>(abstrPred);
    }

    public SimpleObjectProperty<ProgramVariable> getProgVar() {
        return progVar;
    }

    public void setProgVar(ProgramVariable progVar) {
        this.progVar.set(progVar);
    }

    public SimpleObjectProperty<Optional<AbstractDomainElement>> getAbstrPred() {
        return abstrPred;
    }

    public void setAbstrPred(Optional<AbstractDomainElement> abstrPred) {
        this.abstrPred.set(abstrPred);
    }
}
