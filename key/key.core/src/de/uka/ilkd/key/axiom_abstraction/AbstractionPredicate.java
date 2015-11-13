// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.axiom_abstraction;

import java.util.function.Function;

import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Term;

/**
 * Interface for predicates used for predicate abstraction. An abstraction
 * predicate is a mapping from program variables or constants to formulae
 * instantiated for the respective variable.
 *
 * @author Dominic Scheurer
 */
public interface AbstractionPredicate extends Function<Term, Term>, Named {
}
