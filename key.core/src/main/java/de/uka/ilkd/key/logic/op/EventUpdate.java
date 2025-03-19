/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
// Technical University Darmstadt, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic.op;


import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;


/**
 * Class of operators for elementary updates, i.e., updates of the form
 * "x := t". There is one such operator for every left hand side "x".
 * Each of these operator is unary, accepting a single argument "t".
 */
public final class EventUpdate extends AbstractSortedOperator {

    public final static EventUpdate SINGLETON = new EventUpdate();

    private EventUpdate() {
        super(new Name("\\event"),
            new Sort[] { Sort.ANY, Sort.ANY, Sort.ANY },
            Sort.UPDATE,
            false);
    }

}
