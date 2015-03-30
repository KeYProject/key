// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.pp;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.label.TermLabel;

/**
 * This abstract class is used by SequentViewLogicPrinter to determine the set
 * of printed TermLabels.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public abstract class VisibleTermLabels {

    public boolean contains(TermLabel label) {
        return contains(label.name());
    }

    public abstract boolean contains(Name name);

}