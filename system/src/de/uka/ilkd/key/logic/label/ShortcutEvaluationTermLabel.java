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

package de.uka.ilkd.key.logic.label;

import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.Name;

/**
 * Label attached to a term with the logical operator '||' or '&&' to distinguish
 * from '|' or '&' respectively.
 *
 * @author Michael Kirsten
 */
public class ShortcutEvaluationTermLabel implements ITermLabel {
    /**
     * The unique name of this label.
     */
    public static final Name NAME = new Name("SC");

    /**
     * The only instance of this class.
     */
    public static ShortcutEvaluationTermLabel INSTANCE = new ShortcutEvaluationTermLabel();

    /**
     * Constructor to forbid multiple instances.
     */
    private ShortcutEvaluationTermLabel() {
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public Object getChild(int i) {
        return null;
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    /**
     * {@inheritDoc}
     */
    public String toString() {
        return NAME.toString();
    }
}