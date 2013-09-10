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
 * Label attached to a term which is specified implicitly (by the JML specification).
 *
 * @author Michael Kirsten
 */
public class ImplicitSpecTermLabel implements ITermLabel {
    /**
     * The unique name of this label.
     */
    public static final Name NAME = new Name("impl");

    /**
     * The only instance of this class.
     */
    public static ImplicitSpecTermLabel INSTANCE = new ImplicitSpecTermLabel();

    /**
     * Constructor to forbid multiple instances.
     */
    private ImplicitSpecTermLabel() {
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