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
 * Label attached to skolem constants introduced by the rule pullOutSelect.
 */
public class SelectSkolemConstantTermLabel implements ITermLabel {

    /**
     * The unique name of this label.
     */
    public static final Name NAME = new Name("selectSK");

    /**
     * The only instance of this class.
     */
    public static SelectSkolemConstantTermLabel INSTANCE = new SelectSkolemConstantTermLabel();


    /**
     * Constructor to forbid multiple instances.
     */
    private SelectSkolemConstantTermLabel() {
    }


    /**
     * {@inheritDoc}
     */
    public boolean equals(Object o) {
        return this == o;
    }


    /**
     * {@inheritDoc}
     */
    public String toString() {
        return NAME.toString();
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public ITermLabel getChild(int i) {
        // this label is not parameterized
        return null;
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public int getChildCount() {
        // this label is not parameterized
        return 0;
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public Name name() {
        return NAME;
    }
}