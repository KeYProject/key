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

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.TermLabel;
import de.uka.ilkd.key.rule.label.TermLabelInstantiator;

/**
 * The Class SimpleTermLabel can be used to define labels without parameters and
 * with a fixed associated {@link TermLabelInstantiator}.
 * 
 * <p>
 * You can use a {@link SingletonLabelFactory} to create a factory for an
 * instance of this class.
 * 
 * @see TermLabelInstantiator
 * @see SingletonLabelFactory
 * 
 * @author mattias ulbrich
 */
final class SimpleTermLabel implements TermLabel {

    /**
     * The unique name of this label.
     * This is the basename and does not include the parameters 
     */
    private final Name name;

    /**
     * The instantiator associated with this object.
     * May be <code>null</code> if non assigned
     */
    private final TermLabelInstantiator instantiator;

    /**
     * Instantiates a new simple term label.
     * 
     * @param name
     *            the name, not <code>null</code>
     * @param instantiator
     *            the fixed associated instantiator, may be <code>null</code>.
     */
    public SimpleTermLabel(Name name, TermLabelInstantiator instantiator) {
        assert name != null;

        this.name = name;
        this.instantiator = instantiator;
    }

    @Override 
    public Name name() {
        return name;
    }

    @Override 
    public TermLabelInstantiator getInstantiator() {
        return instantiator;
    }


    /**
     * {@inheritDoc}
     * 
     * <p>
     * Simple term labels have no parameters. This always throws an
     * {@link IndexOutOfBoundsException}.
     */
    @Override 
    public Object getChild(int i) {
        throw new IndexOutOfBoundsException();
    }

    /**
     * {@inheritDoc}
     * 
     * <p>
     * Simple term labels have no parameters. This always returns 0.
     */
    @Override 
    public int getChildCount() {
        return 0;
    }

    @Override 
    public String toString() {
        return name.toString();
    }

    /**
     * {@inheritDoc}
     * 
     * <p>This object is equal to another {@link SimpleTermLabel} iff they
     * bear the same name.
     */
    @Override 
    public boolean equals(Object obj) {
        if (obj instanceof SimpleTermLabel) {
            SimpleTermLabel other = (SimpleTermLabel) obj;
            return name.equals(other.name);
        }
        return false;
    }

    @Override 
    public int hashCode() {
        return name.hashCode();
    }

}
