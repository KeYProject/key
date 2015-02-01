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

package de.uka.ilkd.key.logic.label;

import java.util.List;

/**
 * A factory for creating singleton {@link TermLabel}.
 *
 * <p>
 * The resulting factory does not accept arguments for the builder methods and
 * always returns a fixed term level value.
 *
 * @param <T>
 *            the type of the wrapped term label can be narrowed.
 */
public final class SingletonLabelFactory<T extends TermLabel> implements TermLabelFactory<T> {

    /**
     * The label around which the factory is built.
     */
    private final T singletonLabel;

    /**
     * Instantiates a new singleton label factory for a label.
     *
     * @param singletonLabel
     *            the label to be wrapped, not <code>null</code>.
     */
    public SingletonLabelFactory(T singletonLabel) {
        assert singletonLabel != null;
        this.singletonLabel = singletonLabel;
    }

    /**
     * {@inheritDoc}
     *
     * <p>This implementation does not accept arguments and returns the stored label
     */
    @Override
    public T parseInstance(List<String> arguments) throws TermLabelException {
        if (arguments.isEmpty()) {
            return singletonLabel;
        } else {
            throw new TermLabelException("Label " + singletonLabel.name() + " does not expect arguments.");
        }
    }
}