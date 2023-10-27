/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.object_model.impl;

import de.uka.ilkd.key.symbolic_execution.object_model.IModelSettings;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicEquivalenceClass;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicLayout;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicObject;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicState;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * Default implementation of {@link ISymbolicLayout}.
 *
 * @author Martin Hentschel
 */
public class SymbolicLayout extends AbstractElement implements ISymbolicLayout {
    /**
     * The contained {@link ISymbolicEquivalenceClass}.
     */
    private final ImmutableList<ISymbolicEquivalenceClass> equivalenceClasses;

    /**
     * The {@link ISymbolicState}.
     */
    private ISymbolicState state;

    /**
     * The contained {@link ISymbolicObject}s.
     */
    private ImmutableList<ISymbolicObject> objects = ImmutableSLList.nil();

    /**
     * Constructor.
     *
     * @param equivalenceClasses The provided equivalence classes.
     * @param settings The {@link IModelSettings} to use.
     */
    public SymbolicLayout(IModelSettings settings,
            ImmutableList<ISymbolicEquivalenceClass> equivalenceClasses) {
        super(settings);
        assert equivalenceClasses != null;
        this.equivalenceClasses = equivalenceClasses;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public ISymbolicState getState() {
        return state;
    }

    /**
     * Sets the {@link ISymbolicState}.
     *
     * @param state The {@link ISymbolicState} to set.
     */
    public void setState(ISymbolicState state) {
        this.state = state;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public ImmutableList<ISymbolicObject> getObjects() {
        return objects;
    }

    /**
     * Adds a new {@link ISymbolicObject}.
     *
     * @param value The new {@link ISymbolicObject} to add.
     */
    public void addObject(ISymbolicObject object) {
        objects = objects.append(object);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public ImmutableList<ISymbolicEquivalenceClass> getEquivalenceClasses() {
        return equivalenceClasses;
    }
}
