/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.object_model.impl;

import de.uka.ilkd.key.symbolic_execution.object_model.IModelSettings;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicState;

/**
 * Default implementation of {@link ISymbolicState}.
 *
 * @author Martin Hentschel
 */
public class SymbolicState extends AbstractSymbolicAssociationValueContainer
        implements ISymbolicState {
    /**
     * The name of this state.
     */
    private final String name;

    /**
     * Constructor.
     *
     * @param name The name of this state.
     * @param settings The {@link IModelSettings} to use.
     */
    public SymbolicState(String name, IModelSettings settings) {
        super(settings);
        this.name = name;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getName() {
        return name;
    }
}
