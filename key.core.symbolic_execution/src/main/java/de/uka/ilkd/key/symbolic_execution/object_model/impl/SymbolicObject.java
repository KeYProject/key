/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.object_model.impl;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.symbolic_execution.object_model.IModelSettings;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicObject;

/**
 * Default implementation of {@link ISymbolicObject}.
 *
 * @author Martin Hentschel
 */
public class SymbolicObject extends AbstractSymbolicAssociationValueContainer
        implements ISymbolicObject {
    /**
     * The {@link Services} to use.
     */
    private final Services services;

    /**
     * The name.
     */
    private final Term name;

    /**
     * Constructor.
     *
     * @param services The {@link Services} to use.
     * @param name The name.
     * @param settings The {@link IModelSettings} to use.
     */
    public SymbolicObject(Services services, Term name, IModelSettings settings) {
        super(settings);
        this.services = services;
        this.name = name;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Term getName() {
        return name;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getNameString() {
        return formatTerm(name, services);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Sort getType() {
        return name != null ? name.sort() : null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getTypeString() {
        Sort sort = getType();
        return sort != null ? sort.toString() : null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return "Object " + getNameString();
    }
}
