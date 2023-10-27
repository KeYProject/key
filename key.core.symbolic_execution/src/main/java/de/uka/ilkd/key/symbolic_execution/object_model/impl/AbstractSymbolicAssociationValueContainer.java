/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.object_model.impl;

import java.util.Objects;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.symbolic_execution.object_model.IModelSettings;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicAssociation;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicAssociationValueContainer;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicValue;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.java.CollectionUtil;

/**
 * Default implementation of {@link ISymbolicAssociationValueContainer}.
 *
 * @author Martin Hentschel
 */
public abstract class AbstractSymbolicAssociationValueContainer extends AbstractElement
        implements ISymbolicAssociationValueContainer {
    /**
     * The contained {@link ISymbolicAssociation}s.
     */
    private ImmutableList<ISymbolicAssociation> associations = ImmutableSLList.nil();

    /**
     * The contained {@link ISymbolicValue}s.
     */
    private ImmutableList<ISymbolicValue> values = ImmutableSLList.nil();

    /**
     * Constructor.
     *
     * @param settings The {@link IModelSettings} to use.
     */
    public AbstractSymbolicAssociationValueContainer(IModelSettings settings) {
        super(settings);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public ImmutableList<ISymbolicAssociation> getAssociations() {
        return associations;
    }

    /**
     * Adds a new {@link ISymbolicAssociation}.
     *
     * @param value The new {@link ISymbolicAssociation} to add.
     */
    public void addAssociation(ISymbolicAssociation association) {
        associations = associations.append(association);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public ISymbolicAssociation getAssociation(final IProgramVariable programVariable,
            final boolean isArrayIndex, final Term arrayIndex, final Term condition) {
        return CollectionUtil.search(associations,
            element -> element.getProgramVariable() == programVariable
                    && element.isArrayIndex() == isArrayIndex
                    && Objects.equals(element.getArrayIndex(), arrayIndex)
                    && Objects.equals(element.getCondition(), condition));
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public ImmutableList<ISymbolicValue> getValues() {
        return values;
    }

    /**
     * Adds a new {@link ISymbolicValue}.
     *
     * @param value The new {@link ISymbolicValue} to add.
     */
    public void addValue(ISymbolicValue value) {
        values = values.append(value);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public ISymbolicValue getValue(final IProgramVariable programVariable,
            final boolean isArrayIndex, final Term arrayIndex, final Term condition) {
        return CollectionUtil.search(values,
            element -> element.getProgramVariable() == programVariable
                    && element.isArrayIndex() == isArrayIndex
                    && Objects.equals(element.getArrayIndex(), arrayIndex)
                    && Objects.equals(element.getCondition(), condition));
    }
}
