/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import java.util.Map;

import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Sorted;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;

/**
 * A map from some type to the same type.
 *
 * @param <S> the key and value type.
 *
 * @author lanzinger
 */
public abstract class ReplacementMap<S extends Sorted & SVSubstitute>
        extends de.uka.ilkd.key.proof.ReplacementMap.NoIrrelevantLabelsReplacementMap<S, S> {

    /**
     * constructs a replacement map with the given term factory
     *
     * @param tf a term factory
     */
    public ReplacementMap(TermFactory tf) {
        super(tf);
    }

    /**
     * Adds a mapping for the self variable.
     *
     * @param oldSelf the old self variable.
     * @param newSelf the new self variable.
     * @param services services.
     */
    public void replaceSelf(final ProgramVariable oldSelf, final S newSelf, TermServices services) {
        if (newSelf != null) {
            if (!newSelf.sort().extendsTrans(oldSelf.sort())) {
                throw new IllegalArgumentException("new self variable has to be compatible");
            }
            put(convert(oldSelf, services), newSelf);
        }
    }

    /**
     * Adds a mapping for every flag.
     *
     * @param oldFlags old flags.
     * @param newFlags new flags.
     * @param services services.
     */
    public void replaceFlags(final Map<Label, ProgramVariable> oldFlags,
            final Map<Label, S> newFlags, TermServices services) {
        if (newFlags != null) {
            if (newFlags.size() != oldFlags.size()) {
                throw new IllegalArgumentException("flags have to have the same size");
            }
            for (Entry<Label, ProgramVariable> oldFlag : oldFlags.entrySet()) {
                replaceVariable(oldFlag.getValue(), newFlags.get(oldFlag.getKey()), services);
            }
        }
    }

    /**
     * Adds a mapping for a variable.
     *
     * @param oldVariable old variable.
     * @param newVariable new variable.
     * @param services services.
     */
    public void replaceVariable(final ProgramVariable oldVariable, final S newVariable,
            TermServices services) {
        if (newVariable != null) {
            if (!oldVariable.sort().equals(newVariable.sort())) {
                throw new IllegalArgumentException("variables have to have the same sort");
            }
            put(convert(oldVariable, services), newVariable);
        }
    }

    /**
     * Adds mappings for the remembrance heaps.
     *
     * @param oldRemembranceHeaps old remembrance heaps.
     * @param newRemembranceHeaps new remembrance heaps.
     * @param services services.
     */
    public void replaceRemembranceHeaps(
            final Map<LocationVariable, LocationVariable> oldRemembranceHeaps,
            final Map<LocationVariable, ? extends S> newRemembranceHeaps, final Services services) {
        if (newRemembranceHeaps != null) {
            for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                if (heap.name().equals(HeapLDT.SAVED_HEAP_NAME)) {
                    continue;
                }

                if (oldRemembranceHeaps.get(heap) != null) {
                    final LocationVariable oldRemembranceHeap = oldRemembranceHeaps.get(heap);
                    final S newRemembranceHeap = newRemembranceHeaps.get(heap);
                    assert oldRemembranceHeap.sort().equals(newRemembranceHeap.sort());
                    put(convert(oldRemembranceHeap, services), newRemembranceHeap);
                }
            }
        }
    }

    /**
     * Adds mappings for the remembrance variables.
     *
     * @param oldRemembranceLocalVariables old remembrance variables.
     * @param newRemembranceLocalVariables new remembrance variables.
     * @param services services
     */
    public void replaceRemembranceLocalVariables(
            final Map<LocationVariable, LocationVariable> oldRemembranceLocalVariables,
            final Map<LocationVariable, ? extends S> newRemembranceLocalVariables,
            final TermServices services) {
        if (newRemembranceLocalVariables != null) {
            for (final Entry<LocationVariable, LocationVariable> entry : oldRemembranceLocalVariables
                    .entrySet()) {
                LocationVariable localVariable = entry.getKey();
                if (newRemembranceLocalVariables.get(localVariable) != null) {
                    LocationVariable oldRemembranceLocalVariable = entry.getValue();
                    S newRemembranceLocalVariable = newRemembranceLocalVariables.get(localVariable);
                    assert oldRemembranceLocalVariable.sort()
                            .equals(newRemembranceLocalVariable.sort());
                    put(convert(oldRemembranceLocalVariable, services),
                        newRemembranceLocalVariable);
                }
            }
        }
    }

    /**
     * @param variable a variable.
     * @param services services.
     * @return a conversion of the specified variable to the type {@code S}.
     */
    protected abstract S convert(ProgramVariable variable, TermServices services);

}
