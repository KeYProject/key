/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.label;

import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.function.Predicate;

import org.key_project.util.collection.ImmutableArray;

/**
 * <p>
 * Realises a collection for term labels keeping track whether its content has been modified
 * since its initialization. It provides faster lookup than the previously used immutable sets.
 * </p>
 * <p>
 * Note that it does not keep track of changes, so adding a label and removing it afterwards will
 * mark the collection
 * as modified
 * </p>
 */
public class LabelCollection {

    private final LinkedHashSet<TermLabel> labels = new LinkedHashSet<>();
    private boolean modified;

    /**
     * initializes the label collection with the given labels
     * <p>
     * any change to its content afterwards will cause method {@link #isModified()} to return true
     * </p>
     *
     * @param p_labels the list of {@link TermLabel}s for this collections
     */
    public LabelCollection(ImmutableArray<TermLabel> p_labels) {
        for (int i = 0, sz = p_labels.size(); i < sz; i++) {
            labels.add(p_labels.get(i));
        }
        modified = false;
    }

    /**
     * adds the given label to the collection and marks it as modified
     *
     * @param label the {@link TermLabel} to be added
     */
    public void add(TermLabel label) {
        modified |= labels.add(label);
    }

    /**
     * removes the given label from the collection and marks it as modified
     *
     * @param label the {@link TermLabel} to be added
     */
    public void remove(TermLabel label) {
        modified |= labels.remove(label);
    }

    /**
     * returns true if the collection has been modified after its initial creation
     */
    public boolean isModified() {
        return modified;
    }

    /**
     * checks wether a label is contained in the collection
     *
     * @param label the {@link TermLabel} to be checked
     * @return true iff the label is contained
     */
    public boolean contains(TermLabel label) {
        return labels.contains(label);
    }

    /**
     * returns the underlying collection of labels
     * (careful, you get full access to the underlying set)
     */
    public Collection<TermLabel> getLabels() {
        return labels;
    }

    /**
     * removes labels that satisfy the predicate and marks the set as modified
     * if a label has been removed
     *
     * @param p the {@link Predicate} used for testing
     */
    public void removeIf(Predicate<TermLabel> p) {
        modified |= labels.removeIf(p);
    }

    /**
     * returns the first element in the collection of the given kind
     * <br>
     * The method uses instanceof as check, so if subtypes are possible, any of those will be
     * returned.
     *
     * @param termLabelClass the Class specifying the kind of termlabel to be retrieved
     * @return the {@link TermLabel} of the specified type or <code>null</code>, if no such label is
     *         present
     * @param <S> the type of the label to be retrieved
     */
    public <S> S getFirst(Class<S> termLabelClass) {
        for (var label : labels) {
            if (termLabelClass.isInstance(label)) {
                return (S) label;
            }
        }
        return null;
    }

    // only for tests

    /**
     * DO NOT USE; ONLUY for TESTS
     */
    public void replaceWith(Collection<TermLabel> newLabels, boolean p_changed) {
        labels.clear();
        labels.addAll(newLabels);
        modified = p_changed;
    }
}
