/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.label;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.rule.label.TermLabelPolicy;
import de.uka.ilkd.key.rule.label.TermLabelRefactoring;
import de.uka.ilkd.key.rule.label.TermLabelUpdate;

import org.key_project.logic.Name;

/**
 * A {@link TermLabelState} is used to share information between participants which manage
 * {@link TermLabel}s during rule application. Participants are:
 * <ul>
 * <li>{@link TermLabelPolicy}</li>
 * <li>{@link TermLabelUpdate}</li>
 * <li>{@link TermLabelRefactoring}</li>
 * </ul>
 * <p>
 * Exactly one {@link TermLabelState} instance is created in each
 * {@code Rule.apply(...)}
 * implementation and passed to each performed {@link TermLabelManager} call during rule application
 * and thus passed to the participants.
 *
 * @author Martin Hentschel
 */
public class TermLabelState {
    /**
     * Stores for each {@link TermLabel} {@link Name} the state.
     */
    private final Map<Name, Map<Object, Object>> labelStateMap =
        new HashMap<>();

    /**
     * Constructor.
     */
    public TermLabelState() {
    }

    /**
     * Return the state {@link Map} in which arbitrary key values pairs can be stored for the given
     * {@link TermLabel} {@link Name}.
     *
     * @param termLabelName The {@link Name} of the {@link TermLabel}.
     * @return The {@link Map} used by the {@link TermLabel}s participants.
     */
    public Map<Object, Object> getLabelState(Name termLabelName) {
        synchronized (labelStateMap) {
            Map<Object, Object> result =
                labelStateMap.computeIfAbsent(termLabelName, k -> new HashMap<>());
            return result;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return "TermLabelState " + System.identityHashCode(this) + ": " + labelStateMap;
    }
}
