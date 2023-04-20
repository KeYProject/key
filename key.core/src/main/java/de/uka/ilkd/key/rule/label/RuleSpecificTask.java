package de.uka.ilkd.key.rule.label;

import de.uka.ilkd.key.logic.Name;

import org.key_project.util.collection.ImmutableList;

/**
 * Instances of this class provides functionality only if a supported rule is active.
 *
 * @author Martin Hentschel
 * @see ChildTermLabelPolicy
 * @see TermLabelUpdate
 * @see TermLabelRefactoring
 */
public interface RuleSpecificTask {
    /**
     * Returns the supported rule {@link Name}s or {@code null} or an empty list if all rules are
     * supported.
     *
     * @return The list of supported rule {@link Name}s or {@code null}/empty list if all rules are
     *         supported.
     */
    ImmutableList<Name> getSupportedRuleNames();
}
