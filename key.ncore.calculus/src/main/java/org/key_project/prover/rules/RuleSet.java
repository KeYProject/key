/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules;

import org.key_project.logic.Name;
import org.key_project.logic.Named;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/// This class represents a heuristic. Taclets can belong to different rulesets and are executed
/// automatic if these are selected. A ruleset is just a name.
///
/// Rulesets had been originally called heuristics.
///
public record RuleSet(Name name) implements Named {
    /// creates a ruleset
    ///
    /// @param name the [Name] of the ruleset
    public RuleSet {
    }

    /// retrieves name of the ruleset
    ///
    /// @return the [Name] of the ruleset
    @Override
    public @NonNull Name name() { return name; }

    public int hashCode() { return 3 * name().hashCode(); }

    /// Checks whether the given object is equal to this instance.
    /// Two rulesets are equal if and only if their names are equal.
    ///
    /// @param other the Object with which this instance is compared
    /// @return true it the `other` is a ruleset of the same name
    /// as this ruleset
    public boolean equals(@Nullable Object other) {
        if (other instanceof RuleSet(Name otherName)) {
            return this.name().equals(otherName);
        }
        return false;
    }

    /// toString
    public String toString() { return name.toString(); }
}
