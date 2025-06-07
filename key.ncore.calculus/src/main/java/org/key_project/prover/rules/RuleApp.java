/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules;

import org.key_project.logic.Namespace;
import org.key_project.logic.op.Function;
import org.key_project.prover.sequent.PosInOccurrence;

import org.jspecify.annotations.NonNull;

/// Instances of this type accumulate the information for a specific rule application
/// like application position, instantiations and more.
public interface RuleApp {
    /// returns the rule of this rule application
    Rule rule();

    /// last minute check whether rule is applicable and throws an exception if not
    ///
    /// This is a debugging method, if an exception gets thrown there is nothing that can be done
    /// by the user
    ///
    ///
    /// @throws RuntimeException if rule is scheduled for application but not yet ready
    void checkApplicability();

    /// registers new Skolem functions to the provided namespace
    /// This method should be moved to the rule application logic, but remains for
    /// the moment here (checkApplicability() did also the registration before)
    ///
    /// @param fns the [Namespace] where to register the Skolem functions
    void registerSkolemConstants(Namespace<@NonNull Function> fns);

    /// returns true if all variables are instantiated
    ///
    /// @return true if all variables are instantiated
    boolean complete();

    /// @return user-friendly name for this rule-application
    default String displayName() {
        return rule().displayName();
    }

    /// the position where to apply the rule to which this application belongs
    ///
    /// @return the [PosInOccurrence] with the position information
    PosInOccurrence posInOccurrence();
}
