/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.engine;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.proof.ProofObject;

import org.jspecify.annotations.NonNull;

/// Interface to be implemented by builders returning a goal chooser.
public interface GoalChooserFactory<P extends ProofObject<G>, G extends ProofGoal<@NonNull G>> {

    /// returns a new goal chooser
    GoalChooser<P, G> create();

    /// returns a clone of this goal chooser
    GoalChooserFactory<P, G> copy();

    /// returns the name of the goal chooser
    String name();
}
