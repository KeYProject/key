/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover;

/**
 * interface to be implemented by builders returning a goal chooser
 */
public interface GoalChooserBuilder {

    /** returns a new goal chooser */
    GoalChooser create();

    /** returns a clone of this goal chooser */
    GoalChooserBuilder copy();

    /** returns the name of the goal chooser */
    String name();
}
