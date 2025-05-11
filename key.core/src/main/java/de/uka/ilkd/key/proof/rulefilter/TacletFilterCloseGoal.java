/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.rulefilter;

import de.uka.ilkd.key.rule.Taclet;

import org.jspecify.annotations.NonNull;

public class TacletFilterCloseGoal extends TacletFilter {

    public final static TacletFilterCloseGoal INSTANCE = new TacletFilterCloseGoal();

    private TacletFilterCloseGoal() {
    }

    protected boolean filter(@NonNull Taclet taclet) {
        return taclet.goalTemplates().size() == 0;
    }

}
