/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof.io.intermediate;

import org.key_project.logic.PosInTerm;
import org.key_project.util.collection.Pair;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

@NullMarked
public class SMTAppIntermediate extends BuiltInAppIntermediate {
    private final @Nullable String solver;

    public SMTAppIntermediate(String ruleName, Pair<Integer, PosInTerm> pos,
            @Nullable String solver) {
        super(ruleName, pos, null, null, null, null);
        this.solver = solver;
    }

    public @Nullable String getSolver() {
        return solver;
    }
}
