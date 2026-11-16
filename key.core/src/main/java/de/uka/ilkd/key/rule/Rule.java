/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule;


import org.key_project.logic.HasMetaSpaceKey;

import org.jspecify.annotations.NullMarked;



/**
 * This interface has to be implemented by all classes that want to act as a rule in the calculus.
 */
@NullMarked
public interface Rule extends org.key_project.prover.rules.Rule, HasMetaSpaceKey {
    @Override
    default String getMetaKey() {
        return "rule/" + this.name();
    }
}
