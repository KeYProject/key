/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.extension.api;

import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.Rule;

/**
 * @author Alexander Weigl
 * @version 1 (07.04.19)
 */
public enum DefaultContextMenuKind implements ContextMenuKind {
    PROOF_LIST(Proof.class), PROOF_TREE(Node.class), TACLET_INFO(Rule.class),
    SEQUENT_VIEW(PosInSequent.class);

    private final Class<?> clazz;

    DefaultContextMenuKind(Class<?> clazz) {
        this.clazz = clazz;
    }

    public Class<?> getType() {
        return clazz;
    }
}
