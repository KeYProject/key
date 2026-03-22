/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.extension.api;

import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

/**
 * @author Alexander Weigl
 * @version 1 (07.04.19)
 */
public interface ContextMenuKind<T> {
    ContextMenuKind<Proof> PROOF_LIST = new ContextMenuKind<>() {};
    ContextMenuKind<Node> PROOF_TREE = new ContextMenuKind<>() {};
    ContextMenuKind<Object> INFO_TREE = new ContextMenuKind<>() {};
    ContextMenuKind<PosInSequent> SEQUENT_VIEW = new ContextMenuKind<>() {};
}
