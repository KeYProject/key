/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.extension.api;

import java.util.Collections;
import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.Rule;

/**
 * @author Alexander Weigl
 * @version 1 (16.04.19)
 */
public abstract class ContextMenuAdapter implements KeYGuiExtension.ContextMenu {
    @Override
    public final List<Action> getContextActions(KeYMediator mediator, ContextMenuKind kind,
            Object underlyingObject) {
        switch ((DefaultContextMenuKind) kind) {
        case PROOF_LIST:
            return getContextActions(mediator, kind, (Proof) underlyingObject);
        case PROOF_TREE:
            return getContextActions(mediator, kind, (Node) underlyingObject);
        case TACLET_INFO:
            return getContextActions(mediator, kind, (Rule) underlyingObject);
        case SEQUENT_VIEW:
            return getContextActions(mediator, kind, (PosInSequent) underlyingObject);
        default:
            throw new IllegalArgumentException("unexpected kind");
        }
    }

    public List<Action> getContextActions(KeYMediator mediator, ContextMenuKind kind,
            Proof underlyingObject) {
        return Collections.emptyList();
    }

    public List<Action> getContextActions(KeYMediator mediator, ContextMenuKind kind,
            Node underlyingObject) {
        return Collections.emptyList();
    }

    public List<Action> getContextActions(KeYMediator mediator, ContextMenuKind kind,
            PosInSequent underlyingObject) {
        return Collections.emptyList();
    }

    public List<Action> getContextActions(KeYMediator mediator, ContextMenuKind kind,
            Rule underlyingObject) {
        return Collections.emptyList();
    }
}
