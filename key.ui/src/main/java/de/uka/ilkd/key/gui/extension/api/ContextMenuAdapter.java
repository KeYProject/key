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

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * @author Alexander Weigl
 * @version 1 (16.04.19)
 */
@NullMarked
public abstract class ContextMenuAdapter implements KeYGuiExtension.ContextMenu {
    @Override
    public <T> List<Action> getContextActions(KeYMediator mediator, ContextMenuKind<T> kind,
                                                    @Nullable T underlyingObject) {
        return Collections.emptyList();
    }
}
