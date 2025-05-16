/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation;

import java.util.ArrayList;
import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.ContextMenuAdapter;
import de.uka.ilkd.key.gui.extension.api.ContextMenuKind;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.pp.PosInSequent;

import org.key_project.isabelletranslation.gui.controller.IsabelleTranslateAllAction;
import org.key_project.isabelletranslation.gui.controller.IsabelleTranslationAction;

import org.jspecify.annotations.NonNull;

/**
 * Extension class for Isabelle translation
 */
@KeYGuiExtension.Info(name = "Isabelle Translation", optional = true,
    experimental = false)
public class IsabelleTranslationExtension implements KeYGuiExtension, KeYGuiExtension.Settings,
        KeYGuiExtension.ContextMenu, KeYGuiExtension.Startup {
    @Override
    public SettingsProvider getSettings() {
        return new IsabelleSettingsProvider();
    }


    /**
     * The context menu adapter used by the extension.
     */
    private final ContextMenuAdapter adapter = new ContextMenuAdapter() {
        @Override
        public List<Action> getContextActions(
                KeYMediator mediator, ContextMenuKind kind, PosInSequent pos) {
            if (pos.getPosInOccurrence() != null || mediator.getSelectedGoal() == null) {
                return List.of();
            }
            List<Action> list = new ArrayList<>();
            list.add(new IsabelleTranslationAction(MainWindow.getInstance()));
            list.add(new IsabelleTranslateAllAction(MainWindow.getInstance()));
            return list;
        }
    };

    @Override
    public @NonNull List<Action> getContextActions(@NonNull KeYMediator mediator,
            @NonNull ContextMenuKind kind, @NonNull Object underlyingObject) {
        return adapter.getContextActions(mediator, kind, underlyingObject);
    }

    @Override
    public void init(MainWindow window, KeYMediator mediator) {
        IsabelleTranslationSettings.getInstance();
    }
}
