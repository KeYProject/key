/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.testgen;

import java.awt.event.KeyEvent;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.keyshortcuts.KeyStrokeManager;
import de.uka.ilkd.key.gui.keyshortcuts.KeyStrokeSettings;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.testgen.macros.TestGenMacro;

import org.jspecify.annotations.NonNull;

/**
 * @author Alexander Weigl
 * @version 1 (9/16/20)
 */
@KeYGuiExtension.Info(name = "Test case generation", description = "key.testgen",
    experimental = false)
public class TestgenExtension
        implements KeYGuiExtension, KeYGuiExtension.KeyboardShortcuts, KeYGuiExtension.MainMenu,
        KeYGuiExtension.Startup, KeYGuiExtension.Toolbar, KeYGuiExtension.Settings {

    private TestGenerationAction actionTestGeneration;
    private CounterExampleAction actionCounterExample;

    private void init(MainWindow window) {
        this.actionCounterExample = new CounterExampleAction(window);
        this.actionTestGeneration = new TestGenerationAction(window);
    }

    @Override
    public @NonNull List<Action> getMainMenuActions(@NonNull MainWindow mainWindow) {
        init(mainWindow);
        return Arrays.asList(actionCounterExample, actionTestGeneration);
    }

    @Override
    public void init(MainWindow window, KeYMediator mediator) {
        init(window);
        KeyStrokeSettings.defineDefault(TestGenMacro.class, KeyStroke.getKeyStroke(KeyEvent.VK_T,
            KeyStrokeManager.MULTI_KEY_MASK));
    }

    @Override
    public @NonNull JToolBar getToolbar(MainWindow mainWindow) {
        JToolBar tb = new JToolBar("test generation");
        tb.add(actionCounterExample);
        tb.add(actionTestGeneration);
        return tb;
    }

    @Override
    public Collection<Action> getShortcuts(KeYMediator mediator, String componentId,
            JComponent component) {
        return Collections.emptyList();
    }

    @Override
    public SettingsProvider getSettings() {
        return new TestgenOptionsPanel();
    }
}
