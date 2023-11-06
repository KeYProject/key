package org.key_project.slicing;

import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.settings.SettingsProvider;

/**
 * Proof slicing extension.
 * For more details see <a href="https://key-project.org/docs/user/ProofSlicing/">the user
 * guide</a>.
 *
 * @author Arne Keller
 */
@KeYGuiExtension.Info(name = "Slicing",
    description = "Author: Arne Keller <arne.keller@posteo.de>",
    experimental = false,
    optional = true,
    priority = 9001)
public class RegroupExtension implements KeYGuiExtension,
        KeYGuiExtension.Settings,
        KeYGuiExtension.Toolbar {


    @Override
    public JToolBar getToolbar(MainWindow mainWindow) {
        return new JToolBar();
    }

    @Override
    public SettingsProvider getSettings() {
        return new ProofRegroupSettingsProvider();
    }
}
