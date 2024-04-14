package de.uka.ilkd.key.gui.isabelletranslation;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.ContextMenuAdapter;
import de.uka.ilkd.key.gui.extension.api.ContextMenuKind;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.settings.SettingsDialog;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.util.properties.Properties;
import org.jspecify.annotations.NonNull;

import javax.swing.*;
import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

@KeYGuiExtension.Info(name = "Translation", optional = true,
        experimental = true)
public class IsabelleTranslationExtension implements KeYGuiExtension, KeYGuiExtension.Settings, KeYGuiExtension.ContextMenu {

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
            list.add(new TranslationAction(MainWindow.getInstance()));
            return list;
        }
    };

    @Override
    public @NonNull List<Action> getContextActions(@NonNull KeYMediator mediator, @NonNull ContextMenuKind kind, @NonNull Object underlyingObject) {
        return adapter.getContextActions(mediator, kind, underlyingObject);
    }
}
