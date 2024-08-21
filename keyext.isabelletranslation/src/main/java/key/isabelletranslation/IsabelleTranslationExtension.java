package key.isabelletranslation;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.ContextMenuAdapter;
import de.uka.ilkd.key.gui.extension.api.ContextMenuKind;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.pp.PosInSequent;
import org.jspecify.annotations.NonNull;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.swing.*;
import java.util.ArrayList;
import java.util.List;

@KeYGuiExtension.Info(name = "Isabelle Translation", optional = true,
        experimental = false)
public class IsabelleTranslationExtension implements KeYGuiExtension, KeYGuiExtension.Settings, KeYGuiExtension.ContextMenu, KeYGuiExtension.Startup {

    private static final Logger LOGGER = LoggerFactory.getLogger(IsabelleTranslationExtension.class);

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
            list.add(new TranslateAllAction(MainWindow.getInstance()));
            return list;
        }
    };

    @Override
    public @NonNull List<Action> getContextActions(@NonNull KeYMediator mediator, @NonNull ContextMenuKind kind, @NonNull Object underlyingObject) {
        return adapter.getContextActions(mediator, kind, underlyingObject);
    }

    @Override
    public void init(MainWindow window, KeYMediator mediator) {
        IsabelleTranslationSettings.getInstance();
    }
}
