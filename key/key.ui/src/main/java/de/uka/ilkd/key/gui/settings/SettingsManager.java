package de.uka.ilkd.key.gui.settings;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.extension.ExtensionManager;
import de.uka.ilkd.key.gui.extension.impl.KeYGuiExtensionFacade;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.keyshortcuts.ShortcutSettings;
import de.uka.ilkd.key.gui.smt.settings.SMTSettingsProvider;
import de.uka.ilkd.key.gui.testgen.TestGenOptionsPanel;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.*;

import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.util.Comparator;
import java.util.LinkedList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (08.04.19)
 */
public class SettingsManager {
    public static final TestGenOptionsPanel TEST_GEN_OPTIONS_PANEL = new TestGenOptionsPanel();
    public static final ExtensionManager EXTENSION_MANAGER = new ExtensionManager();
    public static final SettingsProvider SMT_SETTINGS = new SMTSettingsProvider();
    public static final TacletOptionsSettings TACLET_OPTIONS_SETTINGS = new TacletOptionsSettings();
    public static final ShortcutSettings SHORTCUT_SETTINGS = new ShortcutSettings();

    private static SettingsManager INSTANCE;
    private List<SettingsProvider> settingsProviders = new LinkedList<>();

    static SettingsManager createWithExtensions() {
        SettingsManager sm = new SettingsManager();
        KeYGuiExtensionFacade.getSettingsProvider().forEach(it ->
                sm.settingsProviders.add(it.getSettings()));
        return sm;
    }

    public static SettingsManager getInstance() {
        if (INSTANCE == null) {
            INSTANCE = createWithExtensions();
            INSTANCE.add(SHORTCUT_SETTINGS);
            INSTANCE.add(SMT_SETTINGS);
            INSTANCE.add(EXTENSION_MANAGER);
            INSTANCE.add(TEST_GEN_OPTIONS_PANEL);
            INSTANCE.add(TACLET_OPTIONS_SETTINGS);

        }
        return INSTANCE;
    }

    public static ProofDependentSMTSettings getSmtPdSettings(MainWindow window) {
        Proof proof = window.getMediator().getSelectedProof();
        ProofDependentSMTSettings pdSettings;
        if (proof == null) {
            return ProofSettings.DEFAULT_SETTINGS.getSMTSettings();
        } else {
            return proof.getSettings().getSMTSettings();
        }
    }

    public static ProofIndependentSMTSettings getSmtPiSettings() {
        return ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings();
    }

    public static TestGenerationSettings getTestgenSettings() {
        return ProofIndependentSettings.DEFAULT_INSTANCE.getTestGenerationSettings();
    }

    public static ChoiceSettings getChoiceSettings(MainWindow window) {
        return ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
/*        if (null != window.getMediator().getSelectedProof()) {
            return window.getMediator().getSelectedProof().getSettings().getChoiceSettings();
        } else {
            return ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
        }*/
    }

    public static JComponent createSettingsHeaderPanel(String header, String subhead) {
        Box pNorth = new Box(BoxLayout.Y_AXIS);
        pNorth.setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5));
        pNorth.setBackground(Color.WHITE);
        pNorth.setOpaque(true);
        JLabel lblHead = new JLabel(header);
        lblHead.setFont(lblHead.getFont().deriveFont(16f).deriveFont(Font.BOLD));
        pNorth.add(lblHead);
        pNorth.add(new JLabel(subhead));
        pNorth.add(new JSeparator());
        return pNorth;
    }


    public void showSettingsDialog(MainWindow mainWindow) {
        SettingsDialog dialog = createDialog(mainWindow);
        dialog.setVisible(true);
    }

    private SettingsDialog createDialog(MainWindow mainWindow) {
        settingsProviders.sort(Comparator.comparingInt(SettingsProvider::getPriorityOfSettings));
        SettingsDialog dialog = new SettingsDialog(mainWindow);
        dialog.setSettingsProvider(settingsProviders);
        dialog.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
        dialog.setIconImage(IconFactory.keyLogo());
        dialog.setSize(800, 600);
        dialog.setLocationByPlatform(true);
        return dialog;
    }

    public void showSettingsDialog(MainWindow mainWindow, SettingsProvider selectedPanel) {
        SettingsDialog dialog = createDialog(mainWindow);
        dialog.getUi().selectPanel(selectedPanel);
        dialog.setVisible(true);
    }

    public boolean add(SettingsProvider settingsProvider) {
        return settingsProviders.add(settingsProvider);
    }

    public boolean remove(SettingsProvider o) {
        return settingsProviders.remove(o);
    }

    public Action getActionShowSettings(MainWindow window) {
        class ShowSettingsAction extends KeyAction {
            public ShowSettingsAction() {
                setName("Show Settings");
                setIcon(IconFactory.editFile(16));
                lookupAcceleratorKey();
            }

            @Override
            public void actionPerformed(ActionEvent e) {
                showSettingsDialog(window);
            }
        }
        return new ShowSettingsAction();
    }
}
