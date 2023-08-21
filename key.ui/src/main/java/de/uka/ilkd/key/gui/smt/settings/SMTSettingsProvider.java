/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.smt.settings;

import java.math.RoundingMode;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.ResourceBundle;
import java.util.stream.Collectors;
import javax.swing.*;

import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.settings.SettingsManager;
import de.uka.ilkd.key.gui.settings.SettingsPanel;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings.ProgressMode;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.smt.solvertypes.SolverType;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;

/**
 * General SMT settings panel in the settings dialog.
 *
 * @author Alexander Weigl
 * @version 1 (08.04.19)
 */
public class SMTSettingsProvider extends SettingsPanel implements SettingsProvider {
    // de/uka/ilkd/key/gui/smt/settings/messages.xml
    public static final ResourceBundle BUNDLE =
        ResourceBundle.getBundle("de.uka.ilkd.key.gui.smt.settings.messages");

    public static final String PROGRESS_MODE_USER = "PROGRESS_MODE_USER";
    public static final String PROGRESS_MODE_CLOSE = "PROGRESS_MODE_CLOSE";
    public static final String PROGRESS_MODE_CLOSE_FIRST = "PROGRESS_MODE_CLOSE_FIRST";
    private static final String INFO_BOUND = "infoBound";
    private static final String INFO_SAVE_TO_FILE_PANEL = "infoSaveToFilePanel";
    private static final String INFO_PROGRESS_MODE_BOX = "infoProgressModeBox";
    private static final String INFO_CHECK_FOR_SUPPORT = "infoCheckForSupport";
    private static final String INFO_MAX_PROCESSES = "infoMaxProcesses";
    private static final String INFO_TIMEOUT_FIELD = "infoTimeoutField";

    private final JTextField saveToFilePanel;

    private final JComboBox<String> progressModeBox;
    private final JSpinner maxProcesses;
    private final JSpinner timeoutField;
    private final JSpinner intBoundField;
    private final JSpinner seqBoundField;
    private final JSpinner objectBoundField;
    private final JSpinner locsetBoundField;
    private final JCheckBox solverSupportCheck;
    private final JCheckBox enableOnLoad;

    private transient ProofIndependentSMTSettings settings;
    private final transient List<SettingsProvider> children = new ArrayList<>();


    public SMTSettingsProvider() {
        saveToFilePanel = getSaveToFilePanel();
        progressModeBox = getProgressModeBox();
        timeoutField = createTimeoutField();
        maxProcesses = createMaxProcesses();
        intBoundField = createIntBoundField();
        objectBoundField = createObjectBoundField();
        locsetBoundField = createLocSetBoundField();
        seqBoundField = createSeqBoundField();
        solverSupportCheck = createSolverSupportCheck();
        enableOnLoad = createEnableOnLoad();

        // Load all available solver types in the system according to SolverTypes.
        // Note that this should happen before creating the NewTranslationOptions, otherwise
        // the SMT translation options used by the solvers' handlers won't be added to the menu.
        Collection<SolverType> solverTypes = SolverTypes.getSolverTypes();

        getChildren().add(new TacletTranslationOptions());
        getChildren().add(new NewTranslationOptions());

        if (!Main.isExperimentalMode()) {
            solverTypes.removeAll(SolverTypes.getLegacySolvers());
        } else {
            getChildren().add(new TranslationOptions());
        }
        /*
         * Only add options for those solvers that are actually theoretically available according to
         * the settings. Note that these aren't necessarily all the types provided by SolverTypes,
         * depending on the implementation of the ProofIndependentSettings.
         */
        for (SolverType options : solverTypes.stream().filter(
            t -> ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings().containsSolver(t))
                .collect(Collectors.toList())) {
            getChildren().add(new SolverOptions(options));
        }
    }

    @Override
    public List<SettingsProvider> getChildren() {
        return children;
    }

    @Override
    public String getDescription() {
        return "SMT";
    }

    @Override
    public JComponent getPanel(MainWindow window) {
        ProofIndependentSMTSettings pi = SettingsManager.getSmtPiSettings();
        setSmtSettings(pi.clone());
        return this;
    }

    @Override
    public void applySettings(MainWindow window) {
        ProofIndependentSMTSettings pi = SettingsManager.getSmtPiSettings();
        pi.copy(settings);
        setSmtSettings(pi.clone());
    }

    private JSpinner createLocSetBoundField() {
        return addNumberField("Locset bound:", 0L, (long) Integer.MAX_VALUE, 1,
            BUNDLE.getString(INFO_BOUND), e -> settings.setLocsetBound(e.longValue()));
    }

    private JSpinner createMaxProcesses() {
        return addNumberField("Concurrent processes:", 0, Integer.MAX_VALUE, 1,
            BUNDLE.getString(INFO_MAX_PROCESSES),
            e -> settings.setMaxConcurrentProcesses(e.intValue()));
    }

    private JSpinner createTimeoutField() {
        // Use doubles so that the formatter doesn't make every entered String into integers.
        // [see NumberFormatter#stringToValue()].
        JSpinner timeoutSpinner = addNumberField("Timeout:", 0.0, (double) Long.MAX_VALUE, 1,
            BUNDLE.getString(INFO_TIMEOUT_FIELD),
            e -> settings.setTimeout((long) Math.floor(e.doubleValue() * 1000)));
        // Set the editor so that entered Strings only have three decimal places.
        JSpinner.NumberEditor editor = new JSpinner.NumberEditor(timeoutSpinner, "#.###");
        // Use floor rounding to be consistent with the value that will be set for the timeout.
        editor.getFormat().setRoundingMode(RoundingMode.FLOOR);
        timeoutSpinner.setEditor(editor);
        return timeoutSpinner;
    }

    private JSpinner createIntBoundField() {
        return addNumberField("Integer bound:", 0L, (long) Integer.MAX_VALUE, 1,
            BUNDLE.getString(INFO_BOUND), e -> settings.setIntBound(e.longValue()));
    }

    private JSpinner createSeqBoundField() {
        return addNumberField("Seq bound:", 0L, (long) Integer.MAX_VALUE, 1,
            BUNDLE.getString(INFO_BOUND), e -> settings.setSeqBound(e.longValue()));
    }

    private JSpinner createObjectBoundField() {
        return addNumberField("Object bound:", 0L, (long) Integer.MAX_VALUE, 1,
            BUNDLE.getString(INFO_BOUND), e -> settings.setObjectBound(e.longValue()));
    }

    private JComboBox<String> getProgressModeBox() {
        return addComboBox("", BUNDLE.getString(INFO_PROGRESS_MODE_BOX), 0,
            e -> settings.setModeOfProgressDialog(
                ProgressMode.values()[progressModeBox.getSelectedIndex()]),
            getProgressMode(ProgressMode.USER), getProgressMode(ProgressMode.CLOSE));
    }

    private JCheckBox createSolverSupportCheck() {
        return addCheckBox("Check for support when a solver is started",
            BUNDLE.getString(INFO_CHECK_FOR_SUPPORT), false,
            e -> settings.setCheckForSupport(solverSupportCheck.isSelected()));
    }

    private JCheckBox createEnableOnLoad() {
        return addCheckBox("Enable SMT solvers when loading proofs",
            "", true,
            e -> settings.setEnableOnLoad(enableOnLoad.isSelected()));
    }

    private JTextField getSaveToFilePanel() {
        return addFileChooserPanel("Store translation to file:", "",
            BUNDLE.getString(INFO_SAVE_TO_FILE_PANEL), true,
            e -> settings.setPathForSMTTranslation(saveToFilePanel.getText()));
    }

    private String getProgressMode(ProgressMode index) {
        switch (index) {
        case USER:
            return BUNDLE.getString(PROGRESS_MODE_USER);
        case CLOSE:
            return BUNDLE.getString(PROGRESS_MODE_CLOSE);
        case CLOSE_FIRST:
            return BUNDLE.getString(PROGRESS_MODE_CLOSE_FIRST);
        }
        return "";
    }

    public void setSmtSettings(ProofIndependentSMTSettings settings) {
        this.settings = settings;
        saveToFilePanel.setText(this.settings.getPathForSMTTranslation());
        solverSupportCheck.setSelected(this.settings.isCheckForSupport());
        progressModeBox.setSelectedIndex(this.settings.getModeOfProgressDialog().ordinal());
        intBoundField.setValue(this.settings.getIntBound());
        locsetBoundField.setValue(this.settings.getLocsetBound());
        objectBoundField.setValue(this.settings.getObjectBound());
        seqBoundField.setValue(this.settings.getSeqBound());
        // Timeout can have up to 3 decimal places in seconds to still be an integer in ms.
        timeoutField.setValue(((double) this.settings.getTimeout()) / 1000);
        maxProcesses.setValue(this.settings.getMaxConcurrentProcesses());
        enableOnLoad.setSelected(this.settings.isEnableOnLoad());
    }
}
