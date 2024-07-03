/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.gui.smt.settings;

import java.util.ArrayList;
import java.util.List;
import java.util.ResourceBundle;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.settings.SettingsManager;
import de.uka.ilkd.key.gui.settings.SettingsPanel;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings.ProgressMode;
import de.uka.ilkd.key.smt.st.SolverType;
import de.uka.ilkd.key.smt.st.SolverTypes;

/**
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

    private transient ProofIndependentSMTSettings settings;
    private transient List<SettingsProvider> children = new ArrayList<>();


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

        getChildren().add(new TranslationOptions());
        getChildren().add(new TacletTranslationOptions());
        getChildren().add(new NewTranslationOptions());

        for (SolverType options : SolverTypes.getSolverTypes()) {
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
        pi.fireSettingsChanged();
        setSmtSettings(pi.clone());
    }

    private JSpinner createLocSetBoundField() {
        return addNumberField("Locset bound:", 0, Integer.MAX_VALUE, 1,
            BUNDLE.getString(INFO_BOUND),
            e -> settings.setLocsetBound(e));
    }

    private JSpinner createMaxProcesses() {
        return addNumberField("Concurrent processes:",
            0, Integer.MAX_VALUE, 1,
            BUNDLE.getString(INFO_MAX_PROCESSES),
            e -> settings.setMaxConcurrentProcesses(e));
    }

    private JSpinner createTimeoutField() {
        return addNumberField("Timeout:", 0, Integer.MAX_VALUE, 1,
            BUNDLE.getString(INFO_TIMEOUT_FIELD),
            e -> settings.setTimeout(e * 1000L));
    }

    private JSpinner createIntBoundField() {
        return addNumberField("Integer bound:", 0, Integer.MAX_VALUE, 1,
            BUNDLE.getString(INFO_BOUND),
            e -> settings.setIntBound(e));
    }

    private JSpinner createSeqBoundField() {
        return addNumberField("Seq bound:", 0, Integer.MAX_VALUE, 1, BUNDLE.getString(INFO_BOUND),
            e -> settings.setSeqBound(e));
    }

    private JSpinner createObjectBoundField() {
        return addNumberField("Object bound:", 0, Integer.MAX_VALUE, 1,
            BUNDLE.getString(INFO_BOUND),
            e -> settings.setObjectBound(e));
    }

    private JComboBox<String> getProgressModeBox() {
        return addComboBox("", BUNDLE.getString(INFO_PROGRESS_MODE_BOX), 0,
            e -> settings.setModeOfProgressDialog(
                ProgressMode.values()[progressModeBox.getSelectedIndex()]),
            getProgressMode(ProgressMode.USER),
            getProgressMode(ProgressMode.CLOSE));
    }

    private JCheckBox createSolverSupportCheck() {
        return addCheckBox("Check for support when a solver is started",
            BUNDLE.getString(INFO_CHECK_FOR_SUPPORT),
            false,
            e -> settings.setCheckForSupport(solverSupportCheck.isSelected()));
    }

    private JTextField getSaveToFilePanel() {
        return addFileChooserPanel("Store translation to file:",
            "", BUNDLE.getString(INFO_SAVE_TO_FILE_PANEL),
            true, e -> settings.setPathForSMTTranslation(saveToFilePanel.getText()));
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
        timeoutField.setValue(((float) this.settings.getTimeout() / 1000));
        maxProcesses.setValue(this.settings.getMaxConcurrentProcesses());
    }
}
