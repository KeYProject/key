package de.uka.ilkd.key.gui.smt.settings;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.settings.SettingsManager;
import de.uka.ilkd.key.gui.settings.SettingsPanel;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings;
import de.uka.ilkd.key.smt.SolverType;


import javax.swing.*;
import java.util.ArrayList;
import java.util.List;
import java.util.ResourceBundle;

/**
 * @author Alexander Weigl
 * @version 1 (08.04.19)
 */
public class SMTSettingsProvider extends SettingsPanel implements SettingsProvider {
    //de/uka/ilkd/key/gui/smt/settings/messages.xml
    public static final ResourceBundle BUNDLE
            = ResourceBundle.getBundle("de.uka.ilkd.key.gui.smt.settings.messages");

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

    private ProofIndependentSMTSettings settings;
    private List<SettingsProvider> children = new ArrayList<>();


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

        for (SolverType options : SolverType.ALL_SOLVERS) {
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
        if (window.getMediator().getSelectedProof() == null) {
            //TODO maybe special handling
        }
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
        return addNumberField("Locset bound:", 0, Integer.MAX_VALUE, 1, BUNDLE.getString(INFO_BOUND),
                e -> settings.locsetBound = e);
    }

    private JSpinner createMaxProcesses() {
        return addNumberField("Concurrent processes:",
                0, Integer.MAX_VALUE, 1,
                BUNDLE.getString(INFO_MAX_PROCESSES),
                e -> settings.maxConcurrentProcesses = e);
    }

    private JSpinner createTimeoutField() {
        return addNumberField("Timeout:", 0, Integer.MAX_VALUE, 1, BUNDLE.getString(INFO_TIMEOUT_FIELD),
                e -> settings.timeout = e * 1000);
    }

    private JSpinner createIntBoundField() {
        return addNumberField("Integer bound:", 0, Integer.MAX_VALUE, 1, BUNDLE.getString(INFO_BOUND),
                e -> settings.intBound = e);
    }

    private JSpinner createSeqBoundField() {
        return addNumberField("Seq bound:", 0, Integer.MAX_VALUE, 1, BUNDLE.getString(INFO_BOUND),
                e -> settings.seqBound = e);
    }

    private JSpinner createObjectBoundField() {
        return addNumberField("Object bound:", 0, Integer.MAX_VALUE, 1, BUNDLE.getString(INFO_BOUND),
                e -> settings.objectBound = e);
    }

    private JComboBox<String> getProgressModeBox() {
        return addComboBox(BUNDLE.getString(INFO_PROGRESS_MODE_BOX), 0,
                e -> settings.modeOfProgressDialog = progressModeBox.getSelectedIndex(),
                getProgressMode(ProofIndependentSMTSettings.PROGRESS_MODE_USER),
                getProgressMode(ProofIndependentSMTSettings.PROGRESS_MODE_CLOSE));
    }

    private JCheckBox createSolverSupportCheck() {
        return addCheckBox("Check for support when a solver is started.",
                BUNDLE.getString(INFO_CHECK_FOR_SUPPORT),
                false,
                e -> settings.checkForSupport = solverSupportCheck.isSelected());
    }

    private JTextField getSaveToFilePanel() {
        return addFileChooserPanel("Store translation to file:",
                "", BUNDLE.getString(INFO_SAVE_TO_FILE_PANEL),
                true, e -> {
                    settings.pathForSMTTranslation = saveToFilePanel.getText();
                    //TODO settings.storeSMTTranslationToFile = saveToFilePanel.isSelected();
                });
    }

    private String getProgressMode(int index) {
        switch (index) {
            case ProofIndependentSMTSettings.PROGRESS_MODE_USER:
                return BUNDLE.getString(PROGRESS_MODE_USER);
            case ProofIndependentSMTSettings.PROGRESS_MODE_CLOSE:
                return BUNDLE.getString(PROGRESS_MODE_CLOSE);
            case ProofIndependentSMTSettings.PROGRESS_MODE_CLOSE_FIRST:
                return BUNDLE.getString(PROGRESS_MODE_CLOSE_FIRST);
        }
        return "";
    }

    public void setSmtSettings(ProofIndependentSMTSettings settings) {
        this.settings = settings;
        saveToFilePanel.setText(this.settings.pathForSMTTranslation);
        solverSupportCheck.setSelected(this.settings.checkForSupport);
        progressModeBox.setSelectedIndex(this.settings.modeOfProgressDialog);
        intBoundField.setValue(this.settings.intBound);
        locsetBoundField.setValue(this.settings.locsetBound);
        objectBoundField.setValue(this.settings.objectBound);
        seqBoundField.setValue(this.settings.seqBound);
        timeoutField.setValue(((float) this.settings.timeout / 1000));
        maxProcesses.setValue(this.settings.maxConcurrentProcesses);
    }
}
