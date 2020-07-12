package de.uka.ilkd.key.gui.smt.settings;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.settings.SettingsManager;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.gui.settings.SettingsPanel;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings;
import de.uka.ilkd.key.smt.SolverType;

import javax.swing.*;
import java.util.ArrayList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (08.04.19)
 */
public class SMTSettingsProvider extends SettingsPanel implements SettingsProvider {
    private static final long serialVersionUID = -5374124826295959483L;
    public final static String PROGRESS_MODE_USER = "Progress dialog remains open after executing solvers.";
    public final static String PROGRESS_MODE_CLOSE = "Close progress dialog after all solvers have finished.";
    public final static String PROGRESS_MODE_CLOSE_FIRST = "Close progress dialog after the first solver has finished.";
    private final static String infoBound = "Bitvector size for this type. Use a value larger than 0.";
    private final static String infoSaveToFilePanel = "Activate this option to store the translations "
            + "that are handed over to the externals solvers:\n"
            + "1. Choose the folder.\n"
            + "2. Specify the filename:\n"
            + "\t%s: the solver's name\n"
            + "\t%d: date\n"
            + "\t%t: time\n"
            + "\t%i: the goal's number\n"
            + "\n\n"
            + "Example: /home/translations/%d_%t_%i_%s.txt"
            + "\n\n"
            + "Remark: After every restart of KeY this option "
            + "is deactivated.";
    private final static String infoProgressModeBox = "1. Option: The progress dialog remains open "
            + "after executing the solvers so that the user "
            + "can decide whether he wants to accept the results.\n"
            + "\n"
            + "2. Option: The progress dialog is closed once the "
            + "external provers have done their work or the time limit "
            + "has been exceeded.\n";// +
    private static final String infoCheckForSupport = "If this option is activated, each time before a solver is started" +
            " it is checked whether the version of that solver is supported. If the version is not supported, a warning is" +
            " presented in the progress dialog.";
    private final static String infoMaxProcesses = "Maximal number or processes that are allowed to run concurrently.";
    private final static String infoTimeoutField = "Timeout for the external solvers in seconds. Fractions of a second are allowed.\n"
            + "Example: 6.5";

    private final JTextField saveToFilePanel;

    private final JComboBox<String> progressModeBox;
    private final JSpinner maxProcesses;
    private final JSpinner timeoutField;
    private final JSpinner intBoundField;
    //private JTextField heapBoundField;
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
        //getChildren().add(new DefaultSettingsProvider("Selection",
        //        new TacletTranslationSelection(smtSettings).getSelectionTree()));
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
        //ProofDependentSMTSettings pd = SettingsManager.getSmtPdSettings(window);
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
    }

    private JSpinner createLocSetBoundField() {
        return addNumberField("Locset bound:", 0, Integer.MAX_VALUE, 1, infoBound,
                e -> settings.locsetBound = e);
    }

    private JSpinner createMaxProcesses() {
        return addNumberField("Concurrent processes:",
                0, Integer.MAX_VALUE, 1,
                infoMaxProcesses,
                e -> settings.maxConcurrentProcesses = e);
    }

    private JSpinner createTimeoutField() {
        return addNumberField("Timeout:", 0, Integer.MAX_VALUE, 1, infoTimeoutField,
                e -> settings.timeout = e * 1000);
    }

    private JSpinner createIntBoundField() {
        return addNumberField("Integer bound:", 0, Integer.MAX_VALUE, 1, infoBound,
                e -> settings.intBound = e);
    }

    private JSpinner createSeqBoundField() {
        return addNumberField("Seq bound:", 0, Integer.MAX_VALUE, 1, infoBound,
                e -> settings.seqBound = e);
    }

    private JSpinner createObjectBoundField() {
        return addNumberField("Object bound:", 0, Integer.MAX_VALUE, 1, infoBound,
                e -> settings.objectBound = e);
    }

    private JComboBox<String> getProgressModeBox() {
        return addComboBox(infoProgressModeBox, 0,
                e -> settings.modeOfProgressDialog = progressModeBox.getSelectedIndex(),
                getProgressMode(ProofIndependentSMTSettings.PROGRESS_MODE_USER),
                getProgressMode(ProofIndependentSMTSettings.PROGRESS_MODE_CLOSE));
    }

    private JCheckBox createSolverSupportCheck() {
        return addCheckBox("Check for support when a solver is started.",
                infoCheckForSupport,
                false,
                e -> settings.checkForSupport = solverSupportCheck.isSelected());
    }

    private JTextField getSaveToFilePanel() {
        return addFileChooserPanel("Store translation to file:",
                "", infoSaveToFilePanel,
                true, e -> {
                    settings.pathForSMTTranslation = saveToFilePanel.getText();
                    //TODO settings.storeSMTTranslationToFile = saveToFilePanel.isSelected();
                });
    }

    private String getProgressMode(int index) {
        switch (index) {
            case ProofIndependentSMTSettings.PROGRESS_MODE_USER:
                return PROGRESS_MODE_USER;
            case ProofIndependentSMTSettings.PROGRESS_MODE_CLOSE:
                return PROGRESS_MODE_CLOSE;
            case ProofIndependentSMTSettings.PROGRESS_MODE_CLOSE_FIRST:
                return PROGRESS_MODE_CLOSE_FIRST;
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
