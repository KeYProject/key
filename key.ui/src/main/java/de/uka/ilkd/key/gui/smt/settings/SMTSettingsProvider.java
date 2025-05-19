/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.smt.settings;

import java.math.RoundingMode;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.settings.SettingsManager;
import de.uka.ilkd.key.gui.settings.SettingsPanel;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.settings.FeatureSettings;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings.ProgressMode;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.smt.solvertypes.SolverType;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;

import static de.uka.ilkd.key.settings.FeatureSettings.createFeature;

/**
 * General SMT settings panel in the settings dialog.
 *
 * @author Alexander Weigl
 * @version 1 (08.04.19)
 */
public class SMTSettingsProvider extends SettingsPanel implements SettingsProvider {
    public static final String PROGRESS_MODE_USER =
        "Progress dialog remains open after executing solvers";
    public static final String PROGRESS_MODE_CLOSE =
        "Close progress dialog after all solvers have finished";
    public static final String PROGRESS_MODE_CLOSE_FIRST =
        "Close progress dialog after the first solver has finished";
    public static final String INFO_BOUND =
        "Bitvector size for this type. Use a value larger than 0.";
    public static final String INFO_SAVE_TO_FILE_PANEL =
        """
                Activate this option to store the translations that are handed over to the externals solvers:
                        1. Choose the folder.
                        2. Specify the filename:
                             %s: the solver's name
                             %d: date
                             %t: time
                             %i: the goal's number
                           Example: /home/translations/%d_%t_%i_%s.txt"
                Remark: After every restart of KeY this option\
                is deactivated.""";

    public static final String INFO_SOLVER_NAME =
        """
                There are two ways to make supported provers applicable for KeY:
                  1. Specify the absolute path of the prover in the field 'Command'.
                  2. Change the environment variable $PATH of your system, so that it
                refers to the installed prover. In that case you must specify the name of the solver in 'Command'""";
    public static final String INFO_PROGRESS_MODE_BOX =
        """
                1. Option: The progress dialog remains open after executing the solvers so that the user\
                can decide whether he wants to accept the results.
                2. Option: The progress dialog is closed once the external provers have done their work or the time limit\
                has been exceeded.""";
    public static final String INFO_CHECK_FOR_SUPPORT =
        """
                If this option is activated, each time before a solver is started\
                it is checked whether the version of that solver is supported. If the version is not supported, a warning is\
                presented in the progress dialog.""";
    public static final String INFO_MAX_PROCESSES =
        "Maximal number or processes that are allowed to run concurrently";
    public static final String INFO_TIMEOUT_FIELD =
        """
                Timeout for the external solvers in seconds. Fractions of a second are allowed. Example: 6.5
                """;
    public static final String INFO_SOLVER_COMMAND = """
            The command for the solver.

            Either you specify the absolute path of your solver or just the command for starting it.
            In the latter case you have to modify the PATH-variable of your system.
            Please note that you also have to specify the filename extension.
            For example: z3.exe""";

    public static final String INFO_SOLVER_PARAMETERS =
        """
                In this field you can specify which parameters are passed to the \
                solver when the solver is started. Note that the default parameters are crucial for a stable run of the\
                solver.""";

    public static final String INFO_SOLVER_SUPPORT =
        """
                For the KeY system only some particular versions of this solver
                have been tested. It is highly recommended to use those versions, because otherwise it is not guaranteed that
                the connection to this solver is stable.
                If you want to check whether the installed solver is supported, please click on the button below.""";

    public static final String SOLVER_SUPPORTED = "Version of solver is supported.";
    public static final String SOLVER_MAY_SUPPORTED = "Version of solver may not be supported.";
    public static final String SOLVER_UNSUPPORTED = "Support has not been checked, yet.";
    public static final String INFO_SOLVER_TIMEOUT =
        "Overrides timeout for this solver. Values in seconds. If value <= 0, global timeout is used.";
    public static final String INFO_SOLVER_INFO = "Information about this solver.";

    private static final FeatureSettings.Feature FEATURE_SMT_TRANSLATION_OPTIONS =
        createFeature("SMT_TRANS_OPTIONS");

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

        if (FeatureSettings.isFeatureActivated(FEATURE_SMT_TRANSLATION_OPTIONS)) {
            getChildren().add(new TranslationOptions());
        } else {
            solverTypes.removeAll(SolverTypes.getExperimentalSolvers());
        }
        /*
         * Only add options for those solvers that are actually theoretically available, according
         * to
         * the settings. Note that these aren't necessarily all the types provided by SolverTypes,
         * depending on the implementation of the ProofIndependentSettings.
         */
        for (SolverType options : solverTypes.stream().filter(
            t -> ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings().containsSolver(t))
                .toList()) {
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
    public JPanel getPanel(MainWindow window) {
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
        return addNumberField("LocSet bound:", 0L, (long) Integer.MAX_VALUE, 1,
            INFO_BOUND, e -> settings.setLocsetBound(e.longValue()));
    }

    private JSpinner createMaxProcesses() {
        return addNumberField("Concurrent processes:", 0, Integer.MAX_VALUE, 1,
            INFO_MAX_PROCESSES,
            e -> settings.setMaxConcurrentProcesses(e.intValue()));
    }

    private JSpinner createTimeoutField() {
        // Use doubles so that the formatter doesn't make every entered String into integers.
        // [see NumberFormatter#stringToValue()].
        JSpinner timeoutSpinner = addNumberField("Timeout:", 0.0, (double) Long.MAX_VALUE, 1,
            INFO_TIMEOUT_FIELD,
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
            INFO_BOUND, e -> settings.setIntBound(e.longValue()));
    }

    private JSpinner createSeqBoundField() {
        return addNumberField("Seq bound:", 0L, (long) Integer.MAX_VALUE, 1,
            INFO_BOUND, e -> settings.setSeqBound(e.longValue()));
    }

    private JSpinner createObjectBoundField() {
        return addNumberField("Object bound:", 0L, (long) Integer.MAX_VALUE, 1,
            INFO_BOUND, e -> settings.setObjectBound(e.longValue()));
    }

    private JComboBox<String> getProgressModeBox() {
        return addComboBox("", INFO_PROGRESS_MODE_BOX, 0,
            e -> settings.setModeOfProgressDialog(
                ProgressMode.values()[progressModeBox.getSelectedIndex()]),
            getProgressMode(ProgressMode.USER), getProgressMode(ProgressMode.CLOSE));
    }

    private JCheckBox createSolverSupportCheck() {
        return addCheckBox("Check for support when a solver is started",
            INFO_CHECK_FOR_SUPPORT, false,
            e -> settings.setCheckForSupport(solverSupportCheck.isSelected()));
    }

    private JCheckBox createEnableOnLoad() {
        return addCheckBox("Enable SMT solvers when loading proofs",
            "", true,
            e -> settings.setEnableOnLoad(enableOnLoad.isSelected()));
    }

    private JTextField getSaveToFilePanel() {
        return addFileChooserPanel("Store translation to file:", "",
            INFO_SAVE_TO_FILE_PANEL, true,
            e -> settings.setPathForSMTTranslation(saveToFilePanel.getText()));
    }

    private String getProgressMode(ProgressMode index) {
        return switch (index) {
        case USER -> PROGRESS_MODE_USER;
        case CLOSE -> PROGRESS_MODE_CLOSE;
        case CLOSE_FIRST -> PROGRESS_MODE_CLOSE_FIRST;
        };
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
