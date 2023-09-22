/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.smt.settings;

import java.math.RoundingMode;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.settings.SettingsManager;
import de.uka.ilkd.key.gui.settings.SettingsPanel;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings;
import de.uka.ilkd.key.smt.solvertypes.SolverType;

import static de.uka.ilkd.key.gui.smt.settings.SMTSettingsProvider.BUNDLE;

/**
 * @author Alexander Weigl
 * @version 1 (08.04.19)
 */
class SolverOptions extends SettingsPanel implements SettingsProvider {
    private static final String INFO_SOLVER_NAME = "infoSolverName";
    private static final String INFO_SOLVER_PARAMETERS = "infoSolverParameters";
    private static final String INFO_SOLVER_COMMAND = "infoSolverCommand";
    private static final String INFO_SOLVER_SUPPORT = "infoSolverSupport";
    private static final String INFO_SOLVER_INFO = "SOLVER_INFO";
    private static final String[] SOLVER_SUPPORT_TEXT = { BUNDLE.getString("SOLVER_SUPPORTED"),
        BUNDLE.getString("SOLVER_MAY_SUPPORTED"), BUNDLE.getString("SOLVER_UNSUPPORTED") };
    private static final String INFO_SOLVER_TIMEOUT = "SOLVER_TIMEOUT";

    private static final int SOLVER_SUPPORTED = 0;

    private static final int SOLVER_NOT_SUPPOTED = 1;
    private static final int SOLVER_SUPPORT_NOT_CHECKED = 2;
    private final transient SolverType solverType;
    private final JTextField solverCommand;
    private final JTextField solverParameters;
    private final JTextField solverSupported;
    private final JTextField solverName;
    private final JTextField solverInstalled;
    private final JSpinner solverTimeout;

    public SolverOptions(SolverType solverType) {
        this.setName(solverType.getName());
        this.solverType = solverType;
        setHeaderText("SMT Solver: " + getDescription());

        solverName = createSolverName();
        createSolverInformation();
        solverInstalled = createSolverInstalled();
        solverCommand = createSolverCommand();
        solverTimeout = createSolverTimeout();
        solverParameters = createSolverParameters();
        solverSupported = createSolverSupported();
        createDefaultButton();
        createCheckSupportButton();
    }

    private static String versionInfo(String info, String versionString) {
        String builder = info +
            " " +
            "(" +
            versionString +
            ")";
        return builder;
    }

    protected JButton createDefaultButton() {
        JButton toDefaultButton = new JButton("Set parameters to default");
        toDefaultButton.addActionListener(
            arg0 -> solverParameters.setText(solverType.getDefaultSolverParameters()));
        addRowWithHelp(null, new JLabel(), toDefaultButton);
        return toDefaultButton;
    }

    private String createSupportedVersionText() {
        return "The following minimal version is supported: "
            + solverType.getMinimumSupportedVersion();
    }

    private String getSolverSupportText() {
        if (solverType.supportHasBeenChecked()) {
            return solverType.isSupportedVersion() ? SOLVER_SUPPORT_TEXT[SOLVER_SUPPORTED]
                    : SOLVER_SUPPORT_TEXT[SOLVER_NOT_SUPPOTED];
        } else {
            return SOLVER_SUPPORT_TEXT[SOLVER_SUPPORT_NOT_CHECKED];
        }
    }

    private JTextArea createSolverInformation() {
        String info = solverType.getInfo();
        if (info != null && !info.equals("")) {
            JTextArea solverInfo =
                addTextAreaWithoutScroll("Info", info, BUNDLE.getString(INFO_SOLVER_INFO), null);
            solverInfo.setLineWrap(true);
            solverInfo.setWrapStyleWord(true);
            solverInfo.setEditable(false);

            // text field to copy style from
            JTextField textField = new JTextField();
            textField.setEditable(false);
            solverInfo.setBackground(textField.getBackground());
            solverInfo.setBorder(textField.getBorder());

            return solverInfo;
        }
        return null;
    }

    protected JTextField createSolverSupported() {

        JTextField txt = addTextField("Support", getSolverSupportText(),
            BUNDLE.getString(INFO_SOLVER_SUPPORT) + createSupportedVersionText(), emptyValidator());
        txt.setEditable(false);
        return txt;
    }

    private JSpinner createSolverTimeout() {
        var model = new SpinnerNumberModel(0.0, -1.0, Long.MAX_VALUE, 1);
        // Validator is empty as no additional requirements have to be fulfilled by the entered
        // value (except being a number, which is ensured by the model itself).
        var jsp = createNumberTextField(model, emptyValidator());
        // Set the editor so that entered Strings only have three decimal places.
        JSpinner.NumberEditor editor = new JSpinner.NumberEditor(jsp, "#.###");
        // Use floor rounding to be consistent with the value that will be set for the timeout.
        editor.getFormat().setRoundingMode(RoundingMode.FLOOR);
        jsp.setEditor(editor);
        addTitledComponent("Timeout", jsp, BUNDLE.getString(INFO_SOLVER_TIMEOUT));
        return jsp;
    }

    protected JButton createCheckSupportButton() {
        JButton checkForSupportButton = new JButton("Check for support");
        checkForSupportButton.setEnabled(solverType.isInstalled(false));
        checkForSupportButton.addActionListener(arg0 -> {
            solverType.checkForSupport();
            solverSupported.setText(getSolverSupportText());
        });
        addRowWithHelp(null, new JLabel(), checkForSupportButton);
        return checkForSupportButton;
    }

    protected JTextField createSolverParameters() {
        return addTextField("Parameters", solverType.getSolverParameters(),
            BUNDLE.getString(INFO_SOLVER_PARAMETERS), e -> {
            });
    }

    public JTextField createSolverCommand() {
        return addTextField("Command", solverType.getSolverCommand(),
            BUNDLE.getString(INFO_SOLVER_COMMAND), e -> {
            });
    }


    protected JTextField createSolverInstalled() {
        final boolean installed = solverType.isInstalled(true);
        String info = installed ? "yes" : "no";
        if (installed) {
            final String versionString;
            try {
                versionString = solverType.getRawVersion();
                info = versionInfo(info, versionString);
            } catch (RuntimeException re) {
                // this case occurs for instance if the user can see e.g. z3 but doesn't have
                // the permission to execute the solver
                info =
                    "(version: unknown) solver is installed, but trying to access it resulted in an error "
                        + (re.getCause() != null ? re.getCause().getLocalizedMessage()
                                : re.getLocalizedMessage());
            }
        }
        JTextField txt = addTextField("Installed", info, "", emptyValidator());
        txt.setEditable(false);
        return txt;
    }

    protected JTextField createSolverName() {
        JTextField txt = addTextField("Name", solverType.getName(),
            BUNDLE.getString(INFO_SOLVER_NAME), emptyValidator());
        txt.setEditable(false);
        return txt;
    }

    @Override
    public String getDescription() {
        return solverType.getName();
    }

    @Override
    public JComponent getPanel(MainWindow window) {
        setSmtSettings(SettingsManager.getSmtPiSettings().clone());
        return this;
    }

    private void setSmtSettings(ProofIndependentSMTSettings clone) {
        if (clone.containsSolver(solverType)) {
            solverCommand.setText(clone.getCommand(solverType));
            solverParameters.setText(clone.getParameters(solverType));
            solverTimeout.setValue(((double) clone.getSolverTimeout(solverType)) / 1000);
            solverName.setText(solverType.getName());
        } else {
            throw new IllegalStateException("Could not find solver data for type: " + solverType);
        }

        final boolean installed = solverType.isInstalled(true);
        String info = installed ? "yes" : "no";
        if (installed) {
            final String versionString = solverType.getRawVersion();
            info = versionInfo(info, versionString);
        }
        solverInstalled.setText(info);
    }

    @Override
    public void applySettings(MainWindow window) {
        var settings = SettingsManager.getSmtPiSettings();
        if (settings.containsSolver(solverType)) {
            String command = solverCommand.getText();
            String params = solverParameters.getText();
            long timeout = (long) (((Number) solverTimeout.getValue()).doubleValue() * 1000.0);

            solverType.setSolverCommand(command);
            solverType.setSolverParameters(params);
            solverType.setSolverTimeout(timeout);
            // This is not necessary as it just calls solverData.setSolver... again
            // SettingsManager.getSmtPiSettings().setCommand(solverType, command);
            // SettingsManager.getSmtPiSettings().setParameters(solverType, params);
            window.updateSMTSelectMenu();

            setSmtSettings(SettingsManager.getSmtPiSettings().clone()); // refresh gui
        } else {
            throw new IllegalStateException("Could not find solver data for type: " + solverType);
        }
    }
}
