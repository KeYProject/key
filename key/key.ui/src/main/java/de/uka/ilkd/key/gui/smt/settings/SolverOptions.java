package de.uka.ilkd.key.gui.smt.settings;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.settings.SettingsManager;
import de.uka.ilkd.key.gui.settings.SettingsPanel;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings;
import de.uka.ilkd.key.smt.SolverType;

import javax.swing.*;

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
    private static final String[] solverSupportText = {
            BUNDLE.getString("SOLVER_SUPPORTED"),
            BUNDLE.getString("SOLVER_MAY_SUPPORTED"),
            BUNDLE.getString("SOLVER_UNSUPPORTED")};

    private static final int SOLVER_SUPPORTED = 0;

    private static final int SOLVER_NOT_SUPPOTED = 1;
    private static final int SOLVER_SUPPORT_NOT_CHECKED = 2;
    private final SolverType solverType;
    private final JTextField solverCommand;
    private final JTextField solverParameters;
    private final JTextField solverSupported;
    private final JTextField solverName;
    private final JTextField solverInstalled;

    public SolverOptions(SolverType solverType) {
        this.setName(solverType.getName());
        this.solverType = solverType;
        setHeaderText("SMT Solver: " + getDescription());

        solverName = createSolverName();
        solverInstalled = createSolverInstalled();
        solverCommand = createSolverCommand();
        solverParameters = createSolverParameters();
        solverSupported = createSolverSupported();
        createDefaultButton();
        createCheckSupportButton();
    }

    protected JButton createDefaultButton() {
        JButton toDefaultButton = new JButton("Set parameters to default.");
        toDefaultButton.addActionListener(arg0 -> {
            solverParameters.setText(solverType.getDefaultSolverParameters());
            //settings.setParameters(solverType, solverParameters.getText());
        });
        addRowWithHelp(null, new JLabel(), toDefaultButton);
        return toDefaultButton;
    }

    private String createSupportedVersionText() {
        String[] versions = solverType.getSupportedVersions();
        StringBuilder result = new StringBuilder(versions.length > 1 ? "The following versions are supported: " :
                "The following version is supported: ");
        for (int i = 0; i < versions.length; i++) {
            result.append(versions[i]);
            result.append(i < versions.length - 1 ? ", " : "");
        }
        return result.toString();
    }

    private String getSolverSupportText() {
        if (solverType.supportHasBeenChecked()) {
            return solverType.isSupportedVersion() ? solverSupportText[SOLVER_SUPPORTED] : solverSupportText[SOLVER_NOT_SUPPOTED];
        } else {
            return solverSupportText[SOLVER_SUPPORT_NOT_CHECKED];
        }
    }

    protected JTextField createSolverSupported() {

        JTextField txt = addTextField("Support", getSolverSupportText(),
                BUNDLE.getString(INFO_SOLVER_SUPPORT) + createSupportedVersionText(), null);
        txt.setEditable(false);
        return txt;
    }

    protected JButton createCheckSupportButton() {
        JButton checkForSupportButton = new JButton("Check for support.");
        checkForSupportButton.setEnabled(solverType.isInstalled(false));
        checkForSupportButton.addActionListener(arg0 -> {
            solverType.checkForSupport();
            solverSupported.setText(getSolverSupportText());
        });
        addRowWithHelp(null, new JLabel(), checkForSupportButton);
        return checkForSupportButton;
    }

    protected JTextField createSolverParameters() {
        return addTextField("Parameters", solverType.getSolverParameters(), BUNDLE.getString(INFO_SOLVER_PARAMETERS),
                e -> {});
    }

    public JTextField createSolverCommand() {
        return addTextField("Command",
                solverType.getSolverCommand(),
                BUNDLE.getString(INFO_SOLVER_COMMAND), e -> {});
    }


    protected JTextField createSolverInstalled() {
        final boolean installed = solverType.isInstalled(true);
        String info = installed ? "yes" : "no";
        if (installed) {
            final String versionString = solverType.getRawVersion();
            info = info + (versionString.startsWith("version") ? " (" : " (version ") + versionString + ")";
        }
        JTextField txt = addTextField("Installed", info, "", null);
        txt.setEditable(false);
        return txt;
    }

    protected JTextField createSolverName() {
        JTextField txt = addTextField("Name", solverType.getName(), BUNDLE.getString(INFO_SOLVER_NAME), null);
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
        solverCommand.setText(clone.getCommand(solverType));
        solverParameters.setText(clone.getParameters(solverType));
        solverName.setText(solverType.getName());

        final boolean installed = solverType.isInstalled(true);
        String info = installed ? "yes" : "no";
        if (installed) {
            final String versionString = solverType.getRawVersion();
            info = info + (versionString.startsWith("version") ? " (" : " (version ") + versionString + ")";
        }
        solverInstalled.setText(info);
    }

    @Override
    public void applySettings(MainWindow window) {
        String command = solverCommand.getText();
        String params = solverParameters.getText();
        solverType.setSolverCommand(command);
        solverType.setSolverParameters(params);
        SettingsManager.getSmtPiSettings().setCommand(solverType, command);
        SettingsManager.getSmtPiSettings().setParameters(solverType, params);
        
        setSmtSettings(SettingsManager.getSmtPiSettings().clone()); // refresh gui
    }
}
