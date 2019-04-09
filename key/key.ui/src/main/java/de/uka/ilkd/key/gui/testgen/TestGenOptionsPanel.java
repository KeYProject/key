package de.uka.ilkd.key.gui.testgen;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.settings.SettingsManager;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.gui.settings.TablePanel;
import de.uka.ilkd.key.settings.TestGenerationSettings;

import javax.swing.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

@SuppressWarnings("serial")
public class TestGenOptionsPanel extends TablePanel implements SettingsProvider {
    private static final String infoApplySymbolicEx = "Performs bounded symbolic execution on the current proof tree. More precisely, the TestGen Macro is executed which the user can also manually execute by right-clicking on the proof tree and selecting Strategy Macros->TestGen.";
    private static final String infoSaveTo = "Choose the folder where the test case files will be written.";
    private static final String infoMaxProcesses = "Maximal number of SMT processes that are allowed to run concurrently.";
    private static final String infoUseJunit = "Generate a JUnit 4 test suite and a test oracle from the postcondition. Disable this option when using a JML runtime checker since the generated code may be too complicated for the runtime checker or may not comply with JML requirements.";
    private static final String infoInvariantForAll = "Includes class invariants in the test data constraints. I.e., require the class invariant of all created objects to be true in the initial state.";
    private static final String infoMaxUnwinds = "Maximal number of loop unwinds or method calls on a branch that is symbolically executed when using the Strategy Macro \"TestGen\". The Strategy Macro is available by right-click on the proof tree.";
    private static final String infoRemoveDuplicates = "Generate a single testcase for two or more nodes which represent the same test data constraint. Two different nodes may represent the same test data constraint, because some formulas from the nodes which cannot be translated into a test case may be filtered out from the test data constraint.";
    private static final String infoRFLSelection = "Enables initialization of protected, private, and ghost fields with test data, " +
            "as well as creation of objects from classes which have no default constructor (requires the Objenesis library)." +
            "This functionality is enabled by RFL.java which is generated along the test suite. Please note, a runtime checker may not be able to handle the generated code.";
    private static final String infoOpenJMLPath = "Set location of openjml.jar. OpenJML is a third-party runtime checker. KeYTestGen generates the shell scripts compileWithOpenJML.sh and executeWithOpenJML.sh in the test output directory to simplify compilation and execution of the tests. The user should visit the OpenJML's website for additional instructions.";
    private static final String infoObjenesisPath = "Set location of objenesis.jar. Objenesis is a thrid-party library allows easy object creation from classes which do not have a (public) default constructur.";
    private static final String infoIncludePostcondition = "Includes the negated post condition in the test data constraint when generating test data. The post condition can only be included for paths (branches) where symbolic execution has finished.";
    private final JTextField saveToFilePanel;
    private final JTextField openJMLPanel;
    private final JTextField objenesisPanel;
    private final JTextField maxProcesses;
    private final JTextField maxUnwinds;
    private final JCheckBox symbolicEx;
    private final JCheckBox useJUnit;
    private final JCheckBox invariantForAll;
    private final JCheckBox includePostCondition;
    private final JCheckBox removeDuplicates;
    private final JCheckBox checkboxRFL;

    private TestGenerationSettings settings = new TestGenerationSettings(
            SettingsManager.getTestgenSettings());

    public TestGenOptionsPanel() {
        symbolicEx = getSymbolicEx();
        maxUnwinds = getMaxUnwinds();
        invariantForAll = getInvariantForall();
        includePostCondition = getIncludePostCondition();
        maxProcesses = getMaxProcesses();
        objenesisPanel = getObjenesisPanel();
        //getRemoveDuplicatesPanel();
        useJUnit = getJUnitPanel();
        openJMLPanel = getOpenJMLPanel();
        saveToFilePanel = getSaveToFilePanel();
        removeDuplicates = getRemoveDuplicatesPanel();
        checkboxRFL = getRFLSelectionPanel();
    }

    private JTextField getMaxProcesses() {
        return addTextField("Concurrent Processes:", Long.toString(settings.getNumberOfProcesses()), infoMaxProcesses,
                e -> {
                    int value;
                    try {
                        value = Integer.parseInt(maxProcesses.getText());
                    } catch (NumberFormatException ex) {
                        value = settings.getNumberOfProcesses();
                    }
                    settings.setConcurrentProcesses(value);
                    settings.fireSettingsChanged();
                });
    }

    private JTextField getMaxUnwinds() {
        return addTextField("Maximal Unwinds:", Long.toString(settings.getMaximalUnwinds()), infoMaxUnwinds,
                e -> {
                    int value;
                    try {
                        value = Integer.parseInt(maxUnwinds.getText());
                    } catch (NumberFormatException ex) {
                        value = settings.getMaximalUnwinds();
                    }
                    settings.setMaxUnwinds(value);
                    settings.fireSettingsChanged();
                });
    }


    private JTextField getSaveToFilePanel() {
        return addFileChooserPanel("Store test cases to folder:",
                settings.getOutputFolderPath(), infoSaveTo,
                true, e -> {
                    settings.setOutputPath(saveToFilePanel.getText());
                    settings.fireSettingsChanged();
                });
    }

    private JTextField getOpenJMLPanel() {
        return addFileChooserPanel("Location of openjml:",
                settings.getOpenjmlPath(), infoOpenJMLPath,
                true, e -> {
                    settings.setOpenjmlPath(openJMLPanel.getText());
                    settings.fireSettingsChanged();
                });
    }

    private JTextField getObjenesisPanel() {
        return addFileChooserPanel("Location of objenesis:",
                settings.getObjenesisPath(), infoObjenesisPath,
                true, e -> {
                    settings.setObjenesisPath(objenesisPanel.getText());
                    settings.fireSettingsChanged();
                });
    }

    private JCheckBox getJUnitPanel() {
        return addCheckBox("Generate JUnit and test oracle", infoUseJunit, settings.useJunit(), e -> {
            settings.setUseJunit(useJUnit.isSelected());
            settings.fireSettingsChanged();
        });
    }

    private JCheckBox getRemoveDuplicatesPanel() {
        return addCheckBox("Remove duplicates", infoRemoveDuplicates, settings.removeDuplicates(), new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                settings.setRemoveDuplicates(removeDuplicates.isSelected());
                settings.fireSettingsChanged();
            }
        });
    }

    private JCheckBox getRFLSelectionPanel() {
        return
                addCheckBox("Use reflection framework", infoRFLSelection, settings.useRFL(), new ActionListener() {
                    @Override
                    public void actionPerformed(ActionEvent e) {
                        settings.setRFL(checkboxRFL.isSelected());
                        settings.fireSettingsChanged();
                    }
                });
    }

    private JCheckBox getSymbolicEx() {
        return addCheckBox("Apply symbolic execution", infoApplySymbolicEx, settings.getApplySymbolicExecution(), new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                settings.setApplySymbolicExecution(symbolicEx.isSelected());
                settings.fireSettingsChanged();
            }
        });
    }

    private JCheckBox getInvariantForall() {
        return addCheckBox("Require invariant for all objects", infoInvariantForAll, settings.invaraiantForAll(), new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                settings.setInvariantForAll(invariantForAll.isSelected());
                settings.fireSettingsChanged();
            }
        });
    }

    private JCheckBox getIncludePostCondition() {
        return addCheckBox("Include Post Condition", infoIncludePostcondition, settings.includePostCondition(), new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                settings.setIncludePostCondition(includePostCondition.isSelected());
                settings.fireSettingsChanged();
            }
        });
    }

    @Override
    public String getDescription() {
        return "TestGen";
    }

    @Override
    public JComponent getPanel(MainWindow window) {
        return this;
    }

    @Override
    public void applySettings(MainWindow window) {
        TestGenerationSettings globalSettings = SettingsManager.getTestgenSettings();
        //TODO copy from settings to globalSettings
    }
}