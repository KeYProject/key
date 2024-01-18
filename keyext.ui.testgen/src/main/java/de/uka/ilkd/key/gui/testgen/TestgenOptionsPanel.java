/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.testgen;

import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.settings.SettingsPanel;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.testgen.Format;
import de.uka.ilkd.key.testgen.settings.TestGenerationSettings;

public class TestgenOptionsPanel extends SettingsPanel implements SettingsProvider {
    private static final long serialVersionUID = -2170118134719823425L;
    private static final String INFO_APPLY_SYMBOLIC_EX =
        "Performs bounded symbolic execution on the current proof tree."
            + " More precisely, the TestGen Macro is executed which the user can also manually execute by right-clicking "
            + "on the proof tree and selecting Strategy Macros->TestGen.";
    private static final String INFO_SAVE_TO =
        "Choose the folder where the test case files will be written.";
    private static final String INFO_MAX_PROCESSES =
        "Maximal number of SMT processes that are allowed to " + "run concurrently.";
    private static final String INFO_USE_JUNIT = "Generate a JUnit 4 test suite and a test oracle "
        + "from the postcondition. Disable this option when using a JML runtime checker since the "
        + "generated code may be too complicated for the runtime checker or may not comply with JML requirements.";
    private static final String INFO_INVARIANT_FOR_ALL =
        "Includes class invariants in the test data constraints. "
            + "I.e., require the class invariant of all created objects to be true in the initial state.";
    private static final String INFO_MAX_UNWINDS =
        "Maximal number of loop unwinds or method calls on a branch that "
            + "is symbolically executed when using the Strategy Macro \"TestGen\". The Strategy Macro is available"
            + " by right-click on the proof tree.";
    private static final String INFO_REMOVE_DUPLICATES =
        "Generate a single testcase for two or more nodes which "
            + "represent the same test data constraint. Two different nodes may represent the same test data constraint, "
            + "because some formulas from the nodes which cannot be translated into a test case may be filtered out from "
            + "the test data constraint.";
    private static final String INFO_RFL_SELECTION =
        "Enables initialization of protected, private, and ghost fields " + "with test data, "
            + "as well as creation of objects from classes which have no default constructor "
            + "(requires the Objenesis library)."
            + "This functionality is enabled by RFL.java which is generated along the test suite. Please note, "
            + "a runtime checker may not be able to handle the generated code.";
    private static final String INFO_OPEN_JML_PATH =
        "Set location of openjml.jar. OpenJML is a third-party "
            + "runtime checker. KeYTestGen generates the shell scripts compileWithOpenJML.sh and executeWithOpenJML.sh "
            + "in the test output directory to simplify compilation and execution of the tests. The user should visit "
            + "the OpenJML's website for additional instructions.";
    private static final String INFO_OBJENESIS_PATH =
        "Set location of objenesis.jar. Objenesis is a thrid-party "
            + "library allows easy object creation from classes which do not have a (public) default constructur.";
    private static final String INFO_INCLUDE_POSTCONDITION =
        "Includes the negated post condition in the test data "
            + "constraint when generating test data. The post condition can only be included for paths (branches)"
            + " where symbolic execution has finished.";
    private final JTextField saveToFilePanel;
    private final JTextField openJMLPanel;
    private final JTextField objenesisPanel;
    private final JSpinner maxProcesses;
    private final JSpinner maxUnwinds;
    private final JCheckBox symbolicEx;
    private final JComboBox<Format> useJUnit;
    private final JCheckBox invariantForAll;
    private final JCheckBox includePostCondition;
    private final JCheckBox removeDuplicates;
    private final JCheckBox checkboxRFL;

    private transient TestGenerationSettings settings =
        new TestGenerationSettings(TestGenerationSettings.getInstance());

    public TestgenOptionsPanel() {
        setHeaderText(getDescription());
        symbolicEx = getSymbolicEx();
        maxUnwinds = getMaxUnwinds();
        invariantForAll = getInvariantForall();
        includePostCondition = getIncludePostCondition();
        maxProcesses = getMaxProcesses();
        objenesisPanel = getObjenesisPanel();
        useJUnit = getJUnitPanel();
        openJMLPanel = getOpenJMLPanel();
        saveToFilePanel = getSaveToFilePanel();
        removeDuplicates = getRemoveDuplicatesPanel();
        checkboxRFL = getRFLSelectionPanel();
    }

    private JSpinner getMaxProcesses() {
        return addNumberField("Concurrent processes:", 0, Integer.MAX_VALUE, 1, INFO_MAX_PROCESSES,
            obj -> {
                settings.setConcurrentProcesses(obj.intValue());
            });
    }

    private JSpinner getMaxUnwinds() {
        return addNumberField("Maximal unwinds:", 0, Integer.MAX_VALUE, 1, INFO_MAX_UNWINDS, e -> {
            settings.setMaxUnwinds(e.intValue());
        });
    }


    private JTextField getSaveToFilePanel() {
        return addFileChooserPanel("Store test cases to folder:", "", INFO_SAVE_TO, true, e -> {
            settings.setOutputPath(saveToFilePanel.getText());
        });
    }

    private JTextField getOpenJMLPanel() {
        return addFileChooserPanel("Location of openjml:", "", INFO_OPEN_JML_PATH, false, e -> {
            settings.setOpenjmlPath(openJMLPanel.getText());
        });
    }

    private JTextField getObjenesisPanel() {
        return addFileChooserPanel("Location of objenesis:", "", INFO_OBJENESIS_PATH, false, e -> {
            settings.setObjenesisPath(objenesisPanel.getText());
        });
    }

    private JComboBox<Format> getJUnitPanel() {
        return addComboBox("Set the format", INFO_USE_JUNIT, 0, val -> {
            settings.setFormat(val);
        }, Format.values());
    }

    private JCheckBox getRemoveDuplicatesPanel() {
        return addCheckBox("Remove duplicates", INFO_REMOVE_DUPLICATES, false, val -> {
            settings.setRemoveDuplicates(val);
        });
    }

    private JCheckBox getRFLSelectionPanel() {
        return addCheckBox("Use reflection framework", INFO_RFL_SELECTION, false, val -> {
            settings.setRFL(val);
        });
    }

    private JCheckBox getSymbolicEx() {
        return addCheckBox("Apply symbolic execution", INFO_APPLY_SYMBOLIC_EX, false, val -> {
            settings.setApplySymbolicExecution(val);
        });
    }

    private JCheckBox getInvariantForall() {
        return addCheckBox("Require invariant for all objects", INFO_INVARIANT_FOR_ALL, false,
            val -> {
                settings.setInvariantForAll(val);
            });
    }

    private JCheckBox getIncludePostCondition() {
        return addCheckBox("Include post condition", INFO_INCLUDE_POSTCONDITION, false, val -> {
            settings.setIncludePostCondition(val);
        });
    }

    @Override
    public String getDescription() {
        return "TestGen";
    }

    @Override
    public JPanel getPanel(MainWindow window) {
        settings = new TestGenerationSettings(TestGenerationSettings.getInstance());
        includePostCondition.setSelected(settings.includePostCondition());
        invariantForAll.setSelected(settings.invariantForAll());
        useJUnit.setSelectedItem(settings.useJunit());
        symbolicEx.setSelected(settings.getApplySymbolicExecution());
        removeDuplicates.setSelected(settings.removeDuplicates());
        checkboxRFL.setSelected(settings.useRFL());
        objenesisPanel.setText(settings.getObjenesisPath());
        openJMLPanel.setText(settings.getOpenjmlPath());
        saveToFilePanel.setText(settings.getOutputFolderPath());
        return this;
    }

    @Override
    public void applySettings(MainWindow window) {
        TestGenerationSettings globalSettings = TestGenerationSettings.getInstance();
        globalSettings.set(settings);
    }
}
