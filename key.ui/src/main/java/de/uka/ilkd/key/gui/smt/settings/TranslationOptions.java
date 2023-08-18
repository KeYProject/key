/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.smt.settings;

import java.awt.*;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.settings.SettingsManager;
import de.uka.ilkd.key.gui.settings.SettingsPanel;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.settings.ProofDependentSMTSettings;

/**
 * @author Alexander Weigl
 * @version 1 (08.04.19)
 */
class TranslationOptions extends SettingsPanel implements SettingsProvider {
    private static final long serialVersionUID = 7299370317491756605L;
    private static final String infoUseExplicitTypeHierarchy =
        "If this option is selected, the transitive inheritance between classes is modeled by "
            + "assumptions.\n\n"
            + "Example: Let A, B and C  be classes such that C extends B and B extends A.\n"
            + "If the option is not selected, the following assumptions are added:\n"
            + "\\forall x; (type_of_C(x)->type_of_B(x))\n"
            + "\\forall x; (type_of_B(x)->type_of_A(x))\n"
            + "If the option is selected, the following assumption is additionally added to the assumptions above:\n"
            + "\\forall x; (type_of_C(x)->type_of_A(x))\n";
    private static final String infoUseNullInstantiation =
        "At the moment this option has only effect on hierarchy assumptions regarding the null object.\n"
            + "Example: Let A and B be classes.\n"
            + "If the option is not selected, the type null is treated as a normal class. "
            + "Consequently, the following assumptions are added:\n"
            + "\\forall x; (type_of_Null(x)->type_of_A(x))\n"
            + "\\forall x; (type_of_Null(x)->type_of_B(x))\n"
            + "If the option is selected, those assumptions are instantiated with a concrete null object:\n"
            + "type_of_A(null)\n" + "type_of_B(null)";
    private static final String infoUseBuiltInUniqueness =
        "Some solvers support the uniqueness of functions by built-in mechanisms. If this option is selected "
            + "those mechanisms are used, otherwise some assumptions are added by using normal FOL.\n"
            + "Note: The uniqueness of functions is needed for translating attributes and arrays.";
    private static final String infoUseUIMultiplication =
        "Some solvers support only simple multiplications. For example Yices supports only multiplications of type a*b"
            + " where a or b must be a number.\n"
            + "In order to support more complex multiplications, this option can be activated: If the solver does not support a"
            + " certain kind of multiplication, the occurence of this multiplication is translated"
            + " into the uninterpreted function mult. Furthermore some"
            + " typical assumptions are added:\n" + "\\forall x; mult(x,0)=0\n"
            + "\\forall x; mult(0,x)=0\n" + "\\forall x; mult(x,1)=x\n"
            + "\\forall x; mult(1,x)=x\n" + "\\forall x; \\forall y; mult(x,y)=mult(y,x)\n"
            + "\\forall x; \\forall y; \\forall z; mult(mult(x,y),z)=mult(x,mult(y,z))\n"
            + "\\forall x; \\forall y; mult(x,y)=0 -> (x=0|y=0)\n"
            + "\\forall x; \\forall y; mult(x,y)=1 -> (x=1&y=1)\n" + "Note:\n"
            + "1. If this option is not selected, an exception is thrown in the case that a unsupported multiplication "
            + "occurs.\n"
            + "2. The translation makes the uninterpreted function mult unique, so that there cannot be any clashes with functions"
            + " that are introduced by the user.";
    private static final String infoUseConstantsForIntegers =
        "Some solvers support only a certain interval of integers (e.g. Simplify). If this option is activated,"
            + " numbers that are not supported by the used solver are translated into uninterpreted constants. Furthermore "
            + " an asumption is added that states that the introduced constant is greater than the maximum of the supported numbers.\n\n"
            + "Example: Assume that a solver supports numbers less or equal 10:\n"
            + "The number 11 is translated into the constant c_11 and the assumption"
            + " c_11>10 is introduced.\n\n"
            + "Note: If this option is not selected, an exception is thrown in the case that a not supported number occurs.\n";
    private final JCheckBox useExplicitTypeHierachy;
    private final JCheckBox useNullInstantiation;
    private final JCheckBox useBuiltInUniqueness;
    private final JCheckBox useUIMultiplication;
    private final JCheckBox useConstantsForIntegers;
    private final JSpinner minField;
    private final JSpinner maxField;
    private ProofDependentSMTSettings settings;


    public TranslationOptions() {
        setHeaderText(getDescription());
        useExplicitTypeHierachy = createUseExplicitTypeHierachy();
        useNullInstantiation = createNullInstantiation();
        useBuiltInUniqueness = createBuiltInUniqueness();
        useUIMultiplication = createUIMultiplication();
        addSeparator("Use constants for too big or too small integers.");
        useConstantsForIntegers = createConstantsForIntegers();
        minField = createMinField();
        maxField = createMaxField();

    }

    public void setSmtSettings(ProofDependentSMTSettings settings) {
        this.settings = settings;
        if (settings == null) {
            setEnabled(false);
        } else {
            setEnabled(true);
            useExplicitTypeHierachy.setSelected(settings.isUseExplicitTypeHierarchy());
            useNullInstantiation.setSelected(settings.isUseNullInstantiation());
            useBuiltInUniqueness.setSelected(settings.isUseBuiltInUniqueness());
            useConstantsForIntegers.setSelected(settings.isUseConstantsForIntegers());
            minField.setValue(settings.getMinInteger());
            maxField.setValue(settings.getMaxInteger());
        }
    }


    protected JCheckBox createUseExplicitTypeHierachy() {
        return addCheckBox("Use an explicit type hierarchy.", infoUseExplicitTypeHierarchy, false,
            e -> settings.setUseExplicitTypeHierarchy(useExplicitTypeHierachy.isSelected()));
    }

    protected JCheckBox createNullInstantiation() {
        return addCheckBox("Instantiate hierarchy assumptions if possible (recommended).",
            infoUseNullInstantiation, false,
            e -> settings.setUseNullInstantiation(useNullInstantiation.isSelected()));
    }

    protected JCheckBox createBuiltInUniqueness() {
        return addCheckBox("Use built-in mechanism for uniqueness if possible.",
            infoUseBuiltInUniqueness, false,
            e -> settings.setUseBuiltInUniqueness(useBuiltInUniqueness.isSelected()));
    }

    protected JCheckBox createUIMultiplication() {
        return addCheckBox("Use uninterpreted multiplication if necessary.",
            infoUseUIMultiplication, false,
            e -> settings.setUseUIMultiplication(useUIMultiplication.isSelected()));
    }

    protected JSpinner createMaxField() {
        JSpinner max = addNumberField("Maximum", Integer.MIN_VALUE, Integer.MAX_VALUE, 1, "", e -> {
            long result = Integer.MAX_VALUE;
            if (settings != null) {
                result = settings.getMaxInteger();
            }
            try {
                result = (long) maxField.getValue();
                maxField.setForeground(Color.BLACK);
            } catch (Throwable ex) {
                maxField.setForeground(Color.RED);
            }
            settings.setMaxInteger(result);
        });
        max.setValue(Integer.MAX_VALUE);
        return max;
    }

    protected JSpinner createMinField() {
        return addNumberField("Minimum", Integer.MIN_VALUE, Integer.MAX_VALUE, 1, "",
            val -> settings.setMinInteger(val.longValue()));
    }

    protected JCheckBox createConstantsForIntegers() {
        return addCheckBox("Active", infoUseConstantsForIntegers, false, e -> {
            settings.setUseConstantsForIntegers(useConstantsForIntegers.isSelected());
            maxField.setEnabled(useConstantsForIntegers.isSelected());
            minField.setEnabled(useConstantsForIntegers.isSelected());
        });
    }

    @Override
    public String getDescription() {
        return "SMT Translation (Old)";
    }

    @Override
    public JComponent getPanel(MainWindow window) {
        setSmtSettings(SettingsManager.getSmtPdSettings(window).clone());
        return this;
    }

    @Override
    public void applySettings(MainWindow window) {
        ProofDependentSMTSettings current = SettingsManager.getSmtPdSettings(window);
        current.copy(settings);// transfer settings
    }
}
