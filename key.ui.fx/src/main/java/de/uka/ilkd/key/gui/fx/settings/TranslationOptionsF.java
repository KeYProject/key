/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.settings;

import javafx.scene.control.CheckBox;
import javafx.scene.control.Spinner;

import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.settings.ProofDependentSMTSettings;

/**
 * The translation semantics options of the old SMT translation mechanism, FX port of
 * {@code TranslationOptions} (Swing {@code gui/smt/settings/TranslationOptions.java}; shown only
 * while the {@code SMT_TRANS_OPTIONS} feature flag is active). The panel edits a copy of the
 * proof-dependent SMT settings and transfers it back on apply (TranslationOptions.java:173-183).
 */
final class TranslationOptionsF extends SettingsPanelF implements SettingsProviderF {

    private static final String INFO_USE_EXPLICIT_TYPE_HIERARCHY =
        """
                If this option is selected, the transitive inheritance between classes is modeled by assumptions.

                Example: Let A, B and C  be classes such that C extends B and B extends A.
                If the option is not selected, the following assumptions are added:
                \\forall x; (type_of_C(x)->type_of_B(x))
                \\forall x; (type_of_B(x)->type_of_A(x))
                If the option is selected, the following assumption is additionally added to the assumptions above:
                \\forall x; (type_of_C(x)->type_of_A(x))
                """;

    private static final String INFO_USE_NULL_INSTANTIATION =
        """
                At the moment this option has only effect on hierarchy assumptions regarding the null object.
                Example: Let A and B be classes.
                If the option is not selected, the type null is treated as a normal class. Consequently, the following assumptions are added:
                \\forall x; (type_of_Null(x)->type_of_A(x))
                \\forall x; (type_of_Null(x)->type_of_B(x))
                If the option is selected, those assumptions are instantiated with a concrete null object:
                type_of_A(null)
                type_of_B(null)""";

    private static final String INFO_USE_BUILT_IN_UNIQUENESS =
        "Some solvers support the uniqueness of functions by built-in mechanisms. If this option "
            + "is selected those mechanisms are used, otherwise some assumptions are added by "
            + "using normal FOL.\n"
            + "Note: The uniqueness of functions is needed for translating attributes and arrays.";

    private static final String INFO_USE_UI_MULTIPLICATION =
        """
                Some solvers support only simple multiplications. For example Yices supports only multiplications of type a*b where a or b must be a number.
                In order to support more complex multiplications, this option can be activated: If the solver does not support a certain kind of multiplication, the occurence of this multiplication is translated into the uninterpreted function mult. Furthermore some typical assumptions are added:
                \\forall x; mult(x,0)=0
                \\forall x; mult(0,x)=0
                \\forall x; mult(x,1)=x
                \\forall x; mult(1,x)=x
                \\forall x; \\forall y; mult(x,y)=mult(y,x)
                \\forall x; \\forall y; \\forall z; mult(mult(x,y),z)=mult(x,mult(y,z))
                \\forall x; \\forall y; mult(x,y)=0 -> (x=0|y=0)
                \\forall x; \\forall y; mult(x,y)=1 -> (x=1&y=1)
                Note:
                1. If this option is not selected, an exception is thrown in the case that a unsupported multiplication occurs.
                2. The translation makes the uninterpreted function mult unique, so that there cannot be any clashes with functions that are introduced by the user.""";

    private static final String INFO_USE_CONSTANTS_FOR_INTEGERS =
        """
                Some solvers support only a certain interval of integers (e.g. Simplify). If this option is activated, numbers that are not supported by the used solver are translated into uninterpreted constants. Furthermore  an asumption is added that states that the introduced constant is greater than the maximum of the supported numbers.

                Example: Assume that a solver supports numbers less or equal 10:
                The number 11 is translated into the constant c_11 and the assumption c_11>10 is introduced.

                Note: If this option is not selected, an exception is thrown in the case that a not supported number occurs.
                """;

    private final CheckBox useExplicitTypeHierarchy;
    private final CheckBox useNullInstantiation;
    private final CheckBox useBuiltInUniqueness;
    private final CheckBox useUIMultiplication;
    private final CheckBox useConstantsForIntegers;
    private final Spinner<Integer> minField;
    private final Spinner<Integer> maxField;

    TranslationOptionsF() {
        setHeaderText(getDescription());
        useExplicitTypeHierarchy = addCheckBox("Use an explicit type hierarchy.",
            INFO_USE_EXPLICIT_TYPE_HIERARCHY, false);
        useNullInstantiation =
            addCheckBox("Instantiate hierarchy assumptions if possible (recommended).",
                INFO_USE_NULL_INSTANTIATION, false);
        useBuiltInUniqueness = addCheckBox("Use built-in mechanism for uniqueness if possible.",
            INFO_USE_BUILT_IN_UNIQUENESS, false);
        useUIMultiplication = addCheckBox("Use uninterpreted multiplication if necessary.",
            INFO_USE_UI_MULTIPLICATION, false);
        addSeparator("Use constants for too big or too small integers.");
        useConstantsForIntegers = addCheckBox("Active", INFO_USE_CONSTANTS_FOR_INTEGERS, false);
        minField = addIntNumberField("Minimum", Integer.MIN_VALUE, Integer.MAX_VALUE, 1,
            Integer.MIN_VALUE, "", null);
        maxField = addIntNumberField("Maximum", Integer.MIN_VALUE, Integer.MAX_VALUE, 1,
            Integer.MAX_VALUE, "", null);
        // the integer bounds only matter while the constants option is active (Swing
        // createConstantsForIntegers, TranslationOptions.java:159-165)
        minField.disableProperty().bind(useConstantsForIntegers.selectedProperty().not());
        maxField.disableProperty().bind(useConstantsForIntegers.selectedProperty().not());
    }

    @Override
    public String getDescription() {
        return "SMT Translation (Old)";
    }

    @Override
    public javafx.scene.Node getPanel(MainWindowF window) {
        // Swing TranslationOptions.getPanel → setSmtSettings on a clone
        // (TranslationOptions.java:94-107 + 173-176)
        ProofDependentSMTSettings settings = SettingsManagerF.getSmtPdSettings(window).clone();
        useExplicitTypeHierarchy.setSelected(settings.isUseExplicitTypeHierarchy());
        useNullInstantiation.setSelected(settings.isUseNullInstantiation());
        useBuiltInUniqueness.setSelected(settings.isUseBuiltInUniqueness());
        useUIMultiplication.setSelected(settings.isUseUIMultiplication());
        useConstantsForIntegers.setSelected(settings.isUseConstantsForIntegers());
        minField.getValueFactory()
                .setValue((int) Math.max(Integer.MIN_VALUE,
                    Math.min(Integer.MAX_VALUE, settings.getMinInteger())));
        maxField.getValueFactory()
                .setValue((int) Math.max(Integer.MIN_VALUE,
                    Math.min(Integer.MAX_VALUE, settings.getMaxInteger())));
        return this;
    }

    @Override
    public void apply(MainWindowF window) {
        // the Swing original applies the checkbox changes live to its clone and transfers the
        // whole clone back with copy (TranslationOptions.java:110-165 + 178-183); the FX panel
        // collects all values here
        ProofDependentSMTSettings settings = SettingsManagerF.getSmtPdSettings(window).clone();
        settings.setUseExplicitTypeHierarchy(useExplicitTypeHierarchy.isSelected());
        settings.setUseNullInstantiation(useNullInstantiation.isSelected());
        settings.setUseBuiltInUniqueness(useBuiltInUniqueness.isSelected());
        settings.setUseUIMultiplication(useUIMultiplication.isSelected());
        settings.setUseConstantsForIntegers(useConstantsForIntegers.isSelected());
        settings.setMinInteger(minField.getValue());
        settings.setMaxInteger(maxField.getValue());
        SettingsManagerF.getSmtPdSettings(window).copy(settings);
    }
}
