/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.profileloading;

import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.control.RadioButton;
import javafx.scene.control.Separator;
import javafx.scene.control.ToggleGroup;
import javafx.scene.control.Tooltip;
import javafx.scene.layout.VBox;

import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.wd.WdProfile;

/**
 * Additional UI components for the selection of the WD semantics, counter-part of
 * {@code de.uka.ilkd.key.gui.profileloading.WDLoadDialogOptionPanel} in the Swing module
 * {@code key.ui}.
 * <p>
 * The Swing original is a {@code KeYGuiExtension.LoadOptionPanel} that contributes a radio
 * group (L / Y / D, default L) with descriptive tooltips into the loading options accessory of
 * the Swing file chooser ({@code WDLoadDialogOptionPanel.java:34-118}); the selected operator
 * is reported as a {@link Configuration} entry {@code wdOperator = wdOperator:<L|Y|D>} and
 * feeds the well-definedness semantics of the loaded proof ({@code getResult}, {@code
 * WDLoadDialogOptionPanel.java:106-117}).
 * <p>
 * Port notes and deviations from the Swing original:
 * <ul>
 * <li>The Swing original is installed via the {@code KeYGuiExtension} SPI into
 * {@code KeYFileChooserLoadingOptions} whenever the user selects the WD profile in the profile
 * combo box ({@code KeYFileChooserLoadingOptions.java:88-99}, install/{@code
 * WDLoadDialogOptionPanel.java:85-94}). In this port the host is {@link
 * LoadingOptionsDialogF}, the FX counterpart of {@code KeYFileChooserLoadingOptions} shown
 * before the load: it registers this panel for the WD profile in its option-panel map (the
 * Swing SPI seam, plan §6/M6, stays open) and installs/removes it on profile changes.</li>
 * <li>MigLayout {@code install/deinstall} becomes a plain {@link Node} ({@link VBox}) with the
 * same content: bold header, separator, "Semantics:" label, mutually exclusive radio buttons.</li>
 * <li>The radio button texts and the three tooltip descriptions are carried over verbatim
 * ({@code WDLoadDialogOptionPanel.java:35-68}).</li>
 * </ul>
 */
public class WDLoadOptionPanelF extends VBox {

    /** Radio button for the L (McCarthy logic) semantics (Swing {@code rdbWDL}). */
    private final RadioButton rdbWDL = new RadioButton("L");

    /** Radio button for the Y (strong Kleene logic) semantics (Swing {@code rdbWDY}). */
    private final RadioButton rdbWDY = new RadioButton("Y");

    /** Radio button for the D (classical logic) semantics (Swing {@code rdbWDD}). */
    private final RadioButton rdbWDD = new RadioButton("D");

    /**
     * Tooltip text of the L semantics (Swing {@code DESCRIPTION_L_WD_SEMANTIC},
     * {@code WDLoadDialogOptionPanel.java:43-50}).
     */
    static final String DESCRIPTION_L_WD_SEMANTIC = """
            More intuitive for software developers and along the lines of
            runtime assertion semantics. Well-Definedness checks will be
            stricter using this operator, since the order of terms/formulas
            matters. It is based on McCarthy logic.
            Cf. "Are the Logical Foundations of Verifying Compiler
            Prototypes Matching User Expectations?" by Patrice Chalin.
            """;

    /**
     * Tooltip text of the D semantics (Swing {@code DESCRIPTION_D_WD_SEMANTIC},
     * {@code WDLoadDialogOptionPanel.java:52-58}).
     */
    static final String DESCRIPTION_D_WD_SEMANTIC = """
            Complete and along the lines of classical logic, where the
            order of terms/formulas is irrelevant. This operator is
            equivalent to the D-operator, but more efficient.
            Cf. "Efficient Well-Definedness Checking" by Ádám Darvas,
            Farhad Mehta, and Arsenii Rudich.
            """;

    /**
     * Tooltip text of the Y semantics (Swing {@code DESCRIPTION_Y_WD_SEMANTIC},
     * {@code WDLoadDialogOptionPanel.java:61-68}).
     */
    static final String DESCRIPTION_Y_WD_SEMANTIC = """
            Complete and along the lines of classical logic, where the
            order of terms/formulas is irrelevant. This operator is not as
            strict as the L-operator, based on strong Kleene logic. To be
            used with care, since formulas may blow up exponentially.
            Cf. "Well Defined B" by Patrick Behm, Lilian Burdy, and
            Jean-Marc Meynadier
            """;

    /** The profile this option panel belongs to (Swing {@code getProfile()}). */
    private final Profile profile = WdProfile.INSTANCE;

    public WDLoadOptionPanelF() {
        Label lblHeader = new Label("WD options");
        lblHeader.getStyleClass().add("dialog-section-title");
        Label lblSemantics = new Label("Semantics:");

        rdbWDL.setTooltip(new Tooltip(DESCRIPTION_L_WD_SEMANTIC));
        rdbWDD.setTooltip(new Tooltip(DESCRIPTION_D_WD_SEMANTIC));
        rdbWDY.setTooltip(new Tooltip(DESCRIPTION_Y_WD_SEMANTIC));

        ToggleGroup btnGrp = new ToggleGroup();
        btnGrp.getToggles().setAll(rdbWDD, rdbWDL, rdbWDY);

        // Swing default selection (WDLoadDialogOptionPanel.java:82)
        rdbWDL.setSelected(true);

        getStyleClass().add("wd-load-option-panel");
        setSpacing(4);
        getChildren().addAll(lblHeader, new Separator(), lblSemantics,
            new javafx.scene.layout.HBox(8, rdbWDD, rdbWDY, rdbWDL));
    }

    /**
     * The profile this option panel belongs to (Swing {@code LoadOptionPanel.getProfile()},
     * {@code WDLoadDialogOptionPanel.java:29-32}).
     *
     * @return the well-definedness profile
     */
    public Profile getProfile() {
        return profile;
    }

    /**
     * The additional profile options selected by the user (Swing
     * {@code OptionPanel.getResult()}, {@code WDLoadDialogOptionPanel.java:106-117}): the key
     * {@code wdOperator} with the value {@code wdOperator:L} (default), {@code wdOperator:D} or
     * {@code wdOperator:Y}.
     *
     * @return the configuration for the proof load
     */
    public Configuration getResult() {
        Configuration configuration = new Configuration();
        configuration.set("wdOperator", "wdOperator:L");
        if (rdbWDD.isSelected()) {
            configuration.set("wdOperator", "wdOperator:D");
        }
        if (rdbWDY.isSelected()) {
            configuration.set("wdOperator", "wdOperator:Y");
        }
        return configuration;
    }

    /**
     * Self test of the panel (system property {@code key.fx.verify.profileloading}), run at
     * startup from {@code MainWindowF}: the WD profile association, the default selection and
     * every {@link #getResult()} mapping are checked.
     *
     * @return a self-test report ending in {@code PASS} or {@code FAIL}
     */
    public static String verifyProfileLoading() {
        StringBuilder report = new StringBuilder();
        try {
            WDLoadOptionPanelF panel = new WDLoadOptionPanelF();

            // the panel is registered for the WD profile (Swing LoadOptionPanel.getProfile)
            report.append("profile=").append(panel.getProfile() == WdProfile.INSTANCE).append("; ");

            // default selection L (WDLoadDialogOptionPanel.java:82)
            check(report, "default", "wdOperator:L",
                String.valueOf(panel.getResult().get("wdOperator")));

            // select D and Y in turn (Swing getResult mapping,
            // WDLoadDialogOptionPanel.java:106-117)
            panel.rdbWDD.setSelected(true);
            check(report, "select D", "wdOperator:D",
                String.valueOf(panel.getResult().get("wdOperator")));
            panel.rdbWDY.setSelected(true);
            check(report, "select Y", "wdOperator:Y",
                String.valueOf(panel.getResult().get("wdOperator")));
            panel.rdbWDL.setSelected(true);
            check(report, "select L", "wdOperator:L",
                String.valueOf(panel.getResult().get("wdOperator")));

            // the three tooltips are set
            boolean tooltips = panel.rdbWDL.getTooltip() != null
                    && panel.rdbWDD.getTooltip() != null && panel.rdbWDY.getTooltip() != null;
            check(report, "tooltips", "true", String.valueOf(tooltips));
        } catch (RuntimeException e) {
            report.append("exception ").append(e).append("; ");
        }
        report.append(report.toString().contains("FAIL")
                || report.toString().contains("exception") ? "FAIL" : "PASS");
        return report.toString();
    }

    private static void check(StringBuilder report, String what, String expected,
            String actual) {
        boolean ok = java.util.Objects.equals(expected, actual);
        report.append(what).append("=").append(ok ? "ok"
                : "FAIL(expected <" + expected + "> got <" + actual + ">").append("); ");
    }
}
