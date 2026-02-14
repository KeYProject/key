package de.uka.ilkd.key.gui.profileloading;

import de.uka.ilkd.key.gui.KeYFileChooserLoadingOptions;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.wd.WdProfile;
import net.miginfocom.layout.CC;

import javax.swing.*;
import java.awt.*;

/// Additional UI components for the selection of the WD semantics.
/// @author weigl
@KeYGuiExtension.Info(experimental = false)
public class WDLoadDialogOptionPanel implements KeYGuiExtension, KeYGuiExtension.LoadOptionPanel {
    @Override
    public OptionPanel get() {
        return new WDLoadDialogOptionPanelImpl();
    }

    @Override
    public Profile getProfile() {
        return WdProfile.INSTANCE;
    }

    public static class WDLoadDialogOptionPanelImpl implements OptionPanel {
        private final JRadioButton rdbWDL = new JRadioButton("L");
        private final JRadioButton rdbWDY = new JRadioButton("Y");
        private final JRadioButton rdbWDD = new JRadioButton("D");

        private final JLabel lblHeader = new JLabel("WD options");
        private final JLabel lblSemantics = new JLabel("Semantics:");
        private final JSeparator sepHeader = new JSeparator();

        private static final String DESCRIPTION_L_WD_SEMANTIC = """
                More intuitive for software developers and along the lines of
                runtime assertion semantics. Well-Definedness checks will be
                stricter using this operator, since the order of terms/formulas
                matters. It is based on McCarthy logic.
                Cf. "Are the Logical Foundations of Verifying Compiler
                Prototypes Matching User Expectations?" by Patrice Chalin.
                """;

        private static final String DESCRIPTION_D_WD_SEMANTIC = """
                Complete and along the lines of classical logic, where the
                order of terms/formulas is irrelevant. This operator is
                equivalent to the D-operator, but more efficient.
                Cf. "Efficient Well-Definedness Checking" by Ádám Darvas,
                Farhad Mehta, and Arsenii Rudich.
                """;


        private static final String DESCRIPTION_Y_WD_SEMANTIC = """
                Complete and along the lines of classical logic, where the
                order of terms/formulas is irrelevant. This operator is not as
                strict as the L-operator, based on strong Kleene logic. To be
                used with care, since formulas may blow up exponentially.
                Cf. "Well Defined B" by Patrick Behm, Lilian Burdy, and
                Jean-Marc Meynadier
                """;

        public WDLoadDialogOptionPanelImpl() {
            lblHeader.setFont(lblHeader.getFont().deriveFont(Font.BOLD));

            rdbWDL.setToolTipText(DESCRIPTION_L_WD_SEMANTIC);
            rdbWDD.setToolTipText(DESCRIPTION_D_WD_SEMANTIC);
            rdbWDY.setToolTipText(DESCRIPTION_Y_WD_SEMANTIC);

            ButtonGroup btnGrp = new ButtonGroup();
            btnGrp.add(rdbWDD);
            btnGrp.add(rdbWDL);
            btnGrp.add(rdbWDY);

            rdbWDL.setSelected(true);
        }

        @Override
        public void install(KeYFileChooserLoadingOptions panel) {
            panel.add(lblHeader);
            panel.add(sepHeader, new CC().wrap().span(2).growX());

            panel.add(lblSemantics);
            panel.add(rdbWDD, new CC().span(2).split(3));
            panel.add(rdbWDY);
            panel.add(rdbWDL);
        }

        @Override
        public void deinstall(KeYFileChooserLoadingOptions panel) {
            panel.remove(lblHeader);
            panel.remove(sepHeader);
            panel.remove(lblSemantics);
            panel.remove(rdbWDL);
            panel.remove(rdbWDD);
            panel.remove(rdbWDY);
        }

        @Override
        public Object getResult() {
            if (rdbWDD.isSelected()) {
                return "wdOperator:D";
            }
            if (rdbWDY.isSelected()) {
                return "wdOperator:Y";
            }
            // default
            return "wdOperator:L";
        }
    }
}
