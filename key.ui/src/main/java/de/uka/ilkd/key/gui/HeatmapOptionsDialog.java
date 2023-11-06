/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;
import java.awt.event.WindowEvent;
import java.awt.event.WindowFocusListener;
import java.util.Objects;
import javax.swing.*;
import javax.swing.border.EmptyBorder;
import javax.swing.text.NumberFormatter;

import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.utilities.GuiUtilities;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;


/**
 * This Dialog contains options for highlighting sequent formulae or terms according to their age,
 * i.e., when they were first introduced into the proof. It is possible to highlight all sf/terms up
 * to a specified age, or to highlight the x newest sf/terms, x being specified by the user.
 *
 * @author jschiffl
 *
 */

public class HeatmapOptionsDialog extends JDialog {

    /**
     * Version ID.
     */
    private static final long serialVersionUID = 5731407140427140088L;

    /** The view settings */
    private static final ViewSettings VS =
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();

    /** Minimal setting for number of highlighted terms */
    private static final int MIN_AGE = 1;

    /** Maximal setting for number of highlighted terms */
    private static final int MAX_AGE = 1000;

    /** Text for introductory heatmap explanation */
    private static final String INTRO_LABEL =
        "Heatmaps can be used to " + "highlight the most recent changes in the sequent.";

    /** Explanation for age textfield */
    private static final String TEXTFIELD_LABEL =
        "Maximum age of highlighted " + "terms or formulae, or number of newest terms or formulae";

    /** Tool tip for age textfield */
    private static final String TOOLTIP_TEXT =
        "Please enter a number between " + MIN_AGE + " and " + MAX_AGE + ".";

    /** Button command names */
    private static final String[] COMMANDS =
        { "default", "sf_age", "sf_newest", "terms_age", "terms_newest" };

    /** Button names */
    private static final String[] BUTTON_NAMES = { "No heatmaps", "Sequent formulae up to age",
        "Newest sequent formulae", "Terms up to age", "Newest terms" };

    /** Descriptions for heatmap options */
    private static final String[] DESCRIPTIONS = { "No Heatmaps are shown.",
        "All sequent formulae that have been added or changed in the last k steps are highlighted. "
            + "More recent formulae will have a stronger highlight. It is possible that less "
            + "than k formulae are highlighted, e.g. if one formula has changed multiple times.",
        "All formulae in the sequent are sorted by how new they are, i.e., how recently they have"
            + " been added or changed. The first k formulae of the sorted list are highlighted "
            + "according to their position in the list,"
            + " with the most recent formula receiving the strongest highlight.",
        "All terms that have been added or changed in the last k steps are highlighted. "
            + "More recent terms will have a stronger highlight. It is possible that less than "
            + "k terms are highlighted, e.g. if one term has changed multiple times.",
        "All terms in the sequent are sorted by how new they are, i.e., how recently they "
            + "have been added or changed. The first k terms of the sorted list are highlighted "
            + "according to their position in the list,"
            + " with the most recent term receiving the strongest highlight." };

    /** Error message on invalid textfield input */ // Not needed atm
    // private static final String INPUT_ERROR_MESSAGE = "Please enter a number bwetween 1 and
    // 1000";

    /** number of radioButtons in the group */
    private static final int NUMRADIOBUTTONS = 5;

    /** question mark icon */
    private static final Icon HELPICON = IconFactory.HELP.get(20);

    /**
     * Opens a dialog for choosing if and how to display heatmap highlighting.
     */
    public HeatmapOptionsDialog() {
        super(MainWindow.getInstance(), "Heatmap Options", true);

        JPanel panel = new JPanel();
        panel.setLayout(new GridBagLayout());
        GridBagConstraints c = new GridBagConstraints();
        c.insets = new Insets(10, 5, 10, 5);

        JRadioButton[] radioButtons = new JRadioButton[NUMRADIOBUTTONS];

        final ButtonGroup group = new ButtonGroup();
        JButton okButton = new JButton("OK");
        JButton cancelButton = new JButton("Cancel");
        GuiUtilities.attachClickOnEscListener(cancelButton);

        // set up spinner for age value

        JSpinner valueSpinner = setupSpinner();



        for (int i = 0; i < NUMRADIOBUTTONS; i++) {
            radioButtons[i] = new JRadioButton(BUTTON_NAMES[i]);
            radioButtons[i].setActionCommand(COMMANDS[i]);
            group.add(radioButtons[i]);
        }

        // Display the current settings
        loadSettings(radioButtons);

        // save current settings in case the user escapes
        boolean isShow = VS.isShowHeatmap();
        boolean isSF = VS.isHeatmapSF();
        boolean isNew = VS.isHeatmapNewest();
        int age = VS.getMaxAgeForHeatmap();
        cancelButton.addActionListener(e -> {
            VS.setHeatmapOptions(isShow, isSF, isNew, age);
            dispose();
        });

        getRootPane().registerKeyboardAction(e -> dispose(),
            KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0), JComponent.WHEN_IN_FOCUSED_WINDOW);

        JPanel radioBoxes = setupRadioPanel(radioButtons, panel.getBackground(), this);
        JPanel spPanel = setupSpinnerPanel(valueSpinner, panel.getBackground());
        JPanel buttonPanel = setupButtonPanel(okButton, cancelButton);

        c.gridy = 0;
        JTextArea l = new JTextArea(INTRO_LABEL, 5, 20);
        l.setLineWrap(true);
        l.setWrapStyleWord(true);
        l.setEditable(false);
        l.setBackground(panel.getBackground());
        panel.add(l, c);
        c.gridy++;
        panel.add(radioBoxes, c);
        c.gridy++;
        panel.add(spPanel, c);
        c.gridy++;
        panel.add(buttonPanel, c);

        add(panel);
        getRootPane().setDefaultButton(okButton);

        // action for okButton
        Action action = setupOkAction(panel, group, valueSpinner);
        okButton.addActionListener(action);

        pack();
        setAlwaysOnTop(true);
        setResizable(false);
        setLocationRelativeTo(MainWindow.getInstance());
    }

    /**
     * @param radioButtons the radio buttons to set
     */
    private void loadSettings(JRadioButton[] radioButtons) {
        if (VS.isShowHeatmap()) {
            if (VS.isHeatmapSF()) {
                if (VS.isHeatmapNewest()) {
                    radioButtons[2].setSelected(true);
                } else {
                    radioButtons[1].setSelected(true);
                }
            } else {
                if (VS.isHeatmapNewest()) {
                    radioButtons[4].setSelected(true);
                } else {
                    radioButtons[3].setSelected(true);
                }
            }
        } else {
            radioButtons[0].setSelected(true);
        }
    }

    /**
     * @return a jSpinner with the correct input constraints
     */
    private JSpinner setupSpinner() {
        JSpinner valueSpinner = new JSpinner(new SpinnerNumberModel(5, MIN_AGE, MAX_AGE, 1));
        valueSpinner.setValue(VS.getMaxAgeForHeatmap());
        valueSpinner.addChangeListener(
            e -> VS.setHeatmapOptions(VS.isShowHeatmap(), VS.isHeatmapSF(), VS.isHeatmapNewest(),
                (int) valueSpinner.getValue()));
        JFormattedTextField txt = ((JSpinner.NumberEditor) valueSpinner.getEditor()).getTextField();
        NumberFormatter nf = (NumberFormatter) txt.getFormatter();
        nf.setAllowsInvalid(false);
        nf.setValueClass(Integer.class);
        nf.setMinimum(MIN_AGE);
        nf.setMaximum(MAX_AGE);
        nf.setCommitsOnValidEdit(true);
        valueSpinner.setToolTipText(TOOLTIP_TEXT);
        return valueSpinner;
    }

    /**
     * @param okButton the ok button on the panel
     * @param cancelButton the cancel button on the panel
     * @return a panel with ok and cancel button
     */
    private JPanel setupButtonPanel(JButton okButton, JButton cancelButton) {
        JPanel buttonPanel = new JPanel();
        buttonPanel.setLayout(new BoxLayout(buttonPanel, BoxLayout.X_AXIS));
        buttonPanel.add(okButton);
        buttonPanel.add(new JLabel("                   "));
        buttonPanel.add(cancelButton);
        return buttonPanel;
    }

    /**
     * @param spinner the spinner shown on the panel
     * @return a panel with spinner and explanation
     */
    private JPanel setupSpinnerPanel(JSpinner spinner, Color bg) {
        JPanel tfPanel = new JPanel();
        tfPanel.setLayout(new BorderLayout());
        JTextArea l = new JTextArea(TEXTFIELD_LABEL, 2, 20);
        l.setLineWrap(true);
        l.setWrapStyleWord(true);
        l.setEditable(false);
        l.setBackground(bg);
        tfPanel.add(l, BorderLayout.NORTH);
        JPanel tmp = new JPanel();
        tmp.add(new JLabel("k = "));
        tmp.add(spinner);
        tfPanel.add(tmp, BorderLayout.CENTER);
        tfPanel.setBorder(BorderFactory.createBevelBorder(0));
        return tfPanel;
    }

    /**
     * @param radioButtons the radio buttons shown on the panel
     * @param bg the background color
     * @return a panel with all the radio buttons and explanations
     */
    private JPanel setupRadioPanel(JRadioButton[] radioButtons, Color bg, JDialog parent) {
        JPanel radioBoxes = new JPanel();
        radioBoxes.setLayout(new BoxLayout(radioBoxes, BoxLayout.Y_AXIS));
        for (int i = 0; i < NUMRADIOBUTTONS; i++) {
            JPanel p = new JPanel();
            p.setLayout(new BorderLayout());
            JLabel dis = new JLabel("Disable heatmaps");
            dis.setAlignmentX(.5f);
            JLabel sf = new JLabel("Highlight sequent formulae");
            sf.setAlignmentX(.5f);
            JLabel terms = new JLabel("Highlight terms");
            terms.setAlignmentX(.5f);
            if (i == 0) {
                radioBoxes.add(dis);
            }
            if (i == 1) {
                radioBoxes.add(new JLabel("                   "));
                radioBoxes.add(sf);
            }
            if (i == 3) {
                radioBoxes.add(new JLabel("                   "));
                radioBoxes.add(terms);
            }
            p.add(radioButtons[i], BorderLayout.WEST);
            int j = i;
            JButton infoButton = new JButton(new AbstractAction() {

                /**
                 * version id
                 */
                private static final long serialVersionUID = 6910725367740582043L;

                @Override
                public void actionPerformed(ActionEvent e) {
                    new InfoDialog(BUTTON_NAMES[j], DESCRIPTIONS[j], parent);
                }
            });
            infoButton.setIcon(HELPICON);
            p.add(infoButton, BorderLayout.EAST);
            p.setBorder(BorderFactory.createBevelBorder(0));
            radioBoxes.add(p);
        }
        return radioBoxes;
    }

    /**
     * Sets up the action that is called on pressing the ok button
     *
     * @param panel the main panel
     * @param group the radio button group
     * @param spinner the age spinner
     * @return
     */
    private Action setupOkAction(JPanel panel, final ButtonGroup group, JSpinner spinner) {
        Action action = new AbstractAction() {

            private static final long serialVersionUID = -5840137383763071948L;

            @Override
            public void actionPerformed(ActionEvent e) {
                String command = group.getSelection().getActionCommand();
                boolean showHm = VS.isShowHeatmap();
                boolean sf = VS.isHeatmapSF();
                boolean newest = VS.isHeatmapNewest();
                int ma = VS.getMaxAgeForHeatmap();
                if (Objects.equals(command, COMMANDS[0])) {
                    VS.setHeatmapOptions(false, sf, newest, ma);
                    dispose();
                    return;
                } else if (Objects.equals(command, COMMANDS[1])) {
                    showHm = true;
                    sf = true;
                    newest = false;
                } else if (Objects.equals(command, COMMANDS[2])) {
                    showHm = true;
                    sf = true;
                    newest = true;
                } else if (Objects.equals(command, COMMANDS[3])) {
                    showHm = true;
                    sf = false;
                    newest = false;
                } else if (Objects.equals(command, COMMANDS[4])) {
                    showHm = true;
                    sf = false;
                    newest = true;
                }
                if (spinner.getValue() != null) {
                    VS.setHeatmapOptions(showHm, sf, newest, (int) spinner.getValue());
                    dispose();
                }
            }
        };
        return action;
    }

    /**
     *
     * @author jschiffl a small dialog that explains an option in more detail
     */
    static class InfoDialog extends JDialog {

        /** serial version id */
        private static final long serialVersionUID = 479715116105454400L;

        /**
         *
         * @param s the description
         * @param title title of the dialog
         * @param owner the parent window
         */
        public InfoDialog(String title, String s, final JDialog owner) {
            super(owner);
            this.setTitle(title);
            JPanel p = new JPanel(new BorderLayout());
            JTextArea l = new JTextArea(s, 8, 20);
            l.setBorder(new EmptyBorder(3, 10, 3, 10));
            l.setLineWrap(true);
            l.setWrapStyleWord(true);
            l.setEditable(false);
            l.setBackground(owner.getBackground());
            p.add(l, BorderLayout.NORTH);
            this.setContentPane(p);
            this.pack();
            this.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
            this.setLocationRelativeTo(owner);
            this.setAlwaysOnTop(true);
            this.setVisible(true);

            // exit on click elsewhere
            this.addWindowFocusListener(new WindowFocusListener() {
                @Override
                public void windowGainedFocus(WindowEvent e) {
                    // do nothing
                }

                @Override
                public void windowLostFocus(WindowEvent e) {
                    InfoDialog.this.dispose();
                }
            });

            // exit on escape button
            getRootPane().registerKeyboardAction(e -> dispose(),
                KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0), JComponent.WHEN_IN_FOCUSED_WINDOW);
        }
    }
}
