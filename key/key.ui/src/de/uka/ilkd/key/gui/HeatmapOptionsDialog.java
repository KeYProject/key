// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.Frame;
import java.awt.Graphics;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.WindowEvent;
import java.awt.event.WindowFocusListener;
import java.awt.image.BufferedImage;
import java.io.File;
import java.io.IOException;
import java.nio.file.Paths;
import java.text.NumberFormat;

import javax.imageio.ImageIO;
import javax.swing.AbstractAction;
import javax.swing.Action;
import javax.swing.BorderFactory;
import javax.swing.BoxLayout;
import javax.swing.ButtonGroup;
import javax.swing.Icon;
import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JFormattedTextField;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JRadioButton;
import javax.swing.JTextArea;
import javax.swing.SwingUtilities;
import javax.swing.WindowConstants;
import javax.swing.text.NumberFormatter;

import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;


/**
 * This Dialog contains options for highlighting sequent formulas
 * or terms according to their age, i.e., when they were first introduced
 * into the proof. It is possible to highlight all sf/terms up to a
 * specified age, or to highlight the x newest sf/terms, x being
 * specified by the user.
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
    private static final ViewSettings VS = ProofIndependentSettings.DEFAULT_INSTANCE
            .getViewSettings();

    /** Minimal setting for number of highlighted terms */
    private static final int MIN_AGE = 1;

    /** Maximal setting for number of highlighted terms */
    private static final int MAX_AGE = 1000;

    /** Text for introductory heatmap explanation */
    private static final String INTRO_LABEL = "Heatmaps can be used to "
            + "highlight the most recent changes in the sequent. You can choose to highlight "
            + "entire sequent formulas or subterms. Highlighting can either "
            + "be done on the newest expressions, or on all expressions "
            + "that have changed whithin the last k steps of the proof. "
            + "Newer expressions will have a stronger highlight.";

    /** Explanation for age textfield */
    private static final String TEXTFIELD_LABEL = "Maximum age of highlighted "
            + "terms or formulas, or number of newest terms or formulas";

    /** Tool tip for age textfield */
    private static final String TOOLTIP_TEXT = "Please enter a number between " + MIN_AGE + " and "
            + MAX_AGE + ".";

    /** Button command names */
    private static final String[] COMMANDS = { "default", "sf_age", "sf_newest", "terms_age",
        "terms_newest" };

    /** Button names */
    private static final String[] BUTTON_NAMES = { "No Heatmaps", "Sequent formulas up to age",
        "Newest sequent formulas", "Terms up to age", "Newest terms" };

    /** Descriptions for heatmap options */
    private static final String[] DESCRIPTIONS = { "No Heatmaps are shown.",
        "All sequent formulas that have changed in the last k steps are highlighted.",
        "The k newest sequent formulas are highlighted.",
        "All terms that have changed in the last k steps are highlighted.",
        "The k newest terms are highlighted." };

    /** Error message on invalid textfield input */
    private static final String INPUT_ERROR_MESSAGE = "Please enter a number bwetween 1 and 1000";

    /** number of radioButtons in the group */
    private static final int NUMRADIOBUTTONS = 5;

    protected static final String[] INFO_IMG = null;

    private static final Icon HELPICON = IconFactory
            .scaleIcon(IconFactory.getImage("images/questionIcon.png"), 20, 20);
    /**
     * Opens a dialog for choosing if and how to display heatmap highlighting.
     */
    public HeatmapOptionsDialog() {
        System.out.println(Paths.get("").toAbsolutePath().toString());
        setTitle("Heatmap Options");

        JPanel panel = new JPanel();
        panel.setLayout(new GridBagLayout());
        GridBagConstraints c = new GridBagConstraints();
        c.insets = new Insets(10, 5, 10, 5);

        JRadioButton[] radioButtons = new JRadioButton[NUMRADIOBUTTONS];

        final ButtonGroup group = new ButtonGroup();
        JButton okButton = new JButton("OK");
        JButton cancelButton = new JButton("Cancel");

        // set up age textfield
        JFormattedTextField textField = setupTextfield();

        for (int i = 0; i < NUMRADIOBUTTONS; i++) {
            radioButtons[i] = new JRadioButton(BUTTON_NAMES[i]);
            radioButtons[i].setActionCommand(COMMANDS[i]);
            group.add(radioButtons[i]);
        }

        // Display the current settings
        loadSettings(radioButtons);

        cancelButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                dispose();
            }
        });

        JPanel radioBoxes = setupRadioPanel(radioButtons, panel.getBackground(), this);
        JPanel tfPanel = setupTextfieldPanel(textField, panel.getBackground());
        JPanel buttonPanel = setupButtonPanel(okButton, cancelButton);

        c.gridy = 0;
        JTextArea l = new JTextArea(INTRO_LABEL, 5, 36);
        l.setLineWrap(true);
        l.setWrapStyleWord(true);
        l.setEditable(false);
        l.setBackground(panel.getBackground());
        panel.add(l, c);
        c.gridy++;
        panel.add(radioBoxes, c);
        c.gridy++;
        panel.add(tfPanel, c);
        c.gridy++;
        panel.add(buttonPanel, c);

        add(panel);
        getRootPane().setDefaultButton(okButton);

        // action for okButton and textfield
        Action action = setupOkAction(panel, group, textField);

        okButton.addActionListener(action);
        textField.addActionListener(action);

        pack();
        System.out.println(l.size());
        setLocationRelativeTo(null);
        setVisible(true);
        setResizable(false);
    }

    /**
     * @param radioButtons
     *            the radio buttons to set
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
     * @return a textfield with the correct input constraints
     */
    private JFormattedTextField setupTextfield() {
        NumberFormat format = NumberFormat.getInstance();
        NumberFormatter formatter = new NumberFormatter(format);
        formatter.setValueClass(Integer.class);
        formatter.setMinimum(MIN_AGE);
        formatter.setMaximum(MAX_AGE);
        formatter.setAllowsInvalid(true);
        JFormattedTextField textField = new JFormattedTextField(formatter);
        textField.setPreferredSize(new Dimension(40, 20));
        textField.setMaximumSize(textField.getPreferredSize());
        textField.setFocusLostBehavior(JFormattedTextField.COMMIT);
        textField.setValue(VS.getMaxAgeForHeatmap());
        textField.setToolTipText(TOOLTIP_TEXT);
        return textField;
    }

    /**
     * @param okButton
     *            the ok button on the panel
     * @param cancelButton
     *            the cancel button on the panel
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
     * @param textField
     *            the textfield shown on the panel
     * @return a panel with textfield and explanation
     */
    private JPanel setupTextfieldPanel(JFormattedTextField textField, Color bg) {
        JPanel tfPanel = new JPanel();
        tfPanel.setLayout(new BorderLayout());
        JTextArea l = new JTextArea(TEXTFIELD_LABEL);
        l.setLineWrap(true);
        l.setWrapStyleWord(true);
        l.setEditable(false);
        l.setBackground(bg);
        tfPanel.add(l, BorderLayout.NORTH);
        JPanel tmp = new JPanel();
        tmp.add(new JLabel("k = "));
        tmp.add(textField);
        tfPanel.add(tmp, BorderLayout.CENTER);
        tfPanel.setBorder(BorderFactory.createBevelBorder(0));
        return tfPanel;
    }

    /**
     * @param radioButtons
     *            the radio buttons shown on the panel
     * @param bg
     *            the backgropund color
     * @return a panel with all the radio buttons and explanations
     */
    private JPanel setupRadioPanel(JRadioButton[] radioButtons, Color bg, JDialog parent) {
        JPanel radioBoxes = new JPanel();
        radioBoxes.setLayout(new BoxLayout(radioBoxes, BoxLayout.Y_AXIS));
        for (int i = 0; i < NUMRADIOBUTTONS; i++) {
            JPanel p = new JPanel();
            p.setLayout(new BorderLayout());
            p.add(radioButtons[i], BorderLayout.WEST);
            int j = i;
            JButton infoButton = new JButton(new AbstractAction() {

                @Override
                public void actionPerformed(ActionEvent e) {
                    InfoDialog id = new InfoDialog(DESCRIPTIONS[j], INFO_IMG[j], parent);
                }
            });
            infoButton.setIcon(HELPICON);
            p.add(infoButton, BorderLayout.EAST);
            JTextArea l = new JTextArea(DESCRIPTIONS[i]);
            l.setEditable(false);
            l.setBackground(bg);
            p.add(l);
            p.setBorder(BorderFactory.createBevelBorder(0));
            radioBoxes.add(p);
        }
        return radioBoxes;
    }

    /**
     * Sets up the action that is called on pressing the ok button
     *
     * @param panel
     *            the main panel
     * @param group
     *            the radio button group
     * @param textField
     *            the age textfield
     * @return
     */
    private Action setupOkAction(JPanel panel, final ButtonGroup group,
            JFormattedTextField textField) {
        Action action = new AbstractAction() {

            private static final long serialVersionUID = -5840137383763071948L;

            @Override
            public void actionPerformed(ActionEvent e) {
                String command = group.getSelection().getActionCommand();
                boolean showHm = VS.isShowHeatmap();
                boolean SF = VS.isHeatmapSF();
                boolean newest = VS.isHeatmapNewest();
                int ma = VS.getMaxAgeForHeatmap();
                if (command == COMMANDS[0]) {
                    VS.setHeatmapOptions(false, SF, newest, ma);
                    dispose();
                    return;
                } else if (command == COMMANDS[1]) {
                    showHm = true;
                    SF = true;
                    newest = false;
                } else if (command == COMMANDS[2]) {
                    showHm = true;
                    SF = true;
                    newest = true;
                } else if (command == COMMANDS[3]) {
                    showHm = true;
                    SF = false;
                    newest = false;
                } else if (command == COMMANDS[4]) {
                    showHm = true;
                    SF = false;
                    newest = true;
                }
                if (textField.getValue() != null) {
                    if (textField.isEditValid()) {
                        VS.setHeatmapOptions(showHm, SF, newest, (int) textField.getValue());
                        dispose();
                    } else {
                        if (VS.isShowHeatmap()) {
                            JOptionPane.showMessageDialog(panel,
                                    INPUT_ERROR_MESSAGE,
                                    "Invalid Input",
                                    JOptionPane.ERROR_MESSAGE);
                        } else {
                            dispose();
                        }
                    }
                }
            }
        };
        return action;
    }

    class InfoDialog extends JDialog {
        public InfoDialog(String s, String imgPath, final JDialog owner) {
            super(owner);
            JPanel p = new JPanel(new BorderLayout());
            JTextArea l = new JTextArea(s);
            l.setLineWrap(true);
            l.setWrapStyleWord(true);
            l.setEditable(false);
            l.setBackground(owner.getBackground());
            ImagePanel ip = new ImagePanel(imgPath);
            p.add(l, BorderLayout.NORTH);
            p.add(ip, BorderLayout.SOUTH);
            this.setContentPane(p);
            this.pack();
            this.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
            this.setLocationRelativeTo(owner);
            this.setAlwaysOnTop(true);
            this.addWindowFocusListener(new WindowFocusListener() {

                @Override
                public void windowGainedFocus(WindowEvent e) {
                    // do nothing
                }

                @Override
                public void windowLostFocus(WindowEvent e) {
                    if (SwingUtilities.isDescendingFrom(e.getOppositeWindow(), InfoDialog.this)) {
                        return;
                    }
                    InfoDialog.this.setVisible(false);
                }
            });
        }
    }

    class ImagePanel extends JPanel {

        private BufferedImage image;

        public ImagePanel(String path) {
            try {
                image = ImageIO.read(new File(path));
            } catch (IOException ex) {
                // handle exception...
            }
        }
        @Override
        protected void paintComponent(Graphics g) {
            super.paintComponent(g);
            g.drawImage(image, 0, 0, this);
        }
    }
}
