package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.pp.LogicPrinter;

import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.speclang.LoopInvariantImpl;

import java.awt.BorderLayout;
import java.awt.ComponentOrientation;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.ArrayList;
import java.util.HashMap;

import javax.swing.BorderFactory;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.JTabbedPane;
import javax.swing.JTextArea;
import javax.swing.ScrollPaneLayout;
import javax.swing.border.TitledBorder;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import javax.swing.text.Document;

import de.uka.ilkd.key.logic.TermBuilder;
import java.awt.Color;
import java.awt.Panel;



/**
 * @author Dreiner This class creates a Dialog to input a loop Invariant,
 *         Variant and Modifies.
 */
public class InvariantConfigurator {

    // Data
    private static InvariantConfigurator configurator = null;
    private ArrayList<String[]> invariants = null;
    private HashMap<LoopStatement, ArrayList<String[]>> mapLoopsToInvariants =
            null;
    private int index = 0;
    private LoopInvariant newInvariant = null;
    // Initialize the Parse
    final DefaultTermParser p = new DefaultTermParser();

    // Methods

    /**
     * Singleton
     */
    private InvariantConfigurator() {
        invariants = new ArrayList<String[]>();
        mapLoopsToInvariants = new HashMap<LoopStatement, ArrayList<String[]>>();
    }


    /**
     * Returns the single Instance of this class
     */
    public static InvariantConfigurator getInstance() {
        if (configurator == null) {
            configurator = new InvariantConfigurator();
        }
        return configurator;
    }


    /**
     * Creates a Dialog. User can enter Invariant, Variant and Modifies
     * clause. The Input is parsed and a new LoopInvariant is returned. In
     * Case of a parser Exception an error-message is shown.
     *
     * @param loopInv
     * @param services
     * @return LoopInvariant
     */
    public LoopInvariant getLoopInvariant(final LoopInvariant loopInv,
                                          final Services services,
                                          final boolean requiresVariant) {
        // Check if there is a LoopInvariant
        if (loopInv == null) {
            return null;
        }

        index = 0;
        /**
         * The given LoopInvariant is put into the List and then handed
         * to the Dialog.
         */
        String[] loopInvStr = new String[3];
        if (loopInv.getInvariant(loopInv.getInternalSelfTerm(),
                                 loopInv.getInternalHeapAtPre(), null) == null) {
            loopInvStr[0] = "";
        } else {
            loopInvStr[0] = LogicPrinter.quickPrintTerm(
                    loopInv.getInvariant(
                    loopInv.getInternalSelfTerm(),
                    loopInv.getInternalHeapAtPre(),
                    null),
                    services);
        }

        if (loopInv.getModifies(loopInv.getInternalSelfTerm(),
                                loopInv.getInternalHeapAtPre(), null) == null) {
            loopInvStr[1] = "";
        } else {
            loopInvStr[1] = LogicPrinter.quickPrintTerm(
                    loopInv.getModifies(
                    loopInv.getInternalSelfTerm(),
                    loopInv.getInternalHeapAtPre(),
                    null),
                    services);
        }

        if (loopInv.getVariant(loopInv.getInternalSelfTerm(),
                               loopInv.getInternalHeapAtPre(), null) == null) {
            loopInvStr[2] = "";
        } else {
            loopInvStr[2] = LogicPrinter.quickPrintTerm(
                    loopInv.getVariant(
                    loopInv.getInternalSelfTerm(),
                    loopInv.getInternalHeapAtPre(),
                    null),
                    services);
        }

        if (!mapLoopsToInvariants.containsKey(loopInv.getLoop())) {
            // add the given Invariant
            invariants = new ArrayList<String[]>();
            invariants.add(loopInvStr);
            mapLoopsToInvariants.put(loopInv.getLoop(), invariants);
            index = invariants.size() - 1;
        } else {
            invariants = mapLoopsToInvariants.get(loopInv.getLoop());
            // Check if the given invariant is in the list
            if (!invariants.contains(loopInvStr)) {
                invariants.add(loopInvStr);
                index = invariants.size() - 1;
            } else {
                // set the index to the currently used invariant
                index = invariants.indexOf(loopInvStr);
            }
        }

        /*
         * local class makes the dialog
         */

        class InvariantDialog extends JDialog {

            private JTabbedPane inputPane;
//                        private JPanel msgPanel = new JPanel();


            public InvariantDialog() {
                super(Main.getInstance(), true);
                // set Title and Layout
                setTitle("Invariant Configurator");
                getContentPane().setLayout(new BorderLayout());
//                                getContentPane().applyComponentOrientation(
//                                                                ComponentOrientation.LEFT_TO_RIGHT);
//                                setPreferredSize(new Dimension(400, 600));
                inputPane = new JTabbedPane();
                JTextArea loopRep = initLoopPresentation();

                for (int i = 0; i < invariants.size(); i++) {
                    JPanel panel = createInvariantTab(i);
                    inputPane.addTab("Inv " + i, panel);
                    inputPane.validate();

                }

                /*  Dimension minimumSize = new Dimension(400, 200);
                inputPane.setMinimumSize(minimumSize);
                loopRep.setMinimumSize(minimumSize);*/

                JSplitPane split = new JSplitPane();
                split.setTopComponent(new JScrollPane(loopRep));
                split.setBottomComponent(inputPane);

                getContentPane().add(split, BorderLayout.CENTER);

                // Add the buttons
                JPanel buttonPanel = new JPanel();
                buttonPanel.setLayout(new FlowLayout(
                        FlowLayout.RIGHT));
                JButton applyButton = new JButton("apply");
                JButton cancelButton = new JButton("cancel");
                JButton storeButton = new JButton("store");

                applyButton.addActionListener(new ActionListener() {

                    public void actionPerformed(
                            ActionEvent e) {
                        System.out.println("Apply Button pressed!");
                        applyActionPerformed(e);
                    }
                });
                cancelButton.addActionListener(new ActionListener() {

                    public void actionPerformed(
                            ActionEvent e) {
                        cancelActionPerformed(e);
                    }
                });
                storeButton.addActionListener(new ActionListener() {

                    public void actionPerformed(
                            ActionEvent e) {
                        storeActionPerformed(e);
                    }
                });

                buttonPanel.add(applyButton);
                buttonPanel.add(storeButton);
                buttonPanel.add(cancelButton);
                getContentPane().add(buttonPanel, BorderLayout.SOUTH);

                this.pack();
                this.setVisible(true);
            }


            private JPanel createInvariantTab(int i) {
                JScrollPane scrollpane = new JScrollPane();
                JPanel panel = new JPanel();
                JTextArea invarea = null;
                invarea = new JTextArea(invariants.get(i)[0]);
                invarea.setPreferredSize(new Dimension(200, 20));
                invarea.setBorder(new TitledBorder("Invariant:"));
                invarea.getDocument().addDocumentListener(new DocumentListener() {

                    public void removeUpdate(DocumentEvent e) {
                        invUdatePerformed(e);
                    }


                    public void insertUpdate(DocumentEvent e) {
                        invUdatePerformed(e);
                    }


                    public void changedUpdate(DocumentEvent e) {
                        invUdatePerformed(e);
                    }
                });
                JTextArea modarea = null;
                JTextArea vararea = null;
                modarea = new JTextArea(invariants.get(i)[1]);
                vararea = new JTextArea(invariants.get(i)[2]);
                modarea.setPreferredSize(new Dimension(200, 20));
                vararea.setPreferredSize(new Dimension(200, 20));
                modarea.setBorder(new TitledBorder("Modifies:"));
                vararea.setBorder(new TitledBorder("Variant:"));
                modarea.getDocument().addDocumentListener(new DocumentListener() {

                    public void removeUpdate(DocumentEvent e) {
                        modUdatePerformed(e);
                    }


                    public void insertUpdate(DocumentEvent e) {
                        modUdatePerformed(e);
                    }


                    public void changedUpdate(DocumentEvent e) {
                        modUdatePerformed(e);
                    }
                });
                vararea.getDocument().addDocumentListener(new DocumentListener() {

                    public void removeUpdate(DocumentEvent e) {
                        varUdatePerformed(e);
                    }


                    public void insertUpdate(DocumentEvent e) {
                        varUdatePerformed(e);
                    }


                    public void changedUpdate(DocumentEvent e) {
                        varUdatePerformed(e);
                    }
                });
                panel.add(invarea);
                panel.add(modarea);
                panel.add(vararea);
                panel.setLayout(new BoxLayout(panel,
                                              BoxLayout.PAGE_AXIS));
                scrollpane.add(new Panel(new BorderLayout()).add(panel));
                return panel;
            }


            private JTextArea initLoopPresentation() {
                JTextArea loopRep =
                        new JTextArea(loopInv.getLoop().toSource());
                loopRep.setEditable(false);
                loopRep.setBackground(new Color(240, 240, 240));
                loopRep.setPreferredSize(new Dimension(200, 20));
                loopRep.setMinimumSize(new Dimension(400, 150));
                loopRep.setLayout(new BorderLayout());
                loopRep.setBorder(BorderFactory.createTitledBorder("Loop"));
                return loopRep;
            }

            // Actions

            public void cancelActionPerformed(ActionEvent e) {
                this.dispose();
            }


            /**
             * copy the current invariant to another tab
             *
             * @param e
             */
            public void storeActionPerformed(ActionEvent aE) {
                index = inputPane.getSelectedIndex();
                String[] invs = invariants.get(index).clone();
                invariants.add(invs);

                JTextArea invarea = new JTextArea(invs[0]);
                JTextArea modarea = new JTextArea(invs[1]);
                JTextArea vararea = new JTextArea(invs[2]);

                invarea.setBorder(new TitledBorder(
                        "Invariant:"));
                modarea.setBorder(new TitledBorder(
                        "Modifies:"));
                vararea.setBorder(new TitledBorder("Variant:"));

                invarea.setPreferredSize(new Dimension(
                        200, 20));
                modarea.setPreferredSize(new Dimension(
                        200, 20));
                vararea.setPreferredSize(new Dimension(
                        200, 20));

                invarea.getDocument().addDocumentListener(
                        new DocumentListener() {

                            public void removeUpdate(
                                    DocumentEvent e) {
                                invUdatePerformed(e);
                            }


                            public void insertUpdate(
                                    DocumentEvent e) {
                                invUdatePerformed(e);
                            }


                            public void changedUpdate(
                                    DocumentEvent e) {
                                invUdatePerformed(e);
                            }
                        });
                modarea.getDocument().addDocumentListener(
                        new DocumentListener() {

                            public void removeUpdate(
                                    DocumentEvent e) {
                                modUdatePerformed(e);
                            }


                            public void insertUpdate(
                                    DocumentEvent e) {
                                modUdatePerformed(e);
                            }


                            public void changedUpdate(
                                    DocumentEvent e) {
                                modUdatePerformed(e);
                            }
                        });
                vararea.getDocument().addDocumentListener(
                        new DocumentListener() {

                            public void removeUpdate(
                                    DocumentEvent e) {
                                varUdatePerformed(e);
                            }


                            public void insertUpdate(
                                    DocumentEvent e) {
                                varUdatePerformed(e);
                            }


                            public void changedUpdate(
                                    DocumentEvent e) {
                                varUdatePerformed(e);
                            }
                        });

                JPanel panel = new JPanel();
                panel.add(invarea);
                panel.add(modarea);
                panel.add(vararea);
                panel.setLayout(new BoxLayout(panel,
                                              BoxLayout.PAGE_AXIS));

                inputPane.addTab("Inv "
                                 + (invariants.size() - 1),
                                 panel);

                this.pack();
                this.setVisible(true);

            }


            /**
             * parse the current invariant and write it to
             * newInvariant. If parsing fails, an error message is
             * displayed.
             *
             * @param e
             */
            public void applyActionPerformed(ActionEvent ae) {
                index = inputPane.getSelectedIndex();
                try {
                    parse();
                    this.dispose();
                } catch (Exception e) {
                    System.out.println("500: \n");
                    this.displayError(e.getMessage());
                }
            }


            public void invUdatePerformed(DocumentEvent d) {
                Document doc = d.getDocument();
                index = inputPane.getSelectedIndex();

                String[] inv = invariants.get(index);
                try {
                    inv[0] = doc.getText(
                            0,
                            doc.getLength());
                } catch (Exception e) {
                }

            }


            public void modUdatePerformed(DocumentEvent d) {
                Document doc = d.getDocument();
                index = inputPane.getSelectedIndex();

                String[] inv = invariants.get(index);
                try {
                    inv[1] = doc.getText(
                            0,
                            doc.getLength());
                } catch (Exception e) {
                }
            }


            public void varUdatePerformed(DocumentEvent d) {
                Document doc = d.getDocument();
                index = inputPane.getSelectedIndex();

                String[] inv = invariants.get(index);
                try {
                    inv[2] = doc.getText(
                            0,
                            doc.getLength());
                } catch (Exception e) {
                }
            }


            /**
             * Calls the parser and creates the
             * Loopinvarant-attribute.
             */
            public void parse()
                    throws Exception {
                Term invariantTerm = null;
                Term variantTerm = null;
                Term modifiesTerm = null;
                index = inputPane.getSelectedIndex();
                invariantTerm = TermBuilder.DF.parseTerm(
                        invariants.get(index)[0],
                        services);

                modifiesTerm = TermBuilder.DF.parseTerm(
                        invariants.get(index)[1],
                        services);
                variantTerm = TermBuilder.DF.parseTerm(
                        invariants.get(index)[2],
                        services);
                /*
                 * Check if the Variant is required and empty
                 */
                if (requiresVariant && variantTerm == null) {
                    System.out.println("576: \n");
                    throw new ParserException(
                            "Variant is required!",
                            new Location(null, 2, 1));
                } else if (invariantTerm == null) {
                    System.out.println("584: \n");
                    throw new ParserException(
                            "Invariant is required!",
                            new Location(null, 1, 1));
                } else {
                    newInvariant = new LoopInvariantImpl(
                            loopInv.getLoop(),
                            invariantTerm,
                            modifiesTerm,
                            variantTerm,
                            loopInv.getInternalSelfTerm(),
                            loopInv.getInternalHeapAtPre());
                }

            }


            public void displayError(String msg) {
//                                this.getContentPane().remove(msgPanel);
                System.out.println("612: " + msg);
//                                msgPanel = new JPanel();
                JTextArea errorMsg = new JTextArea(msg);
                errorMsg.setPreferredSize(new Dimension(
                        400, 50));
                errorMsg.setEditable(false);
                errorMsg.setBorder(BorderFactory.createEmptyBorder());
                errorMsg.setLineWrap(true);
//                                msgPanel.add(errorMsg);
//                                msgPanel.setLayout(new BoxLayout(msgPanel,
//                                                BoxLayout.LINE_AXIS));
//                                msgPanel.setVisible(true);
//                                this.getContentPane().add(msgPanel);
                this.validate();
                this.pack();
            }
        }

        // Create the Dialog
        InvariantDialog dia = new InvariantDialog();
        dia.dispose();

        return newInvariant;
    }
}
