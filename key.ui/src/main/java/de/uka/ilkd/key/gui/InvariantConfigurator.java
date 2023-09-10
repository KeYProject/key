/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.util.*;
import java.util.List;
import javax.swing.*;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import javax.swing.text.BadLocationException;
import javax.swing.text.Document;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.pp.PrettyPrinter;
import de.uka.ilkd.key.proof.io.OutputStreamProofSaver;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.InfFlowSpec;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import static java.lang.String.format;

/**
 * This class creates a dialog to input a user-defined invariant, variant and modifies formula for a
 * selected loop.
 *
 * @author Dreiner, bruns
 */
public class InvariantConfigurator {

    private static final int INV_IDX = 0;
    private static final int MOD_IDX = 1;
    private static final int VAR_IDX = 2;
    private static final int IF_PRE_IDX = 3;
    private static final int IF_POST_IDX = 4;
    private static final int IF_OO_IDX = 5;
    private static final String DEFAULT = "Default";

    private static InvariantConfigurator configurator = null;
    private List<Map<String, String>[]> invariants;
    private final HashMap<LoopStatement, List<Map<String, String>[]>> mapLoopsToInvariants;
    private int index = 0;
    private LoopSpecification newInvariant = null;
    private boolean userPressedCancel = false;

    /**
     * Singleton
     */
    private InvariantConfigurator() {
        invariants = new ArrayList<>();
        mapLoopsToInvariants = new LinkedHashMap<>();
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
     * Creates a Dialog. User can enter Invariant, Variant and Modifies clause. The input is parsed
     * and a new loop invariant is returned. In case of a ParserException an error-message is shown.
     *
     * @param loopInv the {@link LoopSpecification} (complete or partial) to be displayed and
     *        edited in the dialog
     * @param services the {@link Services} object
     * @param requiresVariant a boolean indicating whether termination shall be proven
     * @param heapContext a list of {@link LocationVariable}s representing the relevant heaps
     * @return the user edited/completed loop invariant
     * @throws RuleAbortException if the user cancelled the dialog
     */
    public LoopSpecification getLoopInvariant(final LoopSpecification loopInv,
            final Services services, final boolean requiresVariant,
            final List<LocationVariable> heapContext) throws RuleAbortException {
        // Check if there is a LoopInvariant
        if (loopInv == null) {
            return null;
        }

        index = 0;

        class InvariantDialog extends JDialog {
            private final LocationVariable HEAP_LDT =
                services.getTypeConverter().getHeapLDT().getHeap();
            private final Color COLOR_SUCCESS = Color.GREEN;
            private final Color COLOR_ERROR = Color.RED;

            private static final String INVARIANT_REQUIRED = "Invariant is required!";
            private static final String VARIANT_REQUIRED = "Variant required!";
            private static final String INVARIANTTITLE = "Invariant%s: ";
            private static final String VARIANTTITLE = "Variant%s: ";
            private static final String MODIFIESTITLE = "Modifies%s: ";
            private static final String IF_PRE_TITLE = "InfFlowPreExpressions%s: ";
            private static final String IF_POST_TITLE = "InfFlowPostExpressions%s: ";
            private static final String IF_OO_TITLE = "InfFlowNewObjects%s: ";

            private final KeyIO parser;

            private final JTabbedPane inputPane;
            private JPanel errorPanel;
            private final List<JTabbedPane> heapPanes = new ArrayList<>();

            private Term variantTerm = null;
            private final Map<LocationVariable, Term> modifiesTerm = new LinkedHashMap<>();
            private final Map<LocationVariable, Term> freeModifiesTerm = new LinkedHashMap<>();
            private final Map<LocationVariable, ImmutableList<InfFlowSpec>> infFlowSpecs =
                new LinkedHashMap<>();
            private final Map<LocationVariable, Term> invariantTerm = new LinkedHashMap<>();
            private final Map<LocationVariable, Term> freeInvariantTerm = new LinkedHashMap<>();


            private final JButton applyButton = new JButton("Apply");
            private final JButton cancelButton = new JButton("Cancel");
            private final JButton storeButton = new JButton("Store");


            /**
             * Creates the Dialog
             */
            public InvariantDialog() throws RuleAbortException {
                super(MainWindow.getInstance(), true);


                // set Title and Layout
                setTitle("Invariant Configurator");

                getContentPane().setLayout(new BorderLayout());

                // set up the storage for invariants candidates
                initInvariants();

                // set up the input fields and the Loop Code
                // Representation
                errorPanel = initErrorPanel();

                inputPane = new JTabbedPane();
                initInputPane();
                updateActiveTabs(heapContext);


                JTextArea loopRep = initLoopPresentation();
                JPanel leftPanel = new JPanel();
                leftPanel.setLayout(new BorderLayout());
                leftPanel.add(new JSplitPane(JSplitPane.VERTICAL_SPLIT, new JScrollPane(loopRep),
                    new JScrollPane(errorPanel)));

                final int charXWidth = loopRep.getFontMetrics(loopRep.getFont()).charWidth('X');
                final int fontHeight = loopRep.getFontMetrics(loopRep.getFont()).getHeight();
                leftPanel.setMinimumSize(new Dimension(charXWidth * 25, fontHeight * 10));
                leftPanel.setPreferredSize(new Dimension(charXWidth * 40, fontHeight * 15));

                JSplitPane split =
                    new JSplitPane(JSplitPane.HORIZONTAL_SPLIT, true, leftPanel, inputPane);

                getContentPane().add(split, BorderLayout.CENTER);

                split.setDividerLocation(0.7);

                // Add the buttons
                JPanel buttonPanel = new JPanel();
                initButtonPanel(buttonPanel);
                getContentPane().add(buttonPanel, BorderLayout.SOUTH);


                setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);

                final NamespaceSet nss = services.getNamespaces().copyWithParent();
                Term self = loopInv.getInternalSelfTerm();
                if (self != null) {
                    nss.programVariables()
                            .add(new LocationVariable(new ProgramElementName("self"), self.sort()));
                }
                parser = new KeyIO(services, nss);
                parser.setAbbrevMap(getAbbrevMap());

                parse();
                pack();
                setLocationRelativeTo(getOwner());
                setVisible(true);
            }


            /**
             * Sets up the Button Panel on the Bottom of the Invariant Dialog
             *
             * @param buttonPanel the JPanel on which the buttons are placed
             */
            private void initButtonPanel(JPanel buttonPanel) {
                buttonPanel.setLayout(new FlowLayout(FlowLayout.RIGHT));

                applyButton.addActionListener(this::applyActionPerformed);
                cancelButton.addActionListener(this::cancelActionPerformed);
                storeButton.addActionListener(this::storeActionPerformed);

                buttonPanel.add(applyButton);
                buttonPanel.add(storeButton);
                buttonPanel.add(cancelButton);
            }

            /**
             * sets up the right Panel. Input is parsed directly to give the user feedback and
             * display Error Messages.
             */
            private void initInputPane() {
                for (int i = 0; i < invariants.size(); i++) {
                    inputPane.addTab("Inv " + i, createInvariantTab(i));
                    inputPane.validate();

                }
                inputPane.addChangeListener(e -> {
                    index = ((JTabbedPane) e.getSource()).getSelectedIndex();
                    parse();

                });
            }

            /**
             * sets up datastructures for the Invariants
             */
            private void initInvariants() {

                @SuppressWarnings("unchecked")
                Map<String, String>[] loopInvTexts = new Map[IF_OO_IDX + 1];

                loopInvTexts[INV_IDX] = new LinkedHashMap<>();
                final Map<LocationVariable, Term> atPres = loopInv.getInternalAtPres();

                for (LocationVariable heap : services.getTypeConverter().getHeapLDT()
                        .getAllHeaps()) {
                    final Term invariant =
                        loopInv.getInvariant(heap, loopInv.getInternalSelfTerm(), atPres, services);

                    if (invariant == null) {
                        // FIXME check again and think what is the default for savedHeap
                        loopInvTexts[INV_IDX].put(heap.toString(), "true");
                    } else {
                        loopInvTexts[INV_IDX].put(heap.toString(), printTerm(invariant, true));
                    }
                }

                loopInvTexts[MOD_IDX] = new LinkedHashMap<>();

                for (LocationVariable heap : services.getTypeConverter().getHeapLDT()
                        .getAllHeaps()) {
                    final Term modifies =
                        loopInv.getModifies(heap, loopInv.getInternalSelfTerm(), atPres, services);

                    if (modifies == null) {
                        // FIXME check again and think what is the default for savedHeap
                        loopInvTexts[MOD_IDX].put(heap.toString(), "allLocs");
                    } else {
                        // pretty syntax cannot be parsed yet for modifies
                        loopInvTexts[MOD_IDX].put(heap.toString(), printTerm(modifies, false));
                    }
                }

                loopInvTexts[VAR_IDX] = new LinkedHashMap<>();
                final Term variant =
                    loopInv.getVariant(loopInv.getInternalSelfTerm(), atPres, services);
                if (variant == null) {
                    loopInvTexts[VAR_IDX].put(DEFAULT, "");
                } else {
                    loopInvTexts[VAR_IDX].put(DEFAULT, printTerm(variant, true));
                }

                loopInvTexts[IF_PRE_IDX] = new LinkedHashMap<>();

                for (LocationVariable heap : services.getTypeConverter().getHeapLDT()
                        .getAllHeaps()) {
                    final ImmutableList<InfFlowSpec> infFlowSpecs = loopInv.getInfFlowSpecs(heap,
                        loopInv.getInternalSelfTerm(), atPres, services);

                    if (infFlowSpecs == null) {
                        loopInvTexts[IF_PRE_IDX].put(heap.toString(), "true");
                    } else {
                        for (InfFlowSpec infFlowSpec : infFlowSpecs) {
                            for (Term t : infFlowSpec.preExpressions) {
                                loopInvTexts[IF_PRE_IDX].put(heap.toString(), printTerm(t, false));
                            }
                        }
                    }
                }

                loopInvTexts[IF_POST_IDX] = new LinkedHashMap<>();

                for (LocationVariable heap : services.getTypeConverter().getHeapLDT()
                        .getAllHeaps()) {
                    final ImmutableList<InfFlowSpec> infFlowSpecs = loopInv.getInfFlowSpecs(heap,
                        loopInv.getInternalSelfTerm(), atPres, services);

                    if (infFlowSpecs == null) {
                        loopInvTexts[IF_POST_IDX].put(heap.toString(), "true");
                    } else {
                        for (InfFlowSpec infFlowSpec : infFlowSpecs) {
                            for (Term t : infFlowSpec.postExpressions) {
                                loopInvTexts[IF_POST_IDX].put(heap.toString(), printTerm(t, false));
                            }
                        }
                    }
                }

                loopInvTexts[IF_OO_IDX] = new LinkedHashMap<>();

                for (LocationVariable heap : services.getTypeConverter().getHeapLDT()
                        .getAllHeaps()) {
                    final ImmutableList<InfFlowSpec> infFlowSpecs = loopInv.getInfFlowSpecs(heap,
                        loopInv.getInternalSelfTerm(), atPres, services);

                    if (infFlowSpecs == null) {
                        loopInvTexts[IF_OO_IDX].put(heap.toString(), "true");
                    } else {
                        for (InfFlowSpec infFlowSpec : infFlowSpecs) {
                            for (Term t : infFlowSpec.newObjects) {
                                loopInvTexts[IF_OO_IDX].put(heap.toString(), printTerm(t, false));
                            }
                        }
                    }
                }

                if (!mapLoopsToInvariants.containsKey(loopInv.getLoop())) {
                    // add the given Invariant
                    invariants = new ArrayList<>();
                    invariants.add(loopInvTexts);
                    mapLoopsToInvariants.put(loopInv.getLoop(), invariants);
                    index = invariants.size() - 1;
                } else {
                    invariants = mapLoopsToInvariants.get(loopInv.getLoop());
                    // Check if the given invariant is in
                    // the list
                    if (!invariants.contains(loopInvTexts)) {
                        invariants.add(loopInvTexts);
                        index = invariants.size() - 1;
                    } else {
                        // set the index to the
                        // currently used invariant
                        index = invariants.indexOf(loopInvTexts);
                    }
                }
            }

            /**
             * wrapper for the pretty printer
             *
             * @param t the {@link Term} to be printed
             * @return the String representation of the term
             */
            private String printTerm(Term t, boolean pretty) {
                return OutputStreamProofSaver.printTerm(t, services, pretty);

            }

            private JScrollPane createInvariantTab(int i) {
                JPanel panel = new JPanel();
                panel.setLayout(new BoxLayout(panel, BoxLayout.PAGE_AXIS));

                JTabbedPane invPane = new JTabbedPane(JTabbedPane.BOTTOM);
                Map<String, String> invs = invariants.get(i)[INV_IDX];
                for (String k : invs.keySet()) {
                    String title = format(INVARIANTTITLE,
                        k.equals(HeapLDT.BASE_HEAP_NAME.toString()) ? "" : "[" + k + "]");
                    JTextArea textArea = createInputTextArea(title, invs.get(k));
                    setInvariantListener(textArea, k, i);
                    invPane.add(k, textArea);
                }

                JTabbedPane modPane = new JTabbedPane(JTabbedPane.BOTTOM);
                Map<String, String> mods = invariants.get(i)[MOD_IDX];
                for (String k : mods.keySet()) {
                    String title = format(MODIFIESTITLE,
                        k.equals(HeapLDT.BASE_HEAP_NAME.toString()) ? "" : "[" + k + "]");
                    JTextArea textArea = createInputTextArea(title, mods.get(k));
                    setModifiesListener(textArea, k, i);
                    modPane.add(k, textArea);
                }

                JTabbedPane respPane = new JTabbedPane(JTabbedPane.BOTTOM);
                Map<String, String> resps = invariants.get(i)[IF_PRE_IDX];
                for (String k : resps.keySet()) {
                    String title = format(IF_PRE_TITLE,
                        k.equals(HeapLDT.BASE_HEAP_NAME.toString()) ? "" : "[" + k + "]");
                    JTextArea textArea = createInputTextArea(title, resps.get(k));
                    setInfFlowPreExpsListener(textArea, k, i);
                    respPane.add(k, textArea);
                }

                JTabbedPane ifPostPane = new JTabbedPane(JTabbedPane.BOTTOM);
                Map<String, String> postExps = invariants.get(i)[IF_POST_IDX];
                for (String k : postExps.keySet()) {
                    String title = format(IF_POST_TITLE,
                        k.equals(HeapLDT.BASE_HEAP_NAME.toString()) ? "" : "[" + k + "]");
                    JTextArea textArea = createInputTextArea(title, postExps.get(k));
                    setInfFlowPostExpsListener(textArea, k, i);
                    ifPostPane.add(k, textArea);
                }

                JTabbedPane ifNewObjectsPane = new JTabbedPane(JTabbedPane.BOTTOM);
                Map<String, String> ifNewObjects = invariants.get(i)[IF_OO_IDX];
                for (String k : ifNewObjects.keySet()) {
                    String title = format(IF_OO_TITLE,
                        k.equals(HeapLDT.BASE_HEAP_NAME.toString()) ? "" : "[" + k + "]");
                    JTextArea textArea = createInputTextArea(title, ifNewObjects.get(k));
                    setInfFlowNewObsListener(textArea, k, i);
                    ifNewObjectsPane.add(k, textArea);
                }

                JTextArea vararea = createInputTextArea(format(VARIANTTITLE, ""),
                    invariants.get(i)[VAR_IDX].get(DEFAULT));
                setVariantListener(vararea, DEFAULT, i);

                panel.add(invPane);
                panel.add(modPane);
                panel.add(vararea);
                panel.add(respPane);
                panel.add(ifPostPane);
                panel.add(ifNewObjectsPane);
                heapPanes.add(invPane);
                heapPanes.add(modPane);

                JScrollPane rightPane = new JScrollPane(panel);

                final int charXWidth = vararea.getFontMetrics(vararea.getFont()).charWidth('X');
                final int fontHeight = vararea.getFontMetrics(vararea.getFont()).getHeight();

                rightPane.setMinimumSize(new Dimension(charXWidth * 72, fontHeight * 15));
                rightPane.setPreferredSize(new Dimension(charXWidth * 80, fontHeight * 20));


                return rightPane;

            }

            public JTextArea createInputTextArea(String title, String text) {
                JTextArea inputTextArea = new JTextArea(text);
                inputTextArea.setBorder(BorderFactory.createTitledBorder(
                    BorderFactory.createLineBorder(Color.DARK_GRAY), title));
                inputTextArea.setEditable(true);
                return inputTextArea;
            }

            private void setInvariantListener(JTextArea ta, final String key, int i) {
                index = i;
                ta.getDocument().addDocumentListener(new DocumentListener() {
                    public void removeUpdate(DocumentEvent e) {
                        invUpdatePerformed(e, key);
                    }

                    public void insertUpdate(DocumentEvent e) {
                        invUpdatePerformed(e, key);
                    }

                    public void changedUpdate(DocumentEvent e) {
                        invUpdatePerformed(e, key);
                    }
                });
            }

            private void setVariantListener(JTextArea ta, final String key, int i) {
                index = i;
                ta.getDocument().addDocumentListener(new DocumentListener() {

                    public void removeUpdate(DocumentEvent e) {
                        varUpdatePerformed(e, key);
                    }

                    public void insertUpdate(DocumentEvent e) {
                        varUpdatePerformed(e, key);
                    }

                    public void changedUpdate(DocumentEvent e) {
                        varUpdatePerformed(e, key);
                    }
                });
            }

            private void setModifiesListener(JTextArea ta, final String key, int i) {
                index = i;
                ta.getDocument().addDocumentListener(new DocumentListener() {

                    public void removeUpdate(DocumentEvent e) {
                        modUpdatePerformed(e, key);
                    }

                    public void insertUpdate(DocumentEvent e) {
                        modUpdatePerformed(e, key);
                    }

                    public void changedUpdate(DocumentEvent e) {
                        modUpdatePerformed(e, key);
                    }
                });
            }

            private void setInfFlowPreExpsListener(JTextArea ta, final String key, int i) {
                index = i;
                ta.getDocument().addDocumentListener(new DocumentListener() {

                    public void removeUpdate(DocumentEvent e) {
                        ifPreExpsUdatePerformed(e, key);
                    }

                    public void insertUpdate(DocumentEvent e) {
                        ifPreExpsUdatePerformed(e, key);
                    }

                    public void changedUpdate(DocumentEvent e) {
                        ifPreExpsUdatePerformed(e, key);
                    }
                });
            }

            private void setInfFlowPostExpsListener(JTextArea ta, final String key, int i) {
                index = i;
                ta.getDocument().addDocumentListener(new DocumentListener() {

                    public void removeUpdate(DocumentEvent e) {
                        ifPostExpsUdatePerformed(e, key);
                    }

                    public void insertUpdate(DocumentEvent e) {
                        ifPostExpsUdatePerformed(e, key);
                    }

                    public void changedUpdate(DocumentEvent e) {
                        ifPostExpsUdatePerformed(e, key);
                    }
                });
            }

            private void setInfFlowNewObsListener(JTextArea ta, final String key, int i) {
                index = i;
                ta.getDocument().addDocumentListener(new DocumentListener() {

                    public void removeUpdate(DocumentEvent e) {
                        ifNewObjectsUdatePerformed(e, key);
                    }

                    public void insertUpdate(DocumentEvent e) {
                        ifNewObjectsUdatePerformed(e, key);
                    }

                    public void changedUpdate(DocumentEvent e) {
                        ifNewObjectsUdatePerformed(e, key);
                    }
                });
            }

            private JTextArea initLoopPresentation() {
                JTextArea loopRep = new JTextArea();
                String source;
                PrettyPrinter printer = PrettyPrinter.purePrinter();
                printer.print(loopInv.getLoop());
                source = printer.result();
                loopRep.setText(source);
                loopRep.setEditable(false);
                loopRep.setBackground(new Color(220, 220, 220));
                loopRep.setMinimumSize(loopRep.getPreferredScrollableViewportSize());
                loopRep.setLayout(new BorderLayout());
                loopRep.setBorder(BorderFactory.createTitledBorder("Loop"));
                return loopRep;
            }

            private JPanel createErrorPanel(Map<String, String> invMsgs,
                    Map<String, Color> invColors, Map<String, String> modMsgs,
                    Map<String, Color> modColors, Map<String, String> varMsgs,
                    Map<String, Color> varColors) {
                JPanel panel = new JPanel();
                panel.setLayout(new BoxLayout(panel, BoxLayout.PAGE_AXIS));

                JTabbedPane invPane = new JTabbedPane(JTabbedPane.BOTTOM);
                JTabbedPane modPane = new JTabbedPane(JTabbedPane.BOTTOM);
                for (LocationVariable heap : services.getTypeConverter().getHeapLDT()
                        .getAllHeaps()) {
                    final String k = heap.name().toString();
                    String title =
                        format("Invariant%s - Status: ", heap == HEAP_LDT ? "" : "[" + k + "]");
                    String errorMessage = invMsgs == null ? "OK" : invMsgs.get(k);
                    Color invColor = invColors == null ? COLOR_SUCCESS : invColors.get(k);
                    JTextArea textArea = createErrorTextField(title, errorMessage, invColor);
                    invPane.add(k, textArea);
                    title = format("Modifies%s - Status: ", heap == HEAP_LDT ? "" : "[" + k + "]");
                    String errorMessage2 = modMsgs == null ? "OK" : modMsgs.get(k);
                    Color modColor = modColors == null ? COLOR_SUCCESS : modColors.get(k);
                    textArea = createErrorTextField(title, errorMessage2, modColor);
                    modPane.add(k, textArea);
                }
                panel.add(invPane);
                panel.add(modPane);
                heapPanes.add(invPane);
                heapPanes.add(modPane);
                JTextArea varErrorArea = createErrorTextField("Variant - Status",
                    varMsgs.get(DEFAULT), varColors.get(DEFAULT));
                panel.add(varErrorArea);

                final int charXWidth =
                    varErrorArea.getFontMetrics(varErrorArea.getFont()).charWidth('X');
                final int fontHeight =
                    varErrorArea.getFontMetrics(varErrorArea.getFont()).getHeight();

                varErrorArea.setMinimumSize(new Dimension(charXWidth * 80, fontHeight * 5));
                varErrorArea.setPreferredSize(new Dimension(charXWidth * 80, fontHeight * 10));
                varErrorArea.setMaximumSize(new Dimension(charXWidth * 80, fontHeight * 15));

                return panel;

            }

            private JPanel initErrorPanel() {
                Map<String, String> invMsgs = new LinkedHashMap<>();
                Map<String, Color> invColors = new LinkedHashMap<>();
                Map<String, String> modMsgs = new LinkedHashMap<>();
                Map<String, Color> modColors = new LinkedHashMap<>();
                Map<String, String> varMsgs = new LinkedHashMap<>();
                Map<String, Color> varColors = new LinkedHashMap<>();

                for (LocationVariable heap : services.getTypeConverter().getHeapLDT()
                        .getAllHeaps()) {
                    final String k = heap.name().toString();
                    setOK(invMsgs, invColors, k);
                    setOK(modMsgs, modColors, k);
                }
                setOK(varMsgs, varColors, DEFAULT);
                return createErrorPanel(invMsgs, invColors, modMsgs, modColors, varMsgs, varColors);
            }

            private void setOK(Map<String, String> msgMap, Map<String, Color> colors,
                    String setOn) {
                msgMap.put(setOn, "OK");
                colors.put(setOn, COLOR_SUCCESS);
            }

            private void setError(Map<String, String> msgMap, Map<String, Color> colors,
                    String setOn, String errorMsg) {
                msgMap.put(setOn, errorMsg);
                colors.put(setOn, COLOR_ERROR);
            }

            private JTextArea createErrorTextField(String title, String errorMessage, Color color) {
                JTextArea errorTextfield = new JTextArea();
                errorTextfield.setPreferredSize(errorTextfield.getMinimumSize());
                errorTextfield.setBorder(BorderFactory.createTitledBorder(title));
                errorTextfield.setText(errorMessage);
                errorTextfield.setForeground(color);
                errorTextfield.setEditable(false);
                errorTextfield.setMinimumSize(errorTextfield.getPreferredScrollableViewportSize());
                return errorTextfield;
            }

            public void cancelActionPerformed(ActionEvent e) {
                userPressedCancel = true;
                newInvariant = null;
                this.dispose();
            }

            /**
             * copies the current invariant to another tab
             *
             * @param aE
             */
            public void storeActionPerformed(ActionEvent aE) {
                index = inputPane.getSelectedIndex();
                Map<String, String>[] invs = invariants.get(index).clone();
                invariants.add(invs);
                index = invariants.size() - 1;
                inputPane.addTab("Inv " + (invariants.size() - 1), createInvariantTab(index));
                this.validate();

            }

            /**
             * parse the current invariant and write it to newInvariant. If parsing fails, an error
             * message is displayed.
             *
             * @param ae
             */
            public void applyActionPerformed(ActionEvent ae) {
                index = inputPane.getSelectedIndex();
                parse();
                if (this.buildInvariant()) {
                    this.dispose();
                }

            }

            /**
             * Updates the String that hold the invariant Term.
             *
             * @param d
             */
            private void invUpdatePerformed(DocumentEvent d, String key) {
                Document doc = d.getDocument();
                index = inputPane.getSelectedIndex();

                Map<String, String>[] inv = invariants.get(index);
                try {
                    inv[INV_IDX].put(key, doc.getText(0, doc.getLength()));
                } catch (BadLocationException e) {
                    // ignore
                } finally {
                    parse();
                }
            }

            public void modUpdatePerformed(DocumentEvent d, String key) {
                Document doc = d.getDocument();
                index = inputPane.getSelectedIndex();

                Map<String, String>[] inv = invariants.get(index);
                try {
                    inv[MOD_IDX].put(key, doc.getText(0, doc.getLength()));
                } catch (BadLocationException e) {
                    // ignore
                } finally {
                    parse();
                }
            }

            public void ifPreExpsUdatePerformed(DocumentEvent d, String key) {
                Document doc = d.getDocument();
                index = inputPane.getSelectedIndex();

                Map<String, String>[] inv = invariants.get(index);
                try {
                    inv[IF_PRE_IDX].put(key, doc.getText(0, doc.getLength()));
                } catch (BadLocationException e) {
                    // ignore
                } finally {
                    parse();
                }
            }

            public void ifPostExpsUdatePerformed(DocumentEvent d, String key) {
                Document doc = d.getDocument();
                index = inputPane.getSelectedIndex();

                Map<String, String>[] inv = invariants.get(index);
                try {
                    inv[IF_POST_IDX].put(key, doc.getText(0, doc.getLength()));
                } catch (BadLocationException e) {
                    // ignore
                } finally {
                    parse();
                }
            }

            public void ifNewObjectsUdatePerformed(DocumentEvent d, String key) {
                Document doc = d.getDocument();
                index = inputPane.getSelectedIndex();

                Map<String, String>[] inv = invariants.get(index);
                try {
                    inv[IF_OO_IDX].put(key, doc.getText(0, doc.getLength()));
                } catch (BadLocationException e) {
                    // ignore
                } finally {
                    parse();
                }
            }

            public void varUpdatePerformed(DocumentEvent d, String key) {
                if (!key.equals(DEFAULT)) {
                    throw new IllegalStateException();
                }
                Document doc = d.getDocument();
                index = inputPane.getSelectedIndex();

                Map<String, String>[] inv = invariants.get(index);
                try {
                    inv[VAR_IDX].put(key, doc.getText(0, doc.getLength()));
                } catch (BadLocationException e) {
                    // ignore
                } finally {
                    parse();
                }
            }

            /**
             * tries to build a new Invariant from the currently given Terms
             */
            private boolean buildInvariant() {
                boolean requirementsAreMet = true;
                if (requiresVariant && variantTerm == null) {
                    Map<String, String> varErrors = new LinkedHashMap<>();
                    Map<String, Color> varColors = new LinkedHashMap<>();
                    setError(varErrors, varColors, DEFAULT, VARIANT_REQUIRED);
                    updateErrorPanel(null, null, null, null, varErrors, varColors);
                    requirementsAreMet = false;
                }

                if (invariantTerm.isEmpty()) {
                    requirementsAreMet = false;
                    Map<String, String> invErrors = new LinkedHashMap<>();
                    Map<String, Color> invColors = new LinkedHashMap<>();
                    setError(invErrors, invColors, DEFAULT, INVARIANT_REQUIRED);
                    updateErrorPanel(invErrors, invColors, null, null, null, null);
                }

                if (requirementsAreMet) {
                    newInvariant = loopInv.configurate(invariantTerm, freeInvariantTerm,
                        modifiesTerm, freeModifiesTerm, infFlowSpecs, variantTerm);
                    return true;
                } else {
                    return false;
                }
            }

            /**
             * No Comment
             */
            private void parse() {
                Map<String, String> invErrors = new LinkedHashMap<>();
                Map<String, Color> invCols = new LinkedHashMap<>();
                Map<String, String> modErrors = new LinkedHashMap<>();
                Map<String, Color> modCols = new LinkedHashMap<>();
                Map<String, String> respErrors = new LinkedHashMap<>();
                Map<String, Color> respCols = new LinkedHashMap<>();
                for (LocationVariable heap : services.getTypeConverter().getHeapLDT()
                        .getAllHeaps()) {
                    try {
                        invariantTerm.put(heap, parseInvariant(heap));
                        setOK(invErrors, invCols, heap.toString());
                    } catch (Exception e) {
                        setError(invErrors, invCols, heap.toString(), e.getMessage());
                    }
                    try {
                        modifiesTerm.put(heap, parseModifies(heap));
                        setOK(modErrors, modCols, heap.toString());
                    } catch (Exception e) {
                        setError(modErrors, modCols, heap.toString(), e.getMessage());
                    }
                }
                LocationVariable baseHeap = HEAP_LDT;
                // TODO: add post expressions and new objects
                try {
                    infFlowSpecs.put(baseHeap, parseInfFlowSpec(baseHeap));
                    setOK(respErrors, respCols, baseHeap.toString());
                } catch (Exception e) {
                    setError(respErrors, respCols, baseHeap.toString(), e.getMessage());
                }
                Map<String, String> varErrors = new LinkedHashMap<>();
                Map<String, Color> varCols = new LinkedHashMap<>();

                try {
                    int i = inputPane.getSelectedIndex();
                    // TODO Jonas: hier geht's bei der manuellen Regelanwendung vermutlich schief,
                    // wenn es nur freie Invarianten gibt
                    if (invariants.get(i)[VAR_IDX].get(DEFAULT).equals("")) {
                        variantTerm = null;
                        if (requiresVariant) {
                            throw new ParserException(VARIANT_REQUIRED, null);
                        }
                    } else {
                        variantTerm = parseVariant();
                        setOK(varErrors, varCols, DEFAULT);

                    }
                } catch (Exception e) {
                    setError(varErrors, varCols, DEFAULT, e.getMessage());
                }

                updateErrorPanel(invErrors, invCols, modErrors, modCols, varErrors, varCols);

            }

            private void updateActiveTabs(List<LocationVariable> heapContext) {
                for (JTabbedPane p : heapPanes) {
                    for (int j = 0; j < p.getTabCount(); j++) {
                        p.setEnabledAt(j, false);
                    }
                    for (LocationVariable lv : heapContext) {
                        p.setEnabledAt(p.indexOfTab(lv.name().toString()), true);
                    }

                }
            }

            private void updateErrorPanel(Map<String, String> invErrors, Map<String, Color> invCols,
                    Map<String, String> modErrors, Map<String, Color> modCols,
                    Map<String, String> varErrors, Map<String, Color> varCols) {
                boolean reeinit = true;
                boolean errorFound = false;

                if (invErrors != null) {
                    for (Map.Entry<String, String> entry : invErrors.entrySet()) {
                        String k = entry.getKey();
                        String invError = entry.getValue();
                        Color invCol = invCols.get(k);
                        JTabbedPane p = (JTabbedPane) errorPanel.getComponent(0);
                        JTextArea jta = (JTextArea) p.getComponent(p.indexOfTab(k));
                        jta.setForeground(invCol);
                        jta.setText(invError);
                        if (invCol == COLOR_ERROR) {
                            errorFound = true;
                        }
                    }
                    reeinit = false;
                }
                if (modErrors != null) {
                    for (Map.Entry<String, String> entry : modErrors.entrySet()) {
                        String k = entry.getKey();
                        String modError = entry.getValue();
                        Color modCol = modCols.get(k);
                        JTabbedPane p = (JTabbedPane) errorPanel.getComponent(1);
                        JTextArea jta = (JTextArea) p.getComponent(p.indexOfTab(k));
                        jta.setForeground(modCol);
                        jta.setText(modError);
                        if (modCol == COLOR_ERROR) {
                            errorFound = true;
                        }
                    }
                    reeinit = false;
                }
                if (varErrors != null) {
                    String varError = varErrors.get(DEFAULT);
                    Color varCol = varCols.get(DEFAULT);
                    JTextArea jta = (JTextArea) errorPanel.getComponent(2);
                    jta.setForeground(varCol);
                    jta.setText(varError);
                    if (varCol == COLOR_ERROR) {
                        errorFound = true;
                    }
                    reeinit = false;
                }

                applyButton.setEnabled(!errorFound);
                storeButton.setEnabled(!errorFound);

                if (!reeinit) {
                    Container con = errorPanel.getParent();
                    con.remove(errorPanel);
                    Dimension d = errorPanel.getPreferredSize();
                    errorPanel = createErrorPanel(invErrors, invCols, modErrors, modCols, varErrors,
                        varCols);
                    updateActiveTabs(heapContext);
                    errorPanel.setPreferredSize(d);
                    con.add(errorPanel, BorderLayout.SOUTH);
                }
            }

            /**
             * evil REDUNDANCY!!!
             *
             * @return invariant term
             * @throws Exception
             */
            protected Term parseInvariant(LocationVariable heap) {
                index = inputPane.getSelectedIndex();
                Term result =
                    parser.parseExpression(invariants.get(index)[INV_IDX].get(heap.toString()));
                if (result.sort() != Sort.FORMULA) {
                    throw newUnexpectedTypeException(Sort.FORMULA, result.sort());
                }
                return result;
            }

            private AbbrevMap getAbbrevMap() {
                return MainWindow.getInstance().getMediator().getNotationInfo().getAbbrevMap();
            }

            protected Term parseModifies(LocationVariable heap) {
                index = inputPane.getSelectedIndex();
                final Sort locSetSort = services.getTypeConverter().getLocSetLDT().targetSort();
                String string = invariants.get(index)[MOD_IDX].get(heap.toString());
                if (string.trim().equals("\\strictly_nothing")) {
                    // FIXME
                    // This is a hack that has been introduced to be able
                    // to enter "strictly_nothing" also in interactive mode.
                    return services.getTermBuilder().strictlyNothing();
                }
                Term result = parser.parseExpression(string);
                if (result.sort() != locSetSort) {
                    throw newUnexpectedTypeException(locSetSort, result.sort());
                }
                return result;
            }

            protected ImmutableList<InfFlowSpec> parseInfFlowSpec(LocationVariable heap) {
                index = inputPane.getSelectedIndex();
                final String preExpsAsString =
                    invariants.get(index)[IF_PRE_IDX].get(heap.toString());
                final String postExpsAsString =
                    invariants.get(index)[IF_POST_IDX].get(heap.toString());
                final String newObjectsAsString =
                    invariants.get(index)[IF_OO_IDX].get(heap.toString());
                // TODO: allow more than one term
                Term preExps = parser.parseExpression(preExpsAsString);
                // TODO: allow more than one term
                Term postExps = parser.parseExpression(postExpsAsString);
                // TODO: allow more than one term
                Term newObjects = parser.parseExpression(newObjectsAsString);

                return ImmutableSLList.<InfFlowSpec>nil()
                        .append(new InfFlowSpec(ImmutableSLList.<Term>nil().append(preExps),
                            ImmutableSLList.<Term>nil().append(postExps),
                            ImmutableSLList.<Term>nil().append(newObjects)));
            }

            protected Term parseVariant() {
                index = inputPane.getSelectedIndex();
                final Sort intSort = services.getTypeConverter().getIntegerLDT().targetSort();
                Term result = parser.parseExpression(invariants.get(index)[VAR_IDX].get(DEFAULT));
                if (result.sort() != intSort) {
                    throw newUnexpectedTypeException(intSort, result.sort());
                }
                return result;
            }
        }

        // Create the Dialog
        userPressedCancel = false;
        // Caution: dialogue made modal in the constructor! (TODO change this)
        InvariantDialog dia = new InvariantDialog();
        dia.dispose();
        if (this.userPressedCancel) {
            throw new RuleAbortException("Interactive invariant configuration canceled by user.");
        }

        return newInvariant;
    }

    private static RuntimeException newUnexpectedTypeException(Sort expected, Sort actual) {
        return new IllegalStateException(
            format("Entered formula is expected of type %s but got %s.", expected, actual));
    }
}
