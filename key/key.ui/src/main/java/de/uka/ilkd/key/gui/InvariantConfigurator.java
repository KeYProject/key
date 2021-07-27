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
import java.awt.Container;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.StringReader;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import javax.swing.BorderFactory;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.JTabbedPane;
import javax.swing.JTextArea;
import javax.swing.WindowConstants;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import javax.swing.text.Document;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.InfFlowSpec;

/**
 * @author Dreiner, bruns
 * 
 *         This class creates a Dialog to input a loop Invariant, Variant and
 *         Modifies.
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
    private List<Map<String,String>[]> invariants = null;
    private HashMap<LoopStatement, List<Map<String,String>[]>> mapLoopsToInvariants = null;
    private int index = 0;
    private LoopSpecification newInvariant = null;
    private boolean userPressedCancel = false;

    /**
     * Singleton
     */
    private InvariantConfigurator() {
        invariants = new ArrayList<Map<String,String>[]>();
        mapLoopsToInvariants = new LinkedHashMap<LoopStatement, List<Map<String,String>[]>>();
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
     * Creates a Dialog. User can enter Invariant, Variant and Modifies clause.
     * The Input is parsed and a new LoopInvariant is returned. In Case of a
     * parser Exception an error-message is shown.
     * 
     * @param loopInv
     * @param services
     * @return LoopInvariant
     */
    public LoopSpecification getLoopInvariant (final LoopSpecification loopInv,
            final Services services, final boolean requiresVariant, final List<LocationVariable> heapContext)
                    throws RuleAbortException {
        // Check if there is a LoopInvariant
        if (loopInv == null) {
            return null;
        }

        index = 0;

        class InvariantDialog extends JDialog {


            private static final String INVARIANT_REQUIRED = "Invariant is required!";
            private static final String VARIANT_REQUIRED = "Variant required!";
            private static final long serialVersionUID = 4320775749093028498L;
            private StringWriter sw = new StringWriter();
            private DefaultTermParser parser = new DefaultTermParser();


            //Creates a new Printer, pretty Syntax cannot be parsed up to now!
            /* private final LogicPrinter printer = new LogicPrinter(
                    new ProgramPrinter(sw), null, Main.getInstance().mediator()
                            .getServices());*/
            private JTabbedPane inputPane;
            private JPanel errorPanel;
            private List<JTabbedPane> heapPanes = new ArrayList<JTabbedPane>();

            private Term variantTerm = null;
            private Map<LocationVariable,Term> modifiesTerm = new LinkedHashMap<LocationVariable,Term>();
            private Map<LocationVariable,
                        ImmutableList<InfFlowSpec>> infFlowSpecs
                    = new LinkedHashMap<LocationVariable,
                                        ImmutableList<InfFlowSpec>>();
            private Map<LocationVariable,Term> invariantTerm = new LinkedHashMap<LocationVariable,Term>();
            private Map<LocationVariable,Term> freeInvariantTerm = new LinkedHashMap<LocationVariable,Term>();

            private static final String INVARIANTTITLE = "Invariant%s: ";
            private static final String VARIANTTITLE = "Variant%s: ";
            private static final String MODIFIESTITLE = "Modifies%s: ";
            private static final String IF_PRE_TITLE = "InfFlowPreExpressions%s: ";
            private static final String IF_POST_TITLE = "InfFlowPostExpressions%s: ";
            private static final String IF_OO_TITLE = "InfFlowNewObjects%s: ";


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
                leftPanel.add(new JSplitPane(JSplitPane.VERTICAL_SPLIT,
                        new JScrollPane(loopRep), new JScrollPane(errorPanel)));

                final int charXWidth = loopRep.getFontMetrics(loopRep.getFont()).charWidth('X');
                final int fontHeight = loopRep.getFontMetrics(loopRep.getFont()).getHeight();
                leftPanel.setMinimumSize(new Dimension(charXWidth * 25, fontHeight * 10));
                leftPanel.setPreferredSize(new Dimension(charXWidth * 40, fontHeight * 15));

                JSplitPane split = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT,
                        true, leftPanel, inputPane);

                getContentPane().add(split, BorderLayout.CENTER);

                split.setDividerLocation(0.7);

                // Add the buttons
                JPanel buttonPanel = new JPanel();
                initButtonPanel(buttonPanel);
                getContentPane().add(buttonPanel, BorderLayout.SOUTH);


                setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);

                parse();
                this.pack();
                this.setVisible(true);
            }

            /**
             * Sets up the Button Panel on the Bottom of the Invariant Dialog
             * 
             * @param buttonPanel
             */
            private void initButtonPanel(JPanel buttonPanel) throws RuleAbortException {
                buttonPanel.setLayout(new FlowLayout(FlowLayout.RIGHT));
                JButton applyButton = new JButton("Apply");
                JButton cancelButton = new JButton("Cancel");
                JButton storeButton = new JButton("Store");

                applyButton.addActionListener(new ActionListener() {

                    public void actionPerformed(ActionEvent e) {
                        applyActionPerformed(e);
                    }
                });
                cancelButton.addActionListener(new ActionListener() {

                    public void actionPerformed(ActionEvent e) {
                        cancelActionPerformed(e);
                    }
                });
                storeButton.addActionListener(new ActionListener() {

                    public void actionPerformed(ActionEvent e) {
                        storeActionPerformed(e);
                    }
                });

                buttonPanel.add(applyButton);
                buttonPanel.add(storeButton);
                buttonPanel.add(cancelButton);
            }

            /**
             * sets up the right Panel. Input is parsed directly to give the
             * user feedback and display Error Messages.
             */
            private void initInputPane() {
                for (int i = 0; i < invariants.size(); i++) {
                    inputPane.addTab("Inv " + i, createInvariantTab(i));
                    inputPane.validate();

                }
                inputPane.addChangeListener(new ChangeListener() {

                    @Override
                    public void stateChanged(ChangeEvent e) {
                        index = ((JTabbedPane) e.getSource())
                                .getSelectedIndex();
                        parse();

                    }
                });
            }

            /**
             * sets up datastructures for the Invariants
             */
            private void initInvariants() {

                @SuppressWarnings("unchecked")
                Map<String,String>[] loopInvTexts = new Map[IF_OO_IDX+1];

                loopInvTexts[INV_IDX] = new LinkedHashMap<String,String>();
                final Map<LocationVariable,Term> atPres = loopInv.getInternalAtPres();

                for(LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                    final Term i = loopInv.getInvariant(heap, loopInv.getInternalSelfTerm(), atPres, services);

                    if (i == null) {
                        // FIXME check again and think what is the default for savedHeap
                        loopInvTexts[INV_IDX].put(heap.toString(), "true");
                    } else {
                        loopInvTexts[INV_IDX].put(heap.toString(), printTerm(i, true));
                    }
                }

                loopInvTexts[MOD_IDX] = new LinkedHashMap<String,String>();

                for(LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                    final Term modifies = loopInv.getModifies(heap, loopInv.getInternalSelfTerm(), atPres, services);

                    if (modifies == null) {
                        // FIXME check again and think what is the default for savedHeap
                        loopInvTexts[MOD_IDX].put(heap.toString(), "allLocs");
                    } else {
                        // pretty syntax cannot be parsed yet for modifies
                        loopInvTexts[MOD_IDX].put(heap.toString(), printTerm(modifies, false));
                    }
                }

                loopInvTexts[VAR_IDX] = new LinkedHashMap<String,String>();
                final Term variant = loopInv.getVariant(loopInv.getInternalSelfTerm(), atPres, services);
                if (variant == null) {
                    loopInvTexts[VAR_IDX].put(DEFAULT,"");
                } else {                    
                    loopInvTexts[VAR_IDX].put(DEFAULT,printTerm(variant, true));
                }

                loopInvTexts[IF_PRE_IDX] = new LinkedHashMap<String,String>();

                for(LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                  final ImmutableList<InfFlowSpec>
                          infFlowSpecs = loopInv.getInfFlowSpecs(heap, loopInv.getInternalSelfTerm(), atPres, services);

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

                loopInvTexts[IF_POST_IDX] = new LinkedHashMap<String,String>();

                for(LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                  final ImmutableList<InfFlowSpec>
                          infFlowSpecs = loopInv.getInfFlowSpecs(heap, loopInv.getInternalSelfTerm(), atPres, services);

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

                loopInvTexts[IF_OO_IDX] = new LinkedHashMap<String,String>();

                for(LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                  final ImmutableList<InfFlowSpec>
                          infFlowSpecs = loopInv.getInfFlowSpecs(heap, loopInv.getInternalSelfTerm(), atPres, services);

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
                    invariants = new ArrayList<Map<String,String>[]>();
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
             * just a Wrapper for the pretty Printer
             * 
             * @param t
             * @return the String Representation of the Term
             */
            private String printTerm(Term t, boolean pretty) {                
                return ProofSaver.printTerm(t, services, pretty).toString();

            }

            private JScrollPane createInvariantTab(int i) {
                JPanel panel = new JPanel();
                panel.setLayout(new BoxLayout(panel, BoxLayout.PAGE_AXIS));

                JTabbedPane invPane = new JTabbedPane(JTabbedPane.BOTTOM);
                Map<String,String> invs = invariants.get(i)[INV_IDX];
                for(String k : invs.keySet()) {
                    String title = String.format(INVARIANTTITLE, k.equals(HeapLDT.BASE_HEAP_NAME.toString()) ? "" : "["+k+"]");
                    JTextArea textArea = createInputTextArea(title, invs.get(k), i);
                    setInvariantListener(textArea, k, i);
                    invPane.add(k, textArea);
                }

                JTabbedPane modPane = new JTabbedPane(JTabbedPane.BOTTOM);
                Map<String,String> mods = invariants.get(i)[MOD_IDX];
                for(String k : mods.keySet()) {
                    String title = String.format(MODIFIESTITLE, k.equals(HeapLDT.BASE_HEAP_NAME.toString()) ? "" : "["+k+"]");
                    JTextArea textArea = createInputTextArea(title, mods.get(k), i);
                    setModifiesListener(textArea, k, i);
                    modPane.add(k, textArea);
                }
                
                JTabbedPane respPane = new JTabbedPane(JTabbedPane.BOTTOM);
                Map<String,String> resps = invariants.get(i)[IF_PRE_IDX];
                for(String k : resps.keySet()) {
                   String title = String.format(IF_PRE_TITLE, k.equals(HeapLDT.BASE_HEAP_NAME.toString()) ? "" : "["+k+"]");
                   JTextArea textArea = createInputTextArea(title, resps.get(k), i);
                   setInfFlowPreExpsListener(textArea, k, i);
                   respPane.add(k, textArea);
                }

                JTabbedPane ifPostPane = new JTabbedPane(JTabbedPane.BOTTOM);
                Map<String,String> postExps = invariants.get(i)[IF_POST_IDX];
                for(String k : postExps.keySet()) {
                   String title = String.format(IF_POST_TITLE, k.equals(HeapLDT.BASE_HEAP_NAME.toString()) ? "" : "["+k+"]");
                   JTextArea textArea = createInputTextArea(title, postExps.get(k), i);
                   setInfFlowPostExpsListener(textArea, k, i);
                   ifPostPane.add(k, textArea);
                }

                JTabbedPane ifNewObjectsPane = new JTabbedPane(JTabbedPane.BOTTOM);
                Map<String,String> ifNewObjects = invariants.get(i)[IF_OO_IDX];
                for(String k : ifNewObjects.keySet()) {
                   String title = String.format(IF_OO_TITLE, k.equals(HeapLDT.BASE_HEAP_NAME.toString()) ? "" : "["+k+"]");
                   JTextArea textArea = createInputTextArea(title, ifNewObjects.get(k), i);
                   setInfFlowNewObsListener(textArea, k, i);
                   ifNewObjectsPane.add(k, textArea);
                }

                JTextArea vararea = createInputTextArea(String.format(VARIANTTITLE,""),
                        invariants.get(i)[VAR_IDX].get(DEFAULT), i);
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

            public JTextArea createInputTextArea(String Title, String Text,
                    int i) {
                JTextArea inputTextArea = new JTextArea(Text);
                inputTextArea
                .setBorder(BorderFactory
                        .createTitledBorder(BorderFactory
                                .createLineBorder(Color.DARK_GRAY),
                                Title));
                inputTextArea.setEditable(true);
                return inputTextArea;
            }

            private void setInvariantListener(JTextArea ta, final String key, int i) {
                index = i;
                ta.getDocument().addDocumentListener(new DocumentListener() {

                    public void removeUpdate(DocumentEvent e) {
                        invUdatePerformed(e, key);
                    }

                    public void insertUpdate(DocumentEvent e) {
                        invUdatePerformed(e, key);
                    }

                    public void changedUpdate(DocumentEvent e) {
                        invUdatePerformed(e, key);
                    }
                });
            }

            private void setVariantListener(JTextArea ta, final String key, int i) {
                index = i;
                ta.getDocument().addDocumentListener(new DocumentListener() {

                    public void removeUpdate(DocumentEvent e) {
                        varUdatePerformed(e, key);
                    }

                    public void insertUpdate(DocumentEvent e) {
                        varUdatePerformed(e, key);
                    }

                    public void changedUpdate(DocumentEvent e) {
                        varUdatePerformed(e, key);
                    }
                });
            }

            private void setModifiesListener(JTextArea ta, final String key, int i) {
                index = i;
                ta.getDocument().addDocumentListener(new DocumentListener() {

                    public void removeUpdate(DocumentEvent e) {
                        modUdatePerformed(e, key);
                    }

                    public void insertUpdate(DocumentEvent e) {
                        modUdatePerformed(e, key);
                    }

                    public void changedUpdate(DocumentEvent e) {
                        modUdatePerformed(e, key);
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
                String source = "";
                try {
                    loopInv.getLoop().prettyPrint(new PrettyPrinter(sw));
                    source = sw.toString();
                    // printer
                    // .printJavaBlock(JavaBlock
                    // .createJavaBlock(new StatementBlock(
                    // (Statement) loopInv
                    // .getLoop())));
                    // source = sw.toString();
                } catch (Exception e) {
                    source = loopInv.getLoop().toSource();
                }
                loopRep.setText(source);

                // (loopInv
                // .getLoop().toSource());
                loopRep.setEditable(false);
                loopRep.setBackground(new Color(220, 220, 220));
                loopRep.setMinimumSize(loopRep
                        .getPreferredScrollableViewportSize());
                loopRep.setLayout(new BorderLayout());
                loopRep.setBorder(BorderFactory.createTitledBorder("Loop"));
                return loopRep;
            }

            private JPanel createErrorPanel(Map<String,String> invMsgs, Map<String,Color> invColors,
                    Map<String,String> modMsgs, Map<String,Color> modColors, Map<String,String> varMsgs, Map<String,Color> varColors) {
                JPanel panel = new JPanel();
                panel.setLayout(new BoxLayout(panel, BoxLayout.PAGE_AXIS));

                JTabbedPane invPane = new JTabbedPane(JTabbedPane.BOTTOM);
                JTabbedPane modPane = new JTabbedPane(JTabbedPane.BOTTOM);
                for(LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                    final String k = heap.name().toString();
                    String title = String.format("Invariant%s - Status: ", heap == services.getTypeConverter().getHeapLDT().getHeap() ? "" : "["+k+"]");
                    String errorMessage = invMsgs == null? "OK" : invMsgs.get(k);
                    Color invColor = invColors == null? Color.GREEN : invColors.get(k);
                    JTextArea textArea = createErrorTextField(title, errorMessage,
                            invColor);
                    invPane.add(k, textArea);
                    title = String.format("Modifies%s - Status: ", heap == services.getTypeConverter().getHeapLDT().getHeap() ? "" : "["+k+"]");
                    String errorMessage2 = modMsgs == null? "OK" : modMsgs.get(k);
                    Color modColor = modColors == null? Color.GREEN : modColors.get(k);
                    textArea = createErrorTextField(title, errorMessage2,
                            modColor);
                    modPane.add(k, textArea);
                }
                panel.add(invPane);
                panel.add(modPane);
                heapPanes.add(invPane);
                heapPanes.add(modPane);
                JTextArea varErrorArea = createErrorTextField("Variant - Status", varMsgs.get(DEFAULT),
                        varColors.get(DEFAULT));
                panel.add(varErrorArea);

                final int charXWidth = varErrorArea.getFontMetrics(varErrorArea.getFont()).charWidth('X');
                final int fontHeight = varErrorArea.getFontMetrics(varErrorArea.getFont()).getHeight();

                varErrorArea.setMinimumSize(new Dimension(charXWidth * 80, fontHeight * 5));
                varErrorArea.setPreferredSize(new Dimension(charXWidth * 80, fontHeight * 10));
                varErrorArea.setMaximumSize(new Dimension(charXWidth * 80, fontHeight * 15));

                return panel;

            }

            private JPanel initErrorPanel() {
                Map<String,String> invMsgs = new LinkedHashMap<String,String>();
                Map<String,Color> invColors = new LinkedHashMap<String,Color>();
                Map<String,String> modMsgs = new LinkedHashMap<String,String>();
                Map<String,Color> modColors = new LinkedHashMap<String,Color>();
                Map<String,String> varMsgs = new LinkedHashMap<String,String>();
                Map<String,Color> varColors = new LinkedHashMap<String,Color>();
                
                for(LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                    final String k = heap.name().toString();
                    setOK(invMsgs, invColors, k);
                    setOK(modMsgs, modColors, k);
                }
                setOK(varMsgs, varColors, DEFAULT);
                return createErrorPanel(invMsgs, invColors, modMsgs, modColors,
                        varMsgs, varColors);
            }

            private void setOK(Map<String, String> msgMap,
                    Map<String, Color> colors, String setOn) {
                msgMap.put(setOn, "OK");
                colors.put(setOn, Color.GREEN);
            }

            private void setError(Map<String, String> msgMap, Map<String, Color> colors, String setOn, String errorMsg){
                msgMap.put(setOn, errorMsg);
                colors.put(setOn, Color.RED);
            }

            private JTextArea createErrorTextField(String Title,
                    String errorMessage, Color color) {
                JTextArea errorTextfield = new JTextArea();
                errorTextfield
                .setPreferredSize(errorTextfield.getMinimumSize());
                errorTextfield.setBorder(BorderFactory
                        .createTitledBorder(Title));
                errorTextfield.setText(errorMessage);
                errorTextfield.setForeground(color);
                errorTextfield.setEditable(false);
                errorTextfield.setMinimumSize(errorTextfield
                        .getPreferredScrollableViewportSize());
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
                Map<String,String>[] invs = invariants.get(index).clone();
                invariants.add(invs);
                index = invariants.size() - 1;
                inputPane.addTab("Inv " + (invariants.size() - 1),
                        createInvariantTab(index));
                this.validate();

            }

            /**
             * parse the current invariant and write it to newInvariant. If
             * parsing fails, an error message is displayed.
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
            private void invUdatePerformed(DocumentEvent d, String key) {
                Document doc = d.getDocument();
                index = inputPane.getSelectedIndex();

                Map<String,String>[] inv = invariants.get(index);
                try {
                    inv[INV_IDX].put(key, doc.getText(0, doc.getLength()));
                } catch (Exception e) {
                } finally {
                    parse();
                }
            }

            public void modUdatePerformed(DocumentEvent d, String key) {
                Document doc = d.getDocument();
                index = inputPane.getSelectedIndex();

                Map<String,String>[] inv = invariants.get(index);
                try {
                    inv[MOD_IDX].put(key, doc.getText(0, doc.getLength()));
                } catch (Exception e) {
                } finally {
                    parse();
                }
            }
            
            public void ifPreExpsUdatePerformed(DocumentEvent d, String key) {
                Document doc = d.getDocument();
                index = inputPane.getSelectedIndex();

                Map<String,String>[] inv = invariants.get(index);
                try {
                    inv[IF_PRE_IDX].put(key, doc.getText(0, doc.getLength()));
                } catch (Exception e) {
                } finally {
                    parse();
                }
            }

            public void ifPostExpsUdatePerformed(DocumentEvent d, String key) {
                Document doc = d.getDocument();
                index = inputPane.getSelectedIndex();

                Map<String,String>[] inv = invariants.get(index);
                try {
                    inv[IF_POST_IDX].put(key, doc.getText(0, doc.getLength()));
                } catch (Exception e) {
                } finally {
                    parse();
                }
            }

            public void ifNewObjectsUdatePerformed(DocumentEvent d, String key) {
                Document doc = d.getDocument();
                index = inputPane.getSelectedIndex();

                Map<String,String>[] inv = invariants.get(index);
                try {
                    inv[IF_OO_IDX].put(key, doc.getText(0, doc.getLength()));
                } catch (Exception e) {
                } finally {
                    parse();
                }
            }

            public void varUdatePerformed(DocumentEvent d, String key) {
                assert key.equals(DEFAULT);
                Document doc = d.getDocument();
                index = inputPane.getSelectedIndex();

                Map<String,String>[] inv = invariants.get(index);
                try {
                    inv[VAR_IDX].put(key, doc.getText(0, doc.getLength()));
                } catch (Exception e) {
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
                    Map<String,String> varErrors = new LinkedHashMap<String,String>();
                    Map<String,Color> varColors = new LinkedHashMap<String,Color>();
                    setError(varErrors,varColors,DEFAULT,VARIANT_REQUIRED);
                    updateErrorPanel(null, null, null, null,
                            varErrors, varColors);
                    requirementsAreMet = false;
                }

                if (invariantTerm == null) {
                    requirementsAreMet = false;
                    Map<String,String> invErrors = new LinkedHashMap<String,String>();
                    Map<String,Color> invColors = new LinkedHashMap<String,Color>();
                    setError(invErrors,invColors,DEFAULT,INVARIANT_REQUIRED);
                    updateErrorPanel(invErrors, invColors, null,
                            null, null, null);
                }

                if (requirementsAreMet) {
                    newInvariant = loopInv.configurate(invariantTerm, freeInvariantTerm, modifiesTerm,
                                                       infFlowSpecs, variantTerm);
                    return true;
                } else
                    return false;
            }

            /**
             * No Comment
             */
            private void parse() {
                Map<String,String> invErrors = new LinkedHashMap<String,String>();
                Map<String,Color>  invCols = new LinkedHashMap<String,Color>();
                Map<String,String> modErrors = new LinkedHashMap<String,String>();                
                Map<String,Color>  modCols = new LinkedHashMap<String,Color>();
                Map<String,String> respErrors = new LinkedHashMap<String,String>();
                Map<String,Color>  respCols = new LinkedHashMap<String,Color>();
                for(LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                    try {
                        invariantTerm.put(heap, parseInvariant(heap));
                        setOK(invErrors,invCols,heap.toString());
                    } catch (Exception e) {
                        setError(invErrors,invCols,heap.toString(),e.getMessage());
                    }
                    try {
                        modifiesTerm.put(heap, parseModifies(heap));
                        setOK(modErrors,modCols,heap.toString());
                    } catch (Exception e) {
                        setError(modErrors,modCols,heap.toString(),e.getMessage());
                    }
                }
                LocationVariable baseHeap = services.getTypeConverter().getHeapLDT().getHeap();
                // TODO: add post expressions and new objects
                try {
                    infFlowSpecs.put(baseHeap, parseInfFlowSpec(baseHeap));
                    setOK(respErrors,respCols,baseHeap.toString());
                  } catch (Exception e) {
                      setError(respErrors,respCols,baseHeap.toString(),e.getMessage());
                  }
                Map<String,String> varErrors = new LinkedHashMap<String,String>();
                Map<String,Color>  varCols = new LinkedHashMap<String,Color>();

                try {
                    int i = inputPane.getSelectedIndex();
                    //TODO Jonas: hier geht's bei der manuellen Regelanwendung vermutlich schief, wenn es nur freie Invarianten gibt
                    if (invariants.get(i)[VAR_IDX].get(DEFAULT).equals("")) {
                        variantTerm = null;
                        if (requiresVariant) {
                            throw new ParserException(VARIANT_REQUIRED,null);
                        }
                    } else {
                        variantTerm = parseVariant();
                        setOK(varErrors,varCols,DEFAULT);

                    }
                } catch (Exception e) {
                    setError(varErrors,varCols,DEFAULT,e.getMessage());
                }

                updateErrorPanel(invErrors, invCols, modErrors, modCols, varErrors,
                        varCols);

            }

            private void updateActiveTabs(List<LocationVariable> heapContext) {
                for(JTabbedPane p : heapPanes) {
                    for(int j = 0; j<p.getTabCount(); j++) {
                        p.setEnabledAt(j, false);
                    }
                    for(LocationVariable lv : heapContext) {
                        p.setEnabledAt(p.indexOfTab(lv.name().toString()), true);
                    }

                }
            }

            private void updateErrorPanel(Map<String,String> invErrors, Map<String,Color> invCols,
                    Map<String,String> modErrors, Map<String,Color> modCols, Map<String,String> varErrors, Map<String,Color> varCols) {
                boolean reeinit = true;

                if (invErrors != null) {
                    for(String k : invErrors.keySet()) {
                        String invError = invErrors.get(k);
                        Color invCol = invCols.get(k);
                        JTabbedPane p = (JTabbedPane) errorPanel.getComponent(0);
                        JTextArea jta = (JTextArea)p.getComponent(p.indexOfTab(k));
                        jta.setForeground(invCol);
                        jta.setText(invError);
                        // Set also the tab color
                    }
                    reeinit = false;
                }
                if(modErrors != null) {
                    for(String k : modErrors.keySet()) {
                        String modError = modErrors.get(k);
                        Color modCol = modCols.get(k);
                        JTabbedPane p = (JTabbedPane) errorPanel.getComponent(1);
                        JTextArea jta = (JTextArea)p.getComponent(p.indexOfTab(k));
                        jta.setForeground(modCol);
                        jta.setText(modError);
                        // Set also the tab color
                    }
                    reeinit = false;
                }
                if (varErrors != null) {
                    String varError = varErrors.get(DEFAULT);
                    Color varCol = varCols.get(DEFAULT);
                    JTextArea jta = (JTextArea) errorPanel.getComponent(2);
                    jta.setForeground(varCol);
                    jta.setText(varError);
                    reeinit = false;
                }
                if (!reeinit) {
                    Container con = errorPanel.getParent();
                    con.remove(errorPanel);
                    Dimension d = errorPanel.getPreferredSize();
                    errorPanel = createErrorPanel(invErrors, invCols, modErrors,
                            modCols, varErrors, varCols);
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
            protected Term parseInvariant(LocationVariable heap) throws ParserException {
                Term result = null;
                index = inputPane.getSelectedIndex();
                // might throw parserException

                result =  parser.parse(new StringReader(invariants.get(index)[INV_IDX].get(heap.toString())), 
                        Sort.FORMULA, services, services.getNamespaces(), getAbbrevMap());

                return result;
            }

            private AbbrevMap getAbbrevMap() {
                return MainWindow.getInstance().getMediator().getNotationInfo().getAbbrevMap();
            }

            protected Term parseModifies(LocationVariable heap) throws ParserException {
                Term result = null;
                index = inputPane.getSelectedIndex();
                final Sort locSetSort = services.getTypeConverter().getLocSetLDT().targetSort();
                result = parser.parse(
                        new StringReader(invariants.get(index)[MOD_IDX].get(heap.toString())), locSetSort,
                        services, services.getNamespaces(), getAbbrevMap());
                return result;
            }
            
            protected ImmutableList<InfFlowSpec> parseInfFlowSpec(LocationVariable heap) throws Exception {
                Term preExps = null;
                Term postExps = null;
                Term newObjects = null;
                //ImmutableList<ImmutableList<Term>> result = null;
                index = inputPane.getSelectedIndex();
                // might throw parserException or some obscure
                // antlr
                final String preExpsAsString = invariants.get(index)[IF_PRE_IDX].get(heap.toString());
                final String postExpsAsString = invariants.get(index)[IF_POST_IDX].get(heap.toString());
                final String newObjectsAsString = invariants.get(index)[IF_OO_IDX].get(heap.toString());
                // TODO: allow more than one term
                preExps = parser.parse(
                      new StringReader(preExpsAsString), Sort.ANY,
                      services, services.getNamespaces(), getAbbrevMap());
                // TODO: allow more than one term
                postExps = parser.parse(
                      new StringReader(postExpsAsString), Sort.ANY,
                      services, services.getNamespaces(), getAbbrevMap());
                // TODO: allow more than one term
                newObjects = parser.parse(
                      new StringReader(newObjectsAsString), Sort.ANY,
                      services, services.getNamespaces(), getAbbrevMap());
                ImmutableList<InfFlowSpec> result =
                    ImmutableSLList.<InfFlowSpec>nil()
                                   .append(new InfFlowSpec
                                                     (ImmutableSLList.<Term>nil().append(preExps),
                                                      ImmutableSLList.<Term>nil().append(postExps),
                                                      ImmutableSLList.<Term>nil().append(newObjects)));
                return result;
            }

            protected Term parseVariant() throws ParserException {
                Term result = null;
                index = inputPane.getSelectedIndex();
                final Sort intSort = services.getTypeConverter().getIntegerLDT().targetSort();
                result = parser.parse(
                        new StringReader(invariants.get(index)[VAR_IDX].get(DEFAULT)), intSort,
                        services, services.getNamespaces(), getAbbrevMap());
                return result;
            }

        }

        // Create the Dialog
        userPressedCancel = false;
        // Caution: dialogue made modal in the constructor! (TODO change this)
        InvariantDialog dia = new InvariantDialog();
        dia.dispose();
        if(this.userPressedCancel) {
            throw new RuleAbortException("Interactive invariant configuration canceled by user.");
        }

        return newInvariant;
    }
}
