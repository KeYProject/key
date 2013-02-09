package de.uka.ilkd.key.gui;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.StringReader;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.List;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;

import javax.swing.*;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import javax.swing.text.Document;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.speclang.LoopInvariantImpl;
import de.uka.ilkd.key.util.Triple;

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
    private static final int RSP_IDX = 3;
    private static final String DEFAULT = "Default";

    private static InvariantConfigurator configurator = null;
    // TODO: store Terms instead of Strings
    private List<Map<String,String>[]> invariants = null;
    private HashMap<LoopStatement, List<Map<String,String>[]>> mapLoopsToInvariants = null;
    private int index = 0;
    private LoopInvariant newInvariant = null;
    private boolean userPressedCancel = false;

    /**
     * Singleton
     */
    private InvariantConfigurator() {
        invariants = new ArrayList<Map<String,String>[]>();
        mapLoopsToInvariants = new HashMap<LoopStatement, List<Map<String,String>[]>>();
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
    public LoopInvariant getLoopInvariant (final LoopInvariant loopInv,
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
                        ImmutableList<Triple<ImmutableList<Term>,
                                             ImmutableList<Term>,
                                             ImmutableList<Term>>>> respectsTermList
                    = new LinkedHashMap<LocationVariable,
                                        ImmutableList<Triple<ImmutableList<Term>,
                                                             ImmutableList<Term>,
                                                             ImmutableList<Term>>>>();
            private Map<LocationVariable,Term> invariantTerm = new LinkedHashMap<LocationVariable,Term>();

            private static final String INVARIANTTITLE = "Invariant%s: ";
            private static final String VARIANTTITLE = "Variant%s: ";
            private static final String MODIFIESTITLE = "Modifies%s: ";
            private static final String RESPECTSTITLE = "Respects%s: ";


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

                
                setDefaultCloseOperation(WindowConstants.DO_NOTHING_ON_CLOSE);
                
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
                JButton applyButton = new JButton("apply");
                JButton cancelButton = new JButton("cancel");
                JButton storeButton = new JButton("store");

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

                @SuppressWarnings({"unchecked"})
                Map<String,String>[] loopInvTexts = new Map[RSP_IDX+1];

                loopInvTexts[INV_IDX] = new LinkedHashMap<String,String>();
                final Map<LocationVariable,Term> atPres = loopInv.getInternalAtPres();

                for(LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                  final Term i = loopInv.getInvariant(heap, loopInv.getInternalSelfTerm(), atPres, services);

                  if (i == null) {
                    // FIXME check again and think what is the default for savedHeap
                    loopInvTexts[INV_IDX].put(heap.toString(), "true");
                  } else {
                    loopInvTexts[INV_IDX].put(heap.toString(), printTerm(i, false));
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

                loopInvTexts[RSP_IDX] = new LinkedHashMap<String,String>();

                for(LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                  final ImmutableList<Triple<ImmutableList<Term>,ImmutableList<Term>,ImmutableList<Term>>>
                          respects = loopInv.getRespects(heap, loopInv.getInternalSelfTerm(), atPres, services);

                  if (respects == null) {                    
                    loopInvTexts[RSP_IDX].put(heap.toString(), "noRespects");
                  } else {
                      for (Triple<ImmutableList<Term>,
                                  ImmutableList<Term>,
                                  ImmutableList<Term>> trip : respects) {
                          for (Term t : trip.first) {
                              loopInvTexts[RSP_IDX].put(heap.toString(), printTerm(t, false));
                          }
                      }                                        
                  }
                }

                loopInvTexts[VAR_IDX] = new LinkedHashMap<String,String>();
                final Term variant = loopInv.getVariant(loopInv.getInternalSelfTerm(), atPres, services);
                if (variant == null) {
                    loopInvTexts[VAR_IDX].put(DEFAULT,"");
                } else {                    
                    loopInvTexts[VAR_IDX].put(DEFAULT,printTerm(variant, false));
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
                Map<String,String> resps = invariants.get(i)[RSP_IDX];
                for(String k : resps.keySet()) {
                   String title = String.format(RESPECTSTITLE, k.equals(HeapLDT.BASE_HEAP_NAME.toString()) ? "" : "["+k+"]");
                   JTextArea textArea = createInputTextArea(title, resps.get(k), i);
                   setRespectsListener(textArea, k, i);
                   respPane.add(k, textArea);
                }

                JTextArea vararea = createInputTextArea(String.format(VARIANTTITLE,""),
                        invariants.get(i)[VAR_IDX].get(DEFAULT), i);
                setVariantListener(vararea, DEFAULT, i);

                panel.add(invPane);
                panel.add(modPane);
                panel.add(vararea);
                heapPanes.add(invPane);
                heapPanes.add(modPane);

                JScrollPane rightPane = new JScrollPane(panel);;
                
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
            
            private void setRespectsListener(JTextArea ta, final String key, int i) {
                index = i;
                ta.getDocument().addDocumentListener(new DocumentListener() {

                    public void removeUpdate(DocumentEvent e) {
                        respUdatePerformed(e, key);
                    }

                    public void insertUpdate(DocumentEvent e) {
                        respUdatePerformed(e, key);
                    }

                    public void changedUpdate(DocumentEvent e) {
                        respUdatePerformed(e, key);
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
                for(Name h : HeapLDT.VALID_HEAP_NAMES ) {
                   String k = h.toString();
                   String title = String.format("Invariant%s - Status: ", k.equals(HeapLDT.BASE_HEAP_NAME.toString()) ? "" : "["+k+"]");
                   String errorMessage = invMsgs == null? "OK" : invMsgs.get(k);
                   Color invColor = invColors == null? Color.GREEN : invColors.get(k);
                   JTextArea textArea = createErrorTextField(title, errorMessage,
                        invColor);
                   invPane.add(k, textArea);
                   title = String.format("Modifies%s - Status: ", k.equals(HeapLDT.BASE_HEAP_NAME.toString()) ? "" : "["+k+"]");
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
                for(Name h : HeapLDT.VALID_HEAP_NAMES ) {
                   String k = h.toString();
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
            
            public void respUdatePerformed(DocumentEvent d, String key) {
                Document doc = d.getDocument();
                index = inputPane.getSelectedIndex();

                Map<String,String>[] inv = invariants.get(index);
                try {
                    inv[RSP_IDX].put(key, doc.getText(0, doc.getLength()));
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
                    newInvariant = new LoopInvariantImpl(loopInv.getLoop(),
                            invariantTerm, modifiesTerm, respectsTermList, variantTerm, loopInv
                                    .getInternalSelfTerm(), loopInv.getLocalIns(),
                                    loopInv.getLocalOuts(), loopInv.getInternalAtPres());
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
                    setOK(respErrors,modCols,heap.toString());
                  } catch (Exception e) {
                      setError(respErrors,modCols,heap.toString(),e.getMessage());
                  }
                }
                LocationVariable baseHeap = services.getTypeConverter().getHeapLDT().getHeap();
                try {
                    respectsTermList.put(baseHeap, parseRespects(baseHeap));
                    setOK(respErrors,respCols,baseHeap.toString());
                  } catch (Exception e) {
                      setError(respErrors,respCols,baseHeap.toString(),e.getMessage());
                  }
                Map<String,String> varErrors = new LinkedHashMap<String,String>();
                Map<String,Color>  varCols = new LinkedHashMap<String,Color>();

                try {
                    int i = inputPane.getSelectedIndex();
                    if (invariants.get(i)[VAR_IDX].get(DEFAULT).equals("")) {
                        variantTerm = null;
                        if (requiresVariant) {
                            throw new Exception(VARIANT_REQUIRED);
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
            protected Term parseInvariant(LocationVariable heap) throws Exception {
                Term result = null;
                index = inputPane.getSelectedIndex();
                // might throw parserException
                
                final String invAsString = invariants.get(index)[INV_IDX].get(heap.toString());
                result =  parser.parse(new StringReader(invAsString), Sort.ANY, services, services.getNamespaces(),
                getAbbrevMap());

                return result;
            }

            private AbbrevMap getAbbrevMap() {
                return MainWindow.getInstance().getMediator().getNotationInfo().getAbbrevMap();
            }

            protected Term parseModifies(LocationVariable heap) throws Exception {
                Term result = null;
                index = inputPane.getSelectedIndex();
                // might throw parserException or some obscure
                // antlr
                result = parser.parse(
                        new StringReader(invariants.get(index)[MOD_IDX].get(heap.toString())), Sort.ANY,
                        services, services.getNamespaces(), getAbbrevMap());
                return result;
            }
            
            protected ImmutableList<Triple<ImmutableList<Term>,
                                           ImmutableList<Term>,
                                           ImmutableList<Term>>>
            parseRespects(LocationVariable heap) throws Exception {
                Term res = null;
                //ImmutableList<ImmutableList<Term>> result = null;
                index = inputPane.getSelectedIndex();
                // might throw parserException or some obscure
                // antlr                
                final String respAsString = invariants.get(index)[RSP_IDX].get(heap.toString());
                res = parser.parse(
                      new StringReader(respAsString), Sort.ANY,
                      services, services.getNamespaces(), getAbbrevMap());
                ImmutableList<Triple<ImmutableList<Term>,
                                     ImmutableList<Term>,
                                     ImmutableList<Term>>> result =
                    ImmutableSLList.<Triple<ImmutableList<Term>,
                                            ImmutableList<Term>,
                                            ImmutableList<Term>>>nil()
                                   .append(new Triple<ImmutableList<Term>,
                                                      ImmutableList<Term>,
                                                      ImmutableList<Term>>
                                   (ImmutableSLList.<Term>nil().append(res),
                                                      ImmutableSLList.<Term>nil(),
                                                      ImmutableSLList.<Term>nil()));
                return result;
            }

            protected Term parseVariant() throws Exception {
                Term result = null;
                index = inputPane.getSelectedIndex();
                // might throw parserException or some obscure
                // antlr
                result = parser.parse(
                        new StringReader(invariants.get(index)[VAR_IDX].get(DEFAULT)), Sort.ANY,
                        services, services.getNamespaces(), getAbbrevMap());
                return result;
            }

        }

        // Create the Dialog
        userPressedCancel = false;
        InvariantDialog dia = new InvariantDialog();
        dia.dispose();
        if(this.userPressedCancel) {
            throw new RuleAbortException("Interactive invariant configuration canceled by user.");
        }

        return newInvariant;
    }
}
