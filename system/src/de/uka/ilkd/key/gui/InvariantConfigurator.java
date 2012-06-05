package de.uka.ilkd.key.gui;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.StringReader;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;

import javax.swing.*;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import javax.swing.text.Document;

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.speclang.LoopInvariantImpl;

/**
 * @author Dreiner
 * 
 *         This class creates a Dialog to input a loop Invariant, Variant and
 *         Modifies.
 */
public class InvariantConfigurator {

    private static InvariantConfigurator configurator = null;
    private ArrayList<String[]> invariants = null;
    private HashMap<LoopStatement, ArrayList<String[]>> mapLoopsToInvariants = null;
    private int index = 0;
    private LoopInvariant newInvariant = null;
    private boolean userPressedCancel = false;

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
     * Creates a Dialog. User can enter Invariant, Variant and Modifies clause.
     * The Input is parsed and a new LoopInvariant is returned. In Case of a
     * parser Exception an error-message is shown.
     * 
     * @param loopInv
     * @param services
     * @param isTransaction 
     * @return LoopInvariant
     */
    public LoopInvariant getLoopInvariant (final LoopInvariant loopInv,
            final Services services, final boolean requiresVariant,
            final boolean isTransaction) throws RuleAbortException {
        // Check if there is a LoopInvariant
        if (loopInv == null) {
            return null;
        }

        index = 0;

        class InvariantDialog extends JDialog {

            private static final long serialVersionUID = 1L;

            private StringWriter sw = new StringWriter();
            private DefaultTermParser parser = new DefaultTermParser();
            
            
            //Creates a new Printer, pretty Syntax cannot be parsed up to now!
           /* private final LogicPrinter printer = new LogicPrinter(
                    new ProgramPrinter(sw), null, Main.getInstance().mediator()
                            .getServices());*/
            private JTabbedPane inputPane;
            private JPanel errorPanel;

            private Term invariantTerm = null;
            private Term variantTerm = null;
            private Term modifiesTerm = null;

            private final String INVARIANTTITLE = "Invariant: ";
            private final String VARIANTTITLE = "Variant: ";
            private final String MODIFIESTITLE = "Modifies: ";


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

                String[] loopInvStr = new String[3];
                
                final Map<LocationVariable,Term> atPres = loopInv.getInternalAtPres();
                if(!isTransaction) {
                  atPres.put(services.getTypeConverter().getHeapLDT().getSavedHeap(), null);
                } 
                final Term invariant = loopInv.getInvariant(loopInv.getInternalSelfTerm(), atPres, services, false);
                if (invariant == null) {
                    loopInvStr[0] = "true";
                } else {
                    loopInvStr[0] = printTerm(invariant, true);
                }

                // FIXME TODO !!! This should also deal with savedHeap and other heaps, if any
                final Term modifies = loopInv.getModifies(services.getTypeConverter().getHeapLDT().getHeap(), 
                        loopInv.getInternalSelfTerm(), atPres, services);
                
                if (modifies == null) {
                    loopInvStr[1] = "allLocs";
                } else {
                    // pretty syntax cannot be parsed yet for modifies
                    loopInvStr[1] = printTerm(modifies, false);
                }

                final Term variant = loopInv.getVariant(loopInv.getInternalSelfTerm(), atPres, services);
                if (variant == null) {
                    loopInvStr[2] = "";
                } else {                    
                    loopInvStr[2] = printTerm(variant, true);
                }

                if (!mapLoopsToInvariants.containsKey(loopInv.getLoop())) {
                    // add the given Invariant
                    invariants = new ArrayList<String[]>();
                    invariants.add(loopInvStr);
                    mapLoopsToInvariants.put(loopInv.getLoop(), invariants);
                    index = invariants.size() - 1;
                } else {
                    invariants = mapLoopsToInvariants.get(loopInv.getLoop());
                    // Check if the given invariant is in
                    // the list
                    if (!invariants.contains(loopInvStr)) {
                        invariants.add(loopInvStr);
                        index = invariants.size() - 1;
                    } else {
                        // set the index to the
                        // currently used invariant
                        index = invariants.indexOf(loopInvStr);
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

                JTextArea invarea = createInputTextArea(INVARIANTTITLE,
                        invariants.get(i)[0], i);
                JTextArea modarea = createInputTextArea(MODIFIESTITLE,
                        invariants.get(i)[1], i);
                JTextArea vararea = createInputTextArea(VARIANTTITLE,
                        invariants.get(i)[2], i);
                JTabbedPane p = new JTabbedPane(JTabbedPane.BOTTOM);
                p.add("Regular", invarea);
                p.add("Transaction", new JPanel());
                panel.add(p);
                JTabbedPane p2 = new JTabbedPane(JTabbedPane.BOTTOM);
                p2.add("heap", modarea);
                p2.add("savedHeap", new JPanel());
                p2.add("permissions", new JPanel());
                panel.add(p2);
                panel.add(vararea);

                JScrollPane rightPane = new JScrollPane(panel);;
                
                final int charXWidth = invarea.getFontMetrics(invarea.getFont()).charWidth('X');
                final int fontHeight = invarea.getFontMetrics(invarea.getFont()).getHeight();
                
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

                if (Title.equals(INVARIANTTITLE)) {
                    return setInvariantListener(inputTextArea, i);
                } else if (Title.equals(VARIANTTITLE)) {
                    return setVariantListener(inputTextArea, i);
                } else if (Title.equals(MODIFIESTITLE)) {
                    return setMoifiesListener(inputTextArea, i);
                } else {
                    return inputTextArea;
                }

            }

            private JTextArea setInvariantListener(JTextArea ta, int i) {
                index = i;
                ta.getDocument().addDocumentListener(new DocumentListener() {

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
                return ta;

            }

            private JTextArea setVariantListener(JTextArea ta, int i) {
                index = i;
                ta.getDocument().addDocumentListener(new DocumentListener() {

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
                return ta;

            }

            private JTextArea setMoifiesListener(JTextArea ta, int i) {
                index = i;
                ta.getDocument().addDocumentListener(new DocumentListener() {

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
                return ta;
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

            private JPanel createErrorPanel(String invMsg, Color invColor,
                    String modMsg, Color modColor, String varMsg, Color varColor) {
                JPanel panel = new JPanel();
                panel.setLayout(new BoxLayout(panel, BoxLayout.PAGE_AXIS));
                panel.add(createErrorTextField("Invariant - Status: ", invMsg,
                        invColor));
                panel.add(createErrorTextField("Modifies - Status: ", modMsg,
                        modColor));
                panel.add(createErrorTextField("Variant - Status", varMsg,
                        varColor));

                return panel;

            }

            private JPanel initErrorPanel() {
                return createErrorPanel("OK", Color.GREEN, "OK", Color.GREEN,
                        "OK", Color.GREEN);
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
                String[] invs = invariants.get(index).clone();
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
            private void invUdatePerformed(DocumentEvent d) {
                Document doc = d.getDocument();
                index = inputPane.getSelectedIndex();

                String[] inv = invariants.get(index);
                try {
                    inv[0] = doc.getText(0, doc.getLength());
                } catch (Exception e) {
                } finally {
                    parse();
                }
            }

            public void modUdatePerformed(DocumentEvent d) {
                Document doc = d.getDocument();
                index = inputPane.getSelectedIndex();

                String[] inv = invariants.get(index);
                try {
                    inv[1] = doc.getText(0, doc.getLength());
                } catch (Exception e) {
                } finally {
                    parse();
                }
            }

            public void varUdatePerformed(DocumentEvent d) {
                Document doc = d.getDocument();
                index = inputPane.getSelectedIndex();

                String[] inv = invariants.get(index);
                try {
                    inv[2] = doc.getText(0, doc.getLength());
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
                    updateErrorPanel(null, null, null, null,
                            "Variant is required!", Color.RED);
                    requirementsAreMet = false;
                }

                if (invariantTerm == null) {
                    requirementsAreMet = false;
                    updateErrorPanel("Invariant is required!", Color.RED, null,
                            null, null, null);
                }

                if (requirementsAreMet) {
                    Map<LocationVariable,Term> mods = new LinkedHashMap<LocationVariable,Term>();
                    mods.put(services.getTypeConverter().getHeapLDT().getHeap(), modifiesTerm);
                    newInvariant = new LoopInvariantImpl(loopInv.getLoop(),
                            invariantTerm, mods, variantTerm, loopInv
                                    .getInternalSelfTerm(), loopInv
                                    .getInternalAtPres());
                    return true;
                } else
                    return false;
            }

            /**
             * No Comment
             */
            private void parse() {
                String invError = "OK";
                Color invCol = Color.GREEN;
                try {
                    invariantTerm = parseInvariant();
                } catch (Exception e) {
                    invError = e.getMessage();
                    invCol = Color.RED;
                }
                String modError = "OK";
                Color modCol = Color.GREEN;
                try {
                    modifiesTerm = parseModifies();
                } catch (Exception e) {
                    modError = e.getMessage();
                    modCol = Color.RED;
                }
                String varError = "OK";
                Color varCol = Color.GREEN;

                try {
                    int i = inputPane.getSelectedIndex();
                    if (invariants.get(i)[2] == "") {
                        variantTerm = null;
                        if (requiresVariant) {
                            throw new Exception("Variant required!");
                        }
                    } else {
                        variantTerm = parseVariant();
                    }
                } catch (Exception e) {
                    varCol = Color.RED;
                    varError = e.getMessage();
                }

                updateErrorPanel(invError, invCol, modError, modCol, varError,
                        varCol);

            }

            private void updateErrorPanel(String invError, Color invCol,
                    String modError, Color modCol, String varError, Color varCol) {
                boolean reeinit = true;

                if (invError != null && invCol != null) {
                    JTextArea jta = (JTextArea) errorPanel.getComponent(0);
                    jta.setForeground(invCol);
                    jta.setText(invError);
                    reeinit = false;
                }
                if (modError != null && modCol != null) {
                    JTextArea jta = (JTextArea) errorPanel.getComponent(1);
                    jta.setForeground(modCol);
                    jta.setText(modError);
                    reeinit = false;
                }
                if (varError != null && varCol == null) {
                    JTextArea jta = (JTextArea) errorPanel.getComponent(2);
                    jta.setForeground(varCol);
                    jta.setText(varError);
                    reeinit = false;
                }
                if (!reeinit) {
                    Container con = errorPanel.getParent();
                    con.remove(errorPanel);
                    Dimension d = errorPanel.getPreferredSize();
                    errorPanel = createErrorPanel(invError, invCol, modError,
                            modCol, varError, varCol);
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
            protected Term parseInvariant() throws Exception {
                Term result = null;
                index = inputPane.getSelectedIndex();
                // might throw parserException
                
                
               result =  parser.parse(new StringReader(invariants.get(index)[0]), Sort.ANY, services, services.getNamespaces(),
                MainWindow.getInstance().getMediator().getNotationInfo().getAbbrevMap());

                return result;
            }

            protected Term parseModifies() throws Exception {
                Term result = null;
                index = inputPane.getSelectedIndex();
                // might throw parserException or some obscure
                // antlr
                result = parser.parse(
                        new StringReader(invariants.get(index)[1]), Sort.ANY,
                        services, services.getNamespaces(), MainWindow.getInstance().getMediator().getNotationInfo().getAbbrevMap());
                return result;
            }

            protected Term parseVariant() throws Exception {
                Term result = null;
                index = inputPane.getSelectedIndex();
                // might throw parserException or some obscure
                // antlr
                result = parser.parse(
                        new StringReader(invariants.get(index)[2]), Sort.ANY,
                        services, services.getNamespaces(), MainWindow.getInstance().getMediator().getNotationInfo().getAbbrevMap());
                return result;
            }

        }

        // Create the Dialog
        userPressedCancel = false;
        InvariantDialog dia = new InvariantDialog();
        dia.dispose();
        if(this.userPressedCancel) {
            throw new RuleAbortException("User did not provide Invariant. @InvariantConfigurator:683");
        }

        return newInvariant;
    }
}
