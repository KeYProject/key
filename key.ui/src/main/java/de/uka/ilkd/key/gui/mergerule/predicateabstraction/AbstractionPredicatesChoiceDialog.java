/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.mergerule.predicateabstraction;

import java.awt.*;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.util.*;
import java.util.List;
import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.table.AbstractTableModel;
import javax.swing.table.DefaultTableCellRenderer;
import javax.swing.table.TableCellEditor;
import javax.swing.table.TableCellRenderer;

import de.uka.ilkd.key.axiom_abstraction.AbstractDomainElement;
import de.uka.ilkd.key.axiom_abstraction.AbstractDomainLattice;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.*;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.mergerule.predicateabstraction.ObservableArrayList.ObservableArrayListChangeListener;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.io.OutputStreamProofSaver;
import de.uka.ilkd.key.rule.merge.procedures.MergeWithPredicateAbstraction;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * A Swing reimplementation of the (much nicer) JavaFX abstraction predicates choice dialog -- since
 * JavaFX got removed from Oracle Java.
 *
 * @author Dominic Steinhoefel
 */
public class AbstractionPredicatesChoiceDialog extends JDialog {
    private static final String AVAILABLE_PROGRAM_VARIABLES_DESCR = "Available Program Variables: ";
    private static final long serialVersionUID = 1L;
    private static final MainWindow MAIN_WINDOW_INSTANCE = //
        MainWindow.getInstance();

    /** The initial size of this dialog. */
    private static final Dimension INITIAL_SIZE = new Dimension(850, 600);

    private static final String DIALOG_TITLE = "Choose abstraction predicates for merge";
    private static final Logger LOGGER =
        LoggerFactory.getLogger(AbstractionPredicatesChoiceDialog.class);

    private Goal goal = null;

    private ArrayList<Pair<Sort, Name>> registeredPlaceholders = new ArrayList<>();
    private ArrayList<AbstractionPredicate> registeredPredicates = new ArrayList<>();
    private final ArrayList<AbstractDomainElemChoice> abstrPredicateChoices = new ArrayList<>();

    private Class<? extends AbstractPredicateAbstractionLattice> latticeType =
        SimplePredicateAbstractionLattice.class;

    private final ObservableArrayList<String> placeholdersProblemsListData =
        new ObservableArrayList<>();
    private final ObservableArrayList<String> abstrPredProblemsListData =
        new ObservableArrayList<>();

    /**
     * @return The abstraction predicates set by the user. Is null iff the user pressed cancel.
     */
    private ArrayList<AbstractionPredicate> getRegisteredPredicates() {
        return registeredPredicates;
    }

    /**
     * @return The chosen lattice type (class object for class that is an instance of
     *         {@link AbstractPredicateAbstractionLattice}).
     */
    private Class<? extends AbstractPredicateAbstractionLattice> getLatticeType() {
        return latticeType;
    }

    /**
     * @return The resulting input supplied by the user.
     */
    public Result getResult() {
        return new Result(getRegisteredPredicates(), getLatticeType(), abstrPredicateChoices);
    }

    /**
     * Constructs a new {@link AbstractionPredicatesChoiceDialog}. The given goal is used to get
     * information about the proof.
     *
     * @param goal The goal on which the merge rule is applied.
     * @param differingLocVars Location variables the values of which differ in the merge partner
     *        states.
     */
    public AbstractionPredicatesChoiceDialog(Goal goal, List<LocationVariable> differingLocVars) {
        this();
        this.goal = goal;
        differingLocVars.forEach(
            v -> abstrPredicateChoices.add(new AbstractDomainElemChoice(v, Optional.empty())));
    }

    /**
     * Constructs a new {@link AbstractionPredicatesChoiceDialog}.
     */
    private AbstractionPredicatesChoiceDialog() {
        super(MAIN_WINDOW_INSTANCE, DIALOG_TITLE, true);
        setSize(INITIAL_SIZE);
        setLocationRelativeTo(MAIN_WINDOW_INSTANCE);
        setDefaultCloseOperation(DISPOSE_ON_CLOSE);

        createDialog();
    }

    private void createDialog() {
        final JPanel infoPanel = createInfoPanel();

        final JTabbedPane stepsTabbedPane = new JTabbedPane();

        final JPanel latticeTypePanel = createLatticeTypePanel();
        final JPanel placeholdersPanel = createPlaceholderVariablesPanel();
        final JPanel abstrPredsPanel = createAbstractionPredicatesPanel();
        final JPanel choiceAbstrPredsPanel = createChoiceAbstrPredsPanel();

        stepsTabbedPane.add("(1) Lattice Type", latticeTypePanel);
        stepsTabbedPane.add("(2) Placeholder Variables", placeholdersPanel);
        stepsTabbedPane.add("(3) Abstraction Predicates", abstrPredsPanel);
        stepsTabbedPane.add("(4) Choice of Abstraction Predicates [opt]", choiceAbstrPredsPanel);

        final TitledBorder problemsPanelBorder = new TitledBorder("Problems");
        final JPanel problemsLabelContainer = createProblemsLabelContainer();
        problemsLabelContainer.setBorder(problemsPanelBorder);
        problemsLabelContainer.setPreferredSize(new Dimension(200, 250));

        final JSplitPane centerSplitPane = //
            new JSplitPane(JSplitPane.HORIZONTAL_SPLIT, stepsTabbedPane, problemsLabelContainer);
        centerSplitPane.setResizeWeight(1.0);
        centerSplitPane.setOneTouchExpandable(true);
        centerSplitPane.setDividerLocation(550);

        // Provide minimum sizes for the two components in the split pane
        final Dimension centerComponentsMinSize = new Dimension(200, 50);
        stepsTabbedPane.setMinimumSize(centerComponentsMinSize);
        problemsLabelContainer.setMinimumSize(centerComponentsMinSize);

        final JSplitPane rootSplitPane = //
            new JSplitPane(JSplitPane.VERTICAL_SPLIT, infoPanel, centerSplitPane);
        rootSplitPane.setResizeWeight(0.0);
        rootSplitPane.setOneTouchExpandable(true);
        rootSplitPane.setDividerLocation(220);

        final JPanel controlsPanel = new JPanel(new FlowLayout());
        final JButton cancelButton = new JButton("Cancel");
        cancelButton.addActionListener(e -> {
            registeredPlaceholders = null;
            registeredPredicates = null;
            setVisible(false);
            dispose();
        });
        final JButton okButton = new JButton("OK");
        okButton.addActionListener(e -> {
            setVisible(false);
            dispose();
        });
        controlsPanel.add(cancelButton);
        controlsPanel.add(okButton);

        final JPanel rootPane = new JPanel(new BorderLayout());
        rootPane.add(rootSplitPane, BorderLayout.CENTER);
        rootPane.add(controlsPanel, BorderLayout.SOUTH);

        getContentPane().add(rootPane);
    }

    private JPanel createChoiceAbstrPredsPanel() {
        final JPanel result = new JPanel(new BorderLayout());

        final ChoiceTableModel model = new ChoiceTableModel();
        final JTable choiceTable = new DomElemChoiceTable(model);
        choiceTable.setFillsViewportHeight(true);

        final JScrollPane scrollPane = new JScrollPane(choiceTable);
        result.add(scrollPane, BorderLayout.CENTER);
        return result;
    }

    private JPanel createProblemsLabelContainer() {
        final JPanel result = new JPanel(new BorderLayout());

        final String resourcePath = "/de/uka/ilkd/key/gui/";
        final String stylesheet =
            readFromResourceFile(resourcePath + "css/abstrPredsMergeDialog.css");

        final JTextPane problemsTxtPane = new JTextPane();
        problemsTxtPane.setContentType("text/html");

        final ObservableArrayListChangeListener listener = () -> {
            final StringBuilder sb = new StringBuilder();
            sb.append("<html><head>");
            sb.append("<style type=\"text/css\">");
            sb.append(stylesheet);
            sb.append("</style>");

            if (!placeholdersProblemsListData.isEmpty()) {
                sb.append("<h3>Placeholder Variables</h3>");
                sb.append("<table>");
                for (String problem : placeholdersProblemsListData) {
                    sb.append("<tr><td>") //
                            .append(problem) //
                            .append("</td></tr>");
                }
                sb.append("</table>");
            }

            if (!abstrPredProblemsListData.isEmpty()) {
                sb.append("<h3>Abstraction Predicates</h3>");
                sb.append("<table>");
                for (String problem : abstrPredProblemsListData) {
                    sb.append("<tr><td>") //
                            .append(problem) //
                            .append("</td></tr>");
                }
                sb.append("</table>");
            }

            sb.append("</head><body>");
            sb.append("</body></html>");
            problemsTxtPane.setText(sb.toString());
        };

        placeholdersProblemsListData.addListener(listener);
        abstrPredProblemsListData.addListener(listener);

        final JScrollPane scrollPane = new JScrollPane(problemsTxtPane,
            JScrollPane.VERTICAL_SCROLLBAR_ALWAYS, JScrollPane.HORIZONTAL_SCROLLBAR_NEVER);
        scrollPane.setPreferredSize(new Dimension(INITIAL_SIZE.width, 200));
        result.add(scrollPane, BorderLayout.CENTER);

        return result;
    }

    private JPanel createPlaceholderVariablesPanel() {
        final JPanel result = new JPanel(new BorderLayout());

        final JTextField txtPlaceholderInput = new JTextField();
        txtPlaceholderInput.setToolTipText("Enter a new placeholder variable (e.g., \"int _ph1\")");
        txtPlaceholderInput.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 12));

        result.add(txtPlaceholderInput, BorderLayout.NORTH);

        final DefaultListModel<String> placeholdersLstModel = new DefaultListModel<>();
        final JList<String> lstPlaceholders = new JList<>(placeholdersLstModel);
        lstPlaceholders.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
        lstPlaceholders.setLayoutOrientation(JList.VERTICAL);
        lstPlaceholders.setVisibleRowCount(-1);
        lstPlaceholders.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 12));

        final JScrollPane sp = new JScrollPane(lstPlaceholders);
        result.add(sp, BorderLayout.CENTER);

        txtPlaceholderInput.addKeyListener(new KeyAdapter() {
            @Override
            public void keyReleased(KeyEvent evt) {
                final String currInput = txtPlaceholderInput.getText();

                if (currInput.isEmpty()) {
                    placeholdersProblemsListData.clear();
                    return;
                }

                try {
                    parsePlaceholder(currInput);
                    placeholdersProblemsListData.clear();
                } catch (Exception e) {
                    placeholdersProblemsListData.clear();
                    placeholdersProblemsListData.add(e.getMessage());
                    LOGGER.error("Exception!", e);
                }
            }
        });

        txtPlaceholderInput.addActionListener(e -> {
            final String currInput = txtPlaceholderInput.getText();
            if (placeholdersProblemsListData.isEmpty() && !currInput.isEmpty()) {
                placeholdersLstModel.addElement(currInput);
                txtPlaceholderInput.setText("");

                final Pair<Sort, Name> parsed = parsePlaceholder(currInput);
                registeredPlaceholders.add(parsed);
                final Namespace<IProgramVariable> pvs =
                    goal.proof().getServices().getNamespaces().programVariables();
                pvs.add(new LocationVariable(new ProgramElementName(parsed.second.toString()),
                    parsed.first));
            }
        });

        lstPlaceholders.addKeyListener(new KeyAdapter() {
            @Override
            public void keyReleased(KeyEvent e) {
                final int selectedIndex = lstPlaceholders.getSelectedIndex();
                if (e.getKeyCode() == KeyEvent.VK_DELETE && !placeholdersLstModel.isEmpty()
                        && selectedIndex >= 0) {
                    placeholdersLstModel.remove(selectedIndex);
                    final Pair<Sort, Name> removedPlaceholder =
                        registeredPlaceholders.remove(selectedIndex);
                    final Namespace<IProgramVariable> pvs =
                        goal.proof().getServices().getNamespaces().programVariables();
                    pvs.remove(removedPlaceholder.second);
                }
            }
        });

        return result;
    }

    private JPanel createAbstractionPredicatesPanel() {
        final JPanel result = new JPanel(new BorderLayout());

        final JTextField txtAbstrPredInput = new JTextField();
        txtAbstrPredInput.setToolTipText("Enter a new predicate (e.g., \"_ph1 > 0\").");
        txtAbstrPredInput.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 12));

        result.add(txtAbstrPredInput, BorderLayout.NORTH);

        final DefaultListModel<String> abstrPredListModel = new DefaultListModel<>();
        final JList<String> lstAbstrPreds = new JList<>(abstrPredListModel);
        lstAbstrPreds.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
        lstAbstrPreds.setLayoutOrientation(JList.VERTICAL);
        lstAbstrPreds.setVisibleRowCount(-1);
        lstAbstrPreds.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 12));

        final JScrollPane sp = new JScrollPane(lstAbstrPreds);
        result.add(sp, BorderLayout.CENTER);

        // Goal will only be null in test run
        if (goal != null) {
            String progVarsStr = goal.node().getLocalProgVars().toString().replace(",", ", ");
            progVarsStr = progVarsStr.substring(1, progVarsStr.length() - 1);

            final JLabel lblAvailableProgVars =
                new JLabel(AVAILABLE_PROGRAM_VARIABLES_DESCR + progVarsStr);
            result.add(lblAvailableProgVars, BorderLayout.SOUTH);
            lblAvailableProgVars.setFont(new Font(Font.SANS_SERIF, Font.PLAIN, 12));
        }

        txtAbstrPredInput.addKeyListener(new KeyAdapter() {
            @Override
            public void keyReleased(KeyEvent evt) {
                final String currInput = txtAbstrPredInput.getText();

                if (currInput.isEmpty()) {
                    abstrPredProblemsListData.clear();
                    return;
                }

                try {
                    final AbstractionPredicate pred =
                        parsePredicate(currInput, goal.getLocalNamespaces());
                    abstrPredProblemsListData.clear();

                    if (registeredPredicates.contains(pred)) {
                        abstrPredProblemsListData.add("Predicate is already registered");
                    }
                } catch (Exception e) {
                    abstrPredProblemsListData.clear();
                    abstrPredProblemsListData.add(e.getMessage());
                    LOGGER.error("Exception!", e);
                }
            }
        });

        txtAbstrPredInput.addActionListener(e -> {
            final String currInput = txtAbstrPredInput.getText();
            if (abstrPredProblemsListData.isEmpty() && !currInput.isEmpty()) {
                abstrPredListModel.addElement(currInput);
                txtAbstrPredInput.setText("");

                AbstractionPredicate parsed;
                try {
                    parsed = parsePredicate(currInput, goal.getLocalNamespaces());
                } catch (Exception exc) {
                    throw new RuntimeException(exc);
                }

                registeredPredicates.add(parsed);
            }
        });

        lstAbstrPreds.addKeyListener(new KeyAdapter() {
            @Override
            public void keyReleased(KeyEvent e) {
                final int selectedIndex = lstAbstrPreds.getSelectedIndex();
                if (e.getKeyCode() == KeyEvent.VK_DELETE && !abstrPredListModel.isEmpty()
                        && selectedIndex >= 0) {
                    abstrPredListModel.remove(selectedIndex);
                    registeredPredicates.remove(selectedIndex);
                }
            }
        });

        return result;
    }

    private JPanel createLatticeTypePanel() {
        final JRadioButton simplePredLatticeBtn = new JRadioButton("Simple Predicates Lattice");
        simplePredLatticeBtn
                .addActionListener(e -> latticeType = SimplePredicateAbstractionLattice.class);
        final JRadioButton conjPredLatticeBtn = new JRadioButton("Conjunctive Predicates Lattice");
        conjPredLatticeBtn
                .addActionListener(e -> latticeType = ConjunctivePredicateAbstractionLattice.class);
        final JRadioButton disjPredLatticeBtn = new JRadioButton("Disjunctive Predicates Lattice");
        disjPredLatticeBtn
                .addActionListener(e -> latticeType = DisjunctivePredicateAbstractionLattice.class);

        final ButtonGroup latticeTypeBtnGroup = new ButtonGroup();
        latticeTypeBtnGroup.add(simplePredLatticeBtn);
        latticeTypeBtnGroup.add(conjPredLatticeBtn);
        latticeTypeBtnGroup.add(disjPredLatticeBtn);
        simplePredLatticeBtn.setSelected(true);

        final JPanel result = new JPanel();
        result.setLayout(new BoxLayout(result, BoxLayout.Y_AXIS));

        result.add(simplePredLatticeBtn);
        result.add(conjPredLatticeBtn);
        result.add(disjPredLatticeBtn);

        return result;
    }

    private JPanel createInfoPanel() {
        final String resourcePath = "/de/uka/ilkd/key/gui/";
        final String infoHTML =
            readFromResourceFile(resourcePath + "help/abstrPredsMergeDialogInfo.html");
        final String infoCSS = readFromResourceFile(resourcePath + "css/abstrPredsMergeDialog.css");

        assert infoHTML != null && infoCSS != null : //
                "Could not find css/html resources for the abstraction predicates choice dialog.";

        String sb = "<html><head>" + "<style type=\"text/css\">" + infoCSS + "</style>"
            + "</head><body>" + infoHTML + "</body></html>";

        final JTextPane infoLabel = new JTextPane();
        infoLabel.setContentType("text/html");
        infoLabel.setText(sb);

        final TitledBorder infoLabelBorder =
            new TitledBorder("Information on Merges with Predicate Abstraction");
        final JPanel infoLabelContainer = new JPanel(new BorderLayout());
        infoLabelContainer.setBorder(infoLabelBorder);

        final JScrollPane scrollPane = new JScrollPane(infoLabel,
            JScrollPane.VERTICAL_SCROLLBAR_ALWAYS, JScrollPane.HORIZONTAL_SCROLLBAR_NEVER);
        scrollPane.setPreferredSize(new Dimension(INITIAL_SIZE.width, 200));
        infoLabelContainer.add(scrollPane, BorderLayout.CENTER);

        return infoLabelContainer;
    }

    /**
     * Parses a placeholder using {@link MergeRuleUtils#parsePlaceholder(String, Services)}.
     *
     * @param input The input to parse.
     * @return The parsed placeholder (sort and name).
     */
    private Pair<Sort, Name> parsePlaceholder(String input) {
        return MergeRuleUtils.parsePlaceholder(input, goal.proof().getServices());
    }

    /**
     * Parses an abstraction predicate using
     * {@link MergeRuleUtils#parsePredicate(String, ArrayList, NamespaceSet, Services)}.
     *
     * @param input The input to parse.
     * @param localNamespaces The local {@link NamespaceSet}.
     * @return The parsed abstraction predicate.
     * @throws ParserException If there is a mistake in the input.
     */
    private AbstractionPredicate parsePredicate(String input, NamespaceSet localNamespaces)
            throws ParserException {
        return MergeRuleUtils.parsePredicate(input, registeredPlaceholders, localNamespaces,
            goal.proof().getServices());
    }

    /**
     * A String representation of an abstraction predicate, that is a "pair" expression of the
     * placeholder variable and the predicate term of the form "(PROGVAR,PREDTERM)".
     *
     * @param domElem The abstraction predicate to convert into a String representation.
     * @return A String representation of the given abstraction predicate.
     */
    private String abstrPredToStringRepr(
            Optional<AbstractPredicateAbstractionDomainElement> domElem) {
        if (domElem == null) {
            return "";
        }

        if (!domElem.isPresent()) {
            return "None.";
        }

        final AbstractPredicateAbstractionDomainElement predElem = domElem.get();

        if (predElem.getPredicates().size() < 1) {
            return predElem.toString();
        }

        final StringBuilder sb = new StringBuilder();

        final Iterator<AbstractionPredicate> it = //
            predElem.getPredicates().iterator();

        while (it.hasNext()) {
            sb.append(abstrPredToString(it.next()));

            if (it.hasNext()) {
                sb.append(predElem.getPredicateNameCombinationString());
            }
        }

        return sb.toString();
    }

    /**
     * Returns a String representation of an abstraction predicate.
     *
     * @param pred Predicate to compute a String representation for.
     * @return A String representation of an abstraction predicate.
     */
    private String abstrPredToString(AbstractionPredicate pred) {
        final Services services = MainWindow.getInstance().getMediator().getServices();
        final Pair<LocationVariable, Term> predFormWithPh = pred.getPredicateFormWithPlaceholder();

        return "(" + predFormWithPh.first.toString() + ","
            + OutputStreamProofSaver.printAnything(predFormWithPh.second, services) + ")";
    }

    // ///////////////////////////// //
    // /////// STATIC METHODS ////// //
    // ///////////////////////////// //

    private static URL getURLForResourceFile(Class<?> cl, String filename) {
        URL url = cl.getResource(filename);
        LOGGER.debug("Load Resource:" + filename + " of class " + cl);
        if (url == null && cl.getSuperclass() != null) {
            return getURLForResourceFile(cl.getSuperclass(), filename);
        } else if (url == null && cl.getSuperclass() == null) {
            // error message Resource not found
            LOGGER.error("No resource {} found", filename);
            return null;
        } else {
            LOGGER.debug("Done.");
            return url;
        }
    }

    private static String readFromURL(URL url) {
        try (final InputStream is = url.openStream();
                final Scanner s = new Scanner(is, StandardCharsets.UTF_8)) {
            return s.useDelimiter("\\A").next();
        } catch (IOException e) {
            return null;
        }
    }

    private static String readFromResourceFile(String filename) {
        return readFromURL(
            getURLForResourceFile(AbstractionPredicatesChoiceDialog.class, filename));
    }

    /**
     * Encapsulates the results supplied by the user.
     *
     * @author Dominic Steinhoefel
     */
    static class Result {
        private final ArrayList<AbstractionPredicate> registeredPredicates;
        private final Class<? extends AbstractPredicateAbstractionLattice> latticeType;
        private final LinkedHashMap<ProgramVariable, AbstractDomainElement> abstractDomElemUserChoices =
            new LinkedHashMap<>();

        public Result(ArrayList<AbstractionPredicate> registeredPredicates,
                Class<? extends AbstractPredicateAbstractionLattice> latticeType,
                List<AbstractDomainElemChoice> userChoices) {
            this.registeredPredicates = registeredPredicates;
            this.latticeType = latticeType;

            userChoices.forEach(choice -> {
                if (choice.isChoiceMade()) {
                    abstractDomElemUserChoices.put(choice.getProgVar(),
                        choice.getAbstrDomElem().get());
                }
            });
        }

        /**
         * @return The abstraction predicates set by the user. Is null iff the user pressed cancel.
         */
        public ArrayList<AbstractionPredicate> getRegisteredPredicates() {
            return registeredPredicates;
        }

        /**
         * @return The chosen lattice type (class object for class that is an instance of
         *         {@link AbstractPredicateAbstractionLattice}).
         */
        public Class<? extends AbstractPredicateAbstractionLattice> getLatticeType() {
            return latticeType;
        }

        /**
         * @return Manually chosen lattice elements for program variables.
         */
        public LinkedHashMap<ProgramVariable, AbstractDomainElement> getAbstractDomElemUserChoices() {
            return abstractDomElemUserChoices;
        }
    }

    class DomElemChoiceTable extends JTable {
        private static final long serialVersionUID = 1L;

        public DomElemChoiceTable(ChoiceTableModel model) {
            super(model);
        }

        @Override
        public TableCellEditor getCellEditor(int row, int column) {
            if (column != 1) {
                return super.getCellEditor(row, column);
            }

            final Sort s = abstrPredicateChoices.get(row).getProgVar().sort();

            final AbstractDomainLattice lattice =
                new MergeWithPredicateAbstraction(registeredPredicates, latticeType,
                    new LinkedHashMap<>()).getAbstractDomainForSort(s,
                        MainWindow.getInstance().getMediator().getServices());

            // Set all options, including a default one.

            final JComboBox<Optional<AbstractPredicateAbstractionDomainElement>> items = //
                new JComboBox<>();
            items.setRenderer(new DefaultListCellRenderer() {
                private static final long serialVersionUID = 1L;

                @SuppressWarnings("unchecked")
                @Override
                public Component getListCellRendererComponent(JList<?> list, Object value,
                        int index, boolean isSelected, boolean cellHasFocus) {
                    final DefaultListCellRenderer result = //
                        (DefaultListCellRenderer) super.getListCellRendererComponent(list, value,
                            index, isSelected, cellHasFocus);
                    result.setText(abstrPredToStringRepr(
                        (Optional<AbstractPredicateAbstractionDomainElement>) value));
                    return result;
                }
            });

            items.addItem(Optional.empty());

            if (lattice != null) {
                for (AbstractDomainElement abstractDomainElement : lattice) {
                    items.addItem(
                        Optional.of(
                            (AbstractPredicateAbstractionDomainElement) abstractDomainElement));
                }
            }

            return new DefaultCellEditor(items);
        }

        @Override
        public TableCellRenderer getCellRenderer(int row, int column) {
            if (column != 1) {
                return super.getCellRenderer(row, column);
            }

            return new DefaultTableCellRenderer() {
                private static final long serialVersionUID = 1L;

                @Override
                public Component getTableCellRendererComponent(JTable table, Object value,
                        boolean isSelected, boolean hasFocus, int row, int column) {
                    final DefaultTableCellRenderer result = //
                        (DefaultTableCellRenderer) super.getTableCellRendererComponent(table, value,
                            isSelected, hasFocus, row, column);
                    @SuppressWarnings("unchecked")
                    final Optional<AbstractPredicateAbstractionDomainElement> maybeDomElem = //
                        (Optional<AbstractPredicateAbstractionDomainElement>) value;
                    result.setText(abstrPredToStringRepr(maybeDomElem));
                    return result;
                }
            };
        }
    }

    private class ChoiceTableModel extends AbstractTableModel {
        private static final long serialVersionUID = 1L;

        @Override
        public int getRowCount() {
            return abstrPredicateChoices.size();
        }

        @Override
        public int getColumnCount() {
            return 2;
        }

        @Override
        public String getColumnName(int column) {
            if (column == 0) {
                return "Program Variable";
            } else if (column == 1) {
                return "Domain Element";
            } else {
                throw new IllegalArgumentException();
            }
        }

        @Override
        public Object getValueAt(int rowIndex, int columnIndex) {
            final AbstractDomainElemChoice row = abstrPredicateChoices.get(rowIndex);
            return columnIndex == 0
                    ? row.getProgVar().sort() + " " + row.getProgVar().name().toString()
                    : row.getAbstrDomElem();
        }

        @SuppressWarnings("unchecked")
        @Override
        public void setValueAt(Object aValue, int rowIndex, int columnIndex) {
            assert columnIndex == 2;
            assert aValue instanceof Optional;

            abstrPredicateChoices.get(rowIndex)
                    .setAbstrDomElem((Optional<AbstractPredicateAbstractionDomainElement>) aValue);
        }

        @Override
        public boolean isCellEditable(int rowIndex, int columnIndex) {
            return columnIndex == 1;
        }

    }

    // ////////////////////////////////////// //
    // //////////// TEST METHODS //////////// //
    // ////////////////////////////////////// //

    public static void main(String[] args) {
        final de.uka.ilkd.key.proof.Proof proof = loadProof("firstTouch/01-Agatha/project.key");

        final ArrayList<LocationVariable> differingLocVars = new ArrayList<>();
        differingLocVars.add(new LocationVariable(new ProgramElementName("test"),
            proof.getServices().getNamespaces().sorts().lookup("int")));
        differingLocVars.add(new LocationVariable(new ProgramElementName("test1"),
            proof.getServices().getNamespaces().sorts().lookup("boolean")));

        final AbstractionPredicatesChoiceDialog dialog = //
            new AbstractionPredicatesChoiceDialog(proof.openGoals().head(), differingLocVars);

        dialog.setVisible(true);
    }

    /**
     * Loads the given proof file. Checks if the proof file exists and the proof is not null, and
     * fails if the proof could not be loaded.
     *
     * @param proofFileName The file name of the proof file to load.
     * @return The loaded proof.
     */
    static de.uka.ilkd.key.proof.Proof loadProof(String proofFileName) {
        java.io.File proofFile = new java.io.File("examples/" + proofFileName);

        try {
            de.uka.ilkd.key.control.KeYEnvironment<?> environment =
                de.uka.ilkd.key.control.KeYEnvironment.load(
                    de.uka.ilkd.key.proof.init.JavaProfile.getDefaultInstance(), proofFile, null,
                    null, null, true);

            return environment.getLoadedProof();
        } catch (de.uka.ilkd.key.proof.io.ProblemLoaderException e) {
            return null;
        }
    }
}
