/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.InfoView.InfoNodeFactory.InfoTreeNode;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.extension.impl.KeYGuiExtensionFacade;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.logic.DocSpace;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.event.ProofDisposedListener;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.ThreadUtilities;
import org.key_project.logic.Choice;
import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.logic.op.Function;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.rules.RuleApp;
import org.key_project.util.collection.ImmutableList;

import javax.swing.*;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.MutableTreeNode;
import java.awt.event.ComponentEvent;
import java.awt.event.ComponentListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.util.*;
import java.util.function.Supplier;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Class for info contents displayed in {@link MainWindow}.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class InfoView extends JSplitPane implements TabPanel {
    public static final Icon INFO_ICON =
            IconFactory.INFO_VIEW.get(MainWindow.TAB_ICON_SIZE);

    private final JTree infoTree = new JTree();
    private final JTextArea contentPane = createInfoArea();
    private final ProofDisposedListener proofDisposedListener;
    private final InfoNodeFactory nodeFactory = new InfoNodeFactory();

    private final KeYSelectionListener selectionListener = new KeYSelectionListener() {
        public void selectedProofChanged(KeYSelectionEvent<Proof> e) {
            ThreadUtilities.invokeOnEventQueue(() -> {
                if (mediator.getSelectedGoal() != null) {
                    updateModel(mediator.getSelectedGoal());
                }
                if (mediator.getSelectedProof() != null) {
                    updateModel(mediator.getSelectedProof().openGoals().head());
                }
            });
        }
    };

    private Node lastShownGoalNode;
    private KeYMediator mediator;

    public InfoView(MainWindow window, KeYMediator mediator) {
        super(VERTICAL_SPLIT);

        setMainWindow(window);
        setMediator(mediator);

        // initial placement of the divider
        setDividerLocation(300);

        // growing goes to the upper half only
        setResizeWeight(1.0);

        // Setting a name for this causes PreferenceSaver to include this class.
        setName("infoViewPane");


        DefaultMutableTreeNode root = new DefaultMutableTreeNode();
        root.add(nodeFactory.create("No proof loaded", "In this pane, the available logical rules will be displayed and/or explained."));
        infoTree.setModel(new DefaultTreeModel(root));
        infoTree.setShowsRootHandles(true);
        infoTree.setRootVisible(false);

        lastShownGoalNode = null;

        addComponentListener(new ComponentListener() {
            @Override
            public void componentShown(ComponentEvent e) {
                if (mediator.getSelectedProof() != null) {
                    Goal goal = mediator.getSelectedGoal();
                    if (goal != null) {
                        updateModel(mediator.getSelectedGoal());
                    }
                }
            }

            @Override
            public void componentResized(ComponentEvent e) {
            }

            @Override
            public void componentMoved(ComponentEvent e) {
            }

            @Override
            public void componentHidden(ComponentEvent e) {
            }
        });

        proofDisposedListener = new ProofDisposedListener() {
            @Override
            public void proofDisposing(ProofDisposedEvent e) {
            }

            @Override
            public void proofDisposed(ProofDisposedEvent e) {
                updateModel(null);
            }
        };

        infoTree.addMouseListener(new MouseAdapter() {
            public void mouseClicked(MouseEvent e) {
                checkPopup(e);
            }

            @Override
            public void mousePressed(MouseEvent e) {
                checkPopup(e);
            }

            private void checkPopup(MouseEvent e) {
                /*
                if (e.isPopupTrigger()) {
                    Rule selected = ((InfoTreeNode) infoTree.getLastSelectedPathComponent()).getRule();
                    JPopupMenu menu = KeYGuiExtensionFacade.createContextMenu(
                            DefaultContextMenuKind.TACLET_INFO, selected, mediator);
                    if (menu.getComponentCount() > 0) {
                        menu.show(InfoView.this, e.getX(), e.getY());
                    }
                }*/
            }
        });

        infoTree.addTreeSelectionListener(e -> {
            InfoTreeNode node = (InfoTreeNode) infoTree.getLastSelectedPathComponent();
            if (node != null) {
                contentPane.setText(node.getDescription());
            } else {
                contentPane.setText("");
            }
        });

        setLeftComponent(new JScrollPane(infoTree));
        setRightComponent(new JScrollPane(contentPane));

        KeYGuiExtensionFacade.installKeyboardShortcuts(mediator, this,
                KeYGuiExtension.KeyboardShortcuts.INFO_VIEW);
    }


    public void setMediator(KeYMediator m) {
        if (mediator != null) {
            mediator.removeKeYSelectionListener(selectionListener);
        }
        m.addKeYSelectionListener(selectionListener);
        mediator = m;
    }

    public void setMainWindow(MainWindow w) {
    }

    @Override
    public String getTitle() {
        return "Info";
    }

    @Override
    public Icon getIcon() {
        return INFO_ICON;
    }

    @Override
    public JComponent getComponent() {
        return this;
    }

    private void updateModel(Goal g) {
        if (g == null || lastShownGoalNode != g.node()) {
            if (lastShownGoalNode != null) {
                lastShownGoalNode.proof().removeProofDisposedListener(proofDisposedListener);
            }
            if (g != null) {
                infoTree.setModel(new DefaultTreeModel(nodeFactory.createInfoTreeRoot(g)));
                g.proof().addProofDisposedListener(proofDisposedListener);
                lastShownGoalNode = g.node();
            } else {
                infoTree.setModel(null);
                lastShownGoalNode = null;
            }
            contentPane.setText("");
        }
    }

    private JTextArea createInfoArea() {
        JTextArea description = new JTextArea("", 15, 30);
        description.setEditable(false);
        description.setLineWrap(true);
        description.setWrapStyleWord(true);
        description.setBorder(BorderFactory.createTitledBorder(""));
        description.setCaretPosition(0);
        return description;
    }


    public static class InfoNodeFactory {
        private static final String LEMMAS = "Lemmas";
        private static final String TACLET_BASE = "Taclet Base";

        private static final String COLLECTION =
                "This node stands for a category of symbols; expand it to browse the symbols "
                        + "in the category.";
        private static final String DEFAULT_FUNCTIONS_LABEL =
                "Display descriptions for documented interpreted function and predicate symbols.";


        private DefaultMutableTreeNode createInfoTreeRoot(Goal g) {
            InfoTreeNode root = new InfoTreeNode(
                    "This is the root node of InfoTreeModel. It should not be visible.", null);

            DocSpace docs = g.proof().getServices().getNamespaces().docs();

            root.add(createNodeRules(docs, g));
            root.add(createNodeTermLabels(docs, g.proof()));
            root.add(createNodeFunctions(docs, g.proof().getNamespaces().functions()));
            root.add(createNodeTacletOptions(docs, g.proof().getInitConfig()));
            return root;
        }

        private InfoTreeNode createNodeRules(DocSpace docs, Goal g) {
            var tlRoot = create("Rules", "Browse descriptions for currently available rules.");

            List<NoPosTacletApp> set = new ArrayList<>(g.ruleAppIndex().tacletIndex().allNoPosTacletApps());
            OneStepSimplifier simplifier = MiscTools.findOneStepSimplifier(g.proof());
            if (simplifier != null && !simplifier.isShutdown()) {
                set.addAll(simplifier.getCapturedTaclets());
            }
            set.sort(Comparator.comparing(RuleApp::displayName));

            tlRoot.add(createNodeBuiltInRules(docs, g));
            tlRoot.add(createNodeAxiom(docs,
                    set.stream().filter(it -> {
                        RuleJustification just = g.proof().mgt().getJustification(it);
                        return just != null && just.isAxiomJustification();
                    })));

            tlRoot.add(createNodeLemmas(docs, set.stream().filter(it -> {
                RuleJustification just = g.proof().mgt().getJustification(it);
                return just != null && !just.isAxiomJustification();
            })));

            return tlRoot;
        }

        private MutableTreeNode createNodeBuiltInRules(DocSpace docs, Goal g) {
            InfoTreeNode builtInRoot = create("Built-In",
                    "Some logical rules are implemented in Java code. This is because their semantics " +
                            "cannot easily be expressed in KeY's Taclet language.");
            ImmutableList<BuiltInRule> rules = g.ruleAppIndex().builtInRuleAppIndex().builtInRuleIndex().rules();
            for (BuiltInRule br : rules) {
                builtInRoot.add(create(br, docs));
            }
            return builtInRoot;
        }

        private MutableTreeNode createNodeAxiom(DocSpace docs, Stream<NoPosTacletApp> seq) {
            InfoTreeNode axiomTacletRoot = create(TACLET_BASE, """
                    Most logical rules are implemented as Taclets.
                    
                    Taclets are schematic logical rules formulated in the Taclet Language.\s
                    The language is defined and explained in the KeY book.
                    """);
            seq.forEach(it -> axiomTacletRoot.add(create(it.rule(), docs)));
            return axiomTacletRoot;
        }

        private MutableTreeNode createNodeLemmas(DocSpace docs, Stream<NoPosTacletApp> seq) {
            InfoTreeNode proveableTacletsRoot = create(LEMMAS, """
                    Taclets which have been introduced using File->Load User-Defined Taclets are filed here.
                    
                    Loading User Defined Taclets opens side branches on which the soundness of the lemma taclets must be established.
                    """);
            seq.forEach(it -> proveableTacletsRoot.add(create(it.rule(), docs)));
            return proveableTacletsRoot;
        }

        private MutableTreeNode createNodeTermLabels(DocSpace docs, Proof proof) {
            var tlRoot = create("Term Labels", "Show descriptions for currently available term labels.");
            var mgr = TermLabelManager.getTermLabelManager(proof.getServices());
            var factories = mgr.getFactories();

            var labelNames = new ArrayList<>(factories.keySet());
            labelNames.sort(Comparator.comparing(Name::toString));

            for (Name name : labelNames) {
                tlRoot.add(new InfoTreeNode(name.toString(), () ->
                        factories.get(name).getDocumentation()
                ));
            }
            return tlRoot;
        }

        private InfoTreeNode createNodeFunctions(DocSpace docs, Namespace<Function> functions) {
            var fnRoot = create("Function Symbols", DEFAULT_FUNCTIONS_LABEL);
            var fnByName = create("By Name", DEFAULT_FUNCTIONS_LABEL);
            var fnByReturnType = create("By Return Type", DEFAULT_FUNCTIONS_LABEL);

            fnRoot.add(fnByName);
            fnRoot.add(fnByReturnType);

            var seq = new ArrayList<>(functions.allElements());
            seq.sort(Comparator.comparing(it -> it.name().toString()));

            var byReturn = new TreeMap<Sort, List<InfoTreeNode>>(
                    Comparator.comparing(it -> it.name().toString())
            );

            for (var fn : seq) {
                var fnName = fn.name().toString();
                var fnSort = fn.sort();

                // flat list:
                Supplier<String> stringSupplier = () -> docs.find(fn);
                fnByName.add(new InfoTreeNode(fnName, stringSupplier));

                // by return type
                byReturn.putIfAbsent(fnSort, new ArrayList<>());
                byReturn.get(fnSort).add(new InfoTreeNode(fnName, stringSupplier));
            }

            for (var entry : byReturn.entrySet()) {
                var node = create(entry.getKey().name().toString(), "");
                entry.getValue().forEach(node::add);
                fnByReturnType.add(node);
            }

            return fnRoot;
        }

        private InfoTreeNode createNodeTacletOptions(DocSpace docs, InitConfig initConfig) {
            InfoTreeNode localRoot = create("Active Taclet Options", "Shows the activated Taclet options");
            for (Choice activatedChoice : initConfig.getActivatedChoices()) {
                localRoot.add(
                        create(activatedChoice.name().toString(),
                                docs.find(activatedChoice)));
            }
            return localRoot;
        }


        public InfoTreeNode create(Taclet taclet, DocSpace docs) {
            var node = new InfoTreeNode(taclet.displayName(), null);
            LogicPrinter lp = LogicPrinter.purePrinter(new NotationInfo(), null);
            lp.printTaclet(taclet);
            return new InfoTreeNode(taclet.displayName(),
                    () -> Stream.of(docs.find(taclet), lp.result(),
                                    "Defined at:" + taclet.getOrigin() + "under options:" + taclet.getChoices())
                            .filter(Objects::nonNull)
                            .collect(Collectors.joining("\n\n")));
        }

        public InfoTreeNode create(BuiltInRule br, DocSpace docs) {
            var description = "Defined at: " + br.getOrigin();
            return create(br.displayName(), () ->
                    Stream.of(docs.find(br), description)
                            .filter(Objects::nonNull)
                            .collect(Collectors.joining("\n\n")));
        }

        public InfoTreeNode create(String title, String description) {
            return create(title, () -> description);
        }

        public InfoTreeNode create(String title, Supplier<String> description) {
            return new InfoTreeNode(title, description);
        }


        public static class InfoTreeNode extends DefaultMutableTreeNode {
            private final Supplier<String> description;

            public InfoTreeNode(String name, Supplier<String> description) {
                super(name);
                this.description = description;
            }

            public String getDescription() {
                return description.get();
            }
        }
    }
}
