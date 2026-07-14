/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.awt.event.ComponentEvent;
import java.awt.event.ComponentListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.util.*;
import java.util.function.Supplier;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import javax.swing.*;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.extension.api.ContextMenuKind;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.extension.impl.KeYGuiExtensionFacade;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.utilities.LexerHighlighter;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.label.TermLabelFactory;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.op.ParametricFunctionDecl;
import de.uka.ilkd.key.logic.sort.ParametricSortDecl;
import de.uka.ilkd.key.logic.sort.SortAlias;
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
import de.uka.ilkd.key.scripts.ProofScriptEngine;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.*;
import org.key_project.logic.op.Function;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.rules.RuleApp;

import com.google.common.collect.Multimap;
import com.google.common.collect.MultimapBuilder;
import org.checkerframework.checker.nullness.qual.MonotonicNonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

import static java.util.Objects.requireNonNullElse;

/**
 * Class for info contents displayed in {@link MainWindow}.
 *
 * @author Kai Wallisch
 * @author weigl
 */
@NullMarked
public class InfoView extends JSplitPane implements TabPanel {
    public static final Icon INFO_ICON =
        IconFactory.INFO_VIEW.get(MainWindow.TAB_ICON_SIZE);


    private final JTree infoTree = new JTree();
    private final JTextPane contentPane = createInfoArea();
    private final ProofDisposedListener proofDisposedListener;
    private final InfoNodeFactory nodeFactory = new InfoNodeFactory();

    private LexerHighlighter lexerHighlighter = new LexerHighlighter.KeYLexerHighlighter();


    private final KeYSelectionListener selectionListener = new KeYSelectionListener() {
        @Override
        public void selectedNodeChanged(KeYSelectionEvent<Node> e) {
            update();
        }

        private void update() {
            SwingUtilities.invokeLater(() -> {
                Goal goal = mediator.getSelectedGoal();
                if (goal != null) {
                    updateModel(goal);
                } else if (mediator.getSelectedProof() != null) {
                    try {
                        updateModel(mediator.getSelectedProof().openGoals().head());
                    } catch (NoSuchElementException ex) {
                        // nothing possible to do
                    }
                } else {
                    // No proof loaded (e.g. the last proof was just closed): clear the info tree
                    // instead of leaving stale content behind.
                    updateModel(null);
                }
            });
        }

        public void selectedProofChanged(KeYSelectionEvent<Proof> e) {
            update();
        }
    };

    private @Nullable Node lastShownGoalNode;
    private KeYMediator mediator;

    public InfoView(KeYMediator mediator) {
        super(VERTICAL_SPLIT);

        setMediator(mediator);

        // initial placement of the divider
        setDividerLocation(300);

        // growing goes to the upper half only
        setResizeWeight(1.0);

        // Setting a name for this causes PreferenceSaver to include this class.
        setName("infoViewPane");


        InfoNodeFactory.InfoTreeNode root = nodeFactory.create("No proof loaded",
            () -> "In this pane, the available logical rules will be displayed and/or explained.",
            List::of);
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
                SwingUtilities.invokeLater(() -> updateModel(null));
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
                final Object lastSelectedPathComponent = infoTree.getLastSelectedPathComponent();
                if (lastSelectedPathComponent instanceof InfoNodeFactory.InfoTreeNode node
                        && e.isPopupTrigger()) {
                    Object selected = node.getUserObject();
                    JPopupMenu menu = KeYGuiExtensionFacade.createContextMenu(
                        ContextMenuKind.INFO_TREE, selected, mediator);
                    if (menu.getComponentCount() > 0) {
                        menu.show(InfoView.this, e.getX(), e.getY());
                    }
                }
            }
        });

        infoTree.addTreeSelectionListener(e -> {
            Object node = infoTree.getLastSelectedPathComponent();
            if (node instanceof InfoNodeFactory.InfoTreeNode infoTreeNode) {
                contentPane.setText(infoTreeNode.getDescription());
                lexerHighlighter.highlightPaneMarkdown(contentPane);
            } else {
                contentPane.setText("");
            }
        });

        setLeftComponent(new JScrollPane(infoTree));
        setRightComponent(new JScrollPane(contentPane));

        KeYGuiExtensionFacade.installKeyboardShortcuts(mediator, this,
            KeYGuiExtension.KeyboardShortcuts.INFO_VIEW);
    }

    @Override
    public void updateUI() {
        // create new lexer highlighter for updating dark/light color
        lexerHighlighter = new LexerHighlighter.KeYLexerHighlighter();

        super.updateUI();
    }

    public void setMediator(KeYMediator m) {
        if (mediator != null) {
            mediator.removeKeYSelectionListener(selectionListener);
        }
        m.addKeYSelectionListener(selectionListener);
        mediator = m;
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

    private void updateModel(@Nullable Goal g) {
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

    private JTextPane createInfoArea() {
        JTextPane description = new JTextPane();
        description.setEditable(false);
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


        private InfoTreeNode createInfoTreeRoot(Goal g) {
            return create("This is the root node of InfoTreeModel.It should not be visible.",
                () -> "",
                () -> {
                    MetaSpace docs = g.proof().getServices().getNamespaces().docs();
                    final NamespaceSet namespaces = g.getLocalNamespaces();
                    return List.of(
                        createNodeRules(docs, g),
                        createNodeTermLabels(docs, g.proof()),
                        createNodeFunctions(docs, namespaces.functions()),
                        createNodeTacletOptions(docs, g.proof().getInitConfig()),
                        createNodeChoices(docs, namespaces.choices()),
                        createNodeRS("Parametric Functions", docs,
                            namespaces.parametricFunctions().allElements()),
                        createNodePS(docs, namespaces.parametricSorts().allElements()),
                        createNodePF(docs, namespaces.parametricFunctions().allElements()),
                        createNodeRS("Rule Sets", docs,
                            namespaces.ruleSets().allElements()),
                        createNodeAliases(docs, namespaces.sortAliases().allElements()),
                        createNodeRS("Variables", docs,
                            namespaces.variables().allElements()),
                        createNodeRS("Program Variables", docs,
                            namespaces.programVariables().allElements()),
                        createNodeScripts(docs));
                });
        }

        private InfoTreeNode createNodeAliases(
                MetaSpace docs, Collection<SortAlias> sortAliases) {
            return create("Sort Alias", () -> "", () -> sortAliases.stream().map(
                alias -> new InfoTreeNode(alias.name().toString(),
                    () -> "Alias of %s\n%s".formatted(alias.aliasedSort(),
                        requireNonNullElse(docs.findDocumentation(alias.aliasedSort()), "not set")),
                    List::of)).toList());
        }

        private InfoTreeNode createNodeRS(String title, MetaSpace docs,
                Collection<? extends HasMetaSpaceKey> ruleSets) {
            return create(title, () -> "",
                () -> ruleSets.stream()
                        .map(element -> create(element.toString(),
                            () -> docs.findDocumentation(element),
                            List::of))
                        .toList());
        }

        private InfoTreeNode createNodePS(MetaSpace docs,
                @MonotonicNonNull Collection<ParametricSortDecl> sorts) {
            return create("Parametric Sorts", () -> "",
                () -> sorts.stream().map(element -> create(element.name().toString(),
                    () -> "%s\n\n---\nparams:%s\n\n---\nextends: %s\n\n---\n".formatted(
                        requireNonNullElse(docs.findDocumentation(element), "no doc set"),
                        element.getParameters(), element.getExtendedSorts()),
                    List::of)).toList());
        }

        private InfoTreeNode createNodePF(MetaSpace docs,
                Collection<ParametricFunctionDecl> funcs) {
            return create("Parametric Functions", () -> "",
                () -> funcs.stream()
                        .map(
                            it -> create(it.toString(), () -> docs.findDocumentation(it), List::of))
                        .toList());
        }

        private InfoTreeNode createNodeChoices(MetaSpace docs, Namespace<Choice> choices) {
            return create("Choices",
                () -> "Browse descriptions for currently available choices", () -> {
                    Multimap<String, InfoTreeNode> map =
                        MultimapBuilder.hashKeys().arrayListValues(4).build();
                    choices.allElements().forEach(c -> map.put(c.category(),
                        create(c.name().toString(), () -> docs.findDocumentation(c))));
                    return map.keySet().stream().map(s -> {
                        return create(s,
                            () -> docs.findDocumentation(new HasMetaSpaceKey.OptionCategory(s)),
                            () -> new ArrayList<>(map.get(s)));
                    }).toList();
                });
        }

        private InfoTreeNode createNodeScripts(MetaSpace docs) {
            return create("Proof Script Commands",
                () -> "Browse descriptions for currently available proof script commands.",
                () -> ProofScriptEngine.loadCommands().entrySet().stream()
                        .map((e) -> create(e.getKey(), e.getValue()::getDocumentation)).toList());
        }

        private InfoTreeNode createNodeRules(MetaSpace docs, Goal g) {
            return create("Rules", () -> "Browse descriptions for currently available rules.",
                () -> {
                    List<NoPosTacletApp> set =
                        new ArrayList<>(g.ruleAppIndex().tacletIndex().allNoPosTacletApps());
                    OneStepSimplifier simplifier = MiscTools.findOneStepSimplifier(g.proof());
                    if (simplifier != null && !simplifier.isShutdown()) {
                        set.addAll(simplifier.getCapturedTaclets());
                    }
                    set.sort(Comparator.comparing(RuleApp::displayName));

                    return List.of(
                        createNodeBuiltInRules(docs, g),
                        createNodeAxiom(docs,
                            set.stream().filter(it -> {
                                RuleJustification just = g.proof().mgt().getJustification(it);
                                return just != null && just.isAxiomJustification();
                            }).toList()),
                        createNodeLemmas(docs, set.stream().filter(it -> {
                            RuleJustification just = g.proof().mgt().getJustification(it);
                            return just != null && !just.isAxiomJustification();
                        })));
                });
        }

        private InfoTreeNode createNodeBuiltInRules(MetaSpace docs, Goal g) {
            return create("Built-In",
                () -> "Some logical rules are implemented in Java code. This is because their semantics "
                    + "cannot easily be expressed in KeY's Taclet language.",
                () -> g.ruleAppIndex().builtInRuleAppIndex().builtInRuleIndex().rules()
                        .map(br -> create(br, docs))
                        .toList());
        }

        private InfoTreeNode createNodeAxiom(MetaSpace docs, List<NoPosTacletApp> seq) {
            var title = ("%s (%d)".formatted(TACLET_BASE, seq.size()));
            return create(title, () -> """
                    Most logical rules are implemented as Taclets.

                    Taclets are schematic logical rules formulated in the Taclet Language.\s
                    The language is defined and explained in the KeY book.
                    """,
                () -> {
                    Map<String, List<NoPosTacletApp>> ruleAppIndex = new TreeMap<>();
                    seq.forEach(
                        it -> ruleAppIndex.computeIfAbsent(it.displayName(), k -> new ArrayList<>())
                                .add(it));
                    return ruleAppIndex.entrySet().stream().flatMap(entry -> {
                        var value = entry.getValue();
                        var key = entry.getKey();
                        if (value.size() > 1) {
                            return Stream.of(
                                create("%s (%d)".formatted(key, value.size()), () -> "",
                                    () -> value.stream().map(it -> create(it.rule(), docs))
                                            .toList()));
                        } else {
                            return value.stream().map(it -> create(it.rule(), docs));
                        }
                    }).toList();
                });
        }

        private InfoTreeNode createNodeLemmas(MetaSpace docs, Stream<NoPosTacletApp> seq) {
            return create(LEMMAS,
                () -> """
                        Taclets which have been introduced using File->Load User-Defined Taclets are filed here.

                        Loading User Defined Taclets opens side branches on which the soundness of the lemma taclets must be established.
                        """,
                () -> seq.map(it -> create(it.rule(), docs)).toList());
        }

        private InfoTreeNode create(String title, Supplier<String> description) {
            return create(title, description, List::of);
        }

        private InfoTreeNode createNodeTermLabels(MetaSpace docs, Proof proof) {
            return create("Term Labels",
                () -> "Show descriptions for currently available term labels.",
                () -> {
                    TermLabelManager mgr =
                        TermLabelManager.getTermLabelManager(proof.getServices());
                    Map<Name, TermLabelFactory<?>> factories = mgr.getFactories();

                    ArrayList<Name> labelNames = new ArrayList<>(factories.keySet());
                    labelNames.sort(Comparator.comparing(Name::toString));

                    return labelNames.stream()
                            .map(name -> create(name.toString(),
                                () -> factories.get(name).getDocumentation()))
                            .toList();
                });
        }

        private InfoTreeNode createNodeFunctions(MetaSpace docs,
                Namespace<? extends Function> functions) {
            return create("Function Symbols", () -> DEFAULT_FUNCTIONS_LABEL,
                () -> {
                    ArrayList<? extends Function> seq = new ArrayList<>(functions.allElements());
                    seq.sort(Comparator.comparing(it -> it.name().toString()));

                    TreeMap<Sort, List<InfoTreeNode>> byReturn = new TreeMap<>(
                        Comparator.comparing(it -> it.name().toString()));

                    var flatList = new ArrayList<InfoTreeNode>();
                    var byType = new ArrayList<InfoTreeNode>();

                    for (Function fn : seq) {
                        String fnName = "%s(%s) : %s".formatted(
                            fn.name(),
                            fn.argSorts().stream().map(it -> it.name().toString())
                                    .collect(Collectors.joining(", ")),
                            fn.sort().name());
                        Sort fnSort = fn.sort();

                        // flat list:
                        Supplier<String> stringSupplier = () -> docs.findDocumentation(fn);
                        flatList.add(create(fnName, stringSupplier));

                        // by return type
                        byReturn.putIfAbsent(fnSort, new ArrayList<>());
                        byReturn.get(fnSort).add(create(fnName, stringSupplier));
                    }

                    for (Map.Entry<Sort, List<InfoTreeNode>> entry : byReturn.entrySet()) {
                        InfoTreeNode node = create(entry.getKey().name().toString(), () -> "",
                            () -> entry.getValue());
                        byType.add(node);
                    }

                    InfoTreeNode fnByName =
                        create("By Name", () -> DEFAULT_FUNCTIONS_LABEL, () -> flatList);
                    InfoTreeNode fnByReturnType =
                        create("By Return Type", () -> DEFAULT_FUNCTIONS_LABEL, () -> byType);

                    return List.of(fnByName, fnByReturnType);
                });
        }

        private InfoTreeNode createNodeTacletOptions(MetaSpace docs, InitConfig initConfig) {
            return create("Active Taclet Options",
                () -> "Shows the activated Taclet options", () -> initConfig.getActivatedChoices()
                        .stream()
                        .map(it -> create(it.name().toString(),
                            () -> "" + docs.findDocumentation(it), List::of))
                        .toList());
        }


        private InfoTreeNode create(Taclet taclet, MetaSpace metaSpace) {
            return create(taclet.name().toString(),
                () -> {
                    LogicPrinter lp = LogicPrinter.purePrinter(new NotationInfo(), null);
                    lp.printTaclet(taclet);
                    String doc = metaSpace.findDocumentation(taclet);
                    String origin = metaSpace.findOrigin(taclet);
                    return requireNonNullElse(doc, "No documentation given.")
                        + "\n\n"
                        + "```key\n%s\n```\n\n".formatted(lp.result())
                        + "Defined at: %s \n under options: (%s)".formatted(
                            requireNonNullElse(origin, "not set"),
                            taclet.getChoices());
                },
                List::of);
        }

        private InfoTreeNode create(BuiltInRule br, MetaSpace docs) {
            String description = "Defined in Java class" + br.getClass();
            return create(br.displayName(), () -> Stream.of(docs.findDocumentation(br), description)
                    .filter(Objects::nonNull)
                    .collect(Collectors.joining("\n\n")),
                List::of);
        }

        private InfoTreeNode create(String title, Supplier<String> description,
                Supplier<List<InfoTreeNode>> children) {
            return new InfoTreeNode(title, description, children);
        }

        private static class InfoTreeNode implements TreeNode {
            private final Supplier<@Nullable String> description;
            private final String title;
            private @Nullable List<InfoTreeNode> children;
            private final Supplier<List<InfoTreeNode>> childrenSupplier;
            private TreeNode parent;
            private Object userObject;

            public InfoTreeNode(String name, Supplier<String> description,
                    Supplier<List<InfoTreeNode>> children) {
                this.title = name;
                this.description = description;
                this.childrenSupplier = children;
            }

            @Override
            public String toString() {
                return title;
            }

            public @Nullable String getDescription() {
                return description.get();
            }

            public List<InfoTreeNode> getChildren() {
                if (children == null) {
                    children = childrenSupplier.get();
                }
                return children;
            }

            @Override
            public TreeNode getChildAt(int childIndex) {
                return getChildren().get(childIndex);
            }

            @Override
            public int getChildCount() {
                return getChildren().size();
            }

            @Override
            public TreeNode getParent() {
                return parent;
            }

            @Override
            public int getIndex(TreeNode node) {
                return getChildren().indexOf(node);
            }

            @Override
            public boolean getAllowsChildren() {
                return true;
            }

            @Override
            public boolean isLeaf() {
                return getChildren().isEmpty();
            }

            @Override
            public Enumeration<? extends TreeNode> children() {
                return Collections.enumeration(getChildren());
            }

            public Object getUserObject() {
                return userObject;
            }

            public void setUserObject(Object userObject) {
                this.userObject = userObject;
            }
        }
    }
}
