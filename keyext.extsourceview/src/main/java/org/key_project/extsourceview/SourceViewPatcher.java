package org.key_project.extsourceview;

import bibliothek.util.container.Tuple;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.ProofMacroWorker;
import de.uka.ilkd.key.gui.nodeviews.CurrentGoalView;
import de.uka.ilkd.key.gui.sourceview.SourceView;
import de.uka.ilkd.key.gui.sourceview.SourceViewInsertion;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.origin.OriginRef;
import de.uka.ilkd.key.macros.*;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.StrategyProperties;
import org.key_project.extsourceview.transformer.*;
import org.key_project.extsourceview.utils.SplitRunner;
import org.key_project.extsourceview.utils.SymbolicExecutionAndSimplificationRunner;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import org.jspecify.annotations.Nullable;
import javax.swing.*;
import javax.swing.text.BadLocationException;
import java.awt.*;
import java.awt.event.MouseEvent;
import java.io.IOException;
import java.net.URI;
import java.time.Instant;
import java.time.temporal.ChronoField;
import java.time.temporal.TemporalField;
import java.util.List;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Main class for transforming current sequent back to InsertionTerms
 * and then positioning them in the SourceView
 */
public class SourceViewPatcher {

    private static final Logger LOGGER = LoggerFactory.getLogger(SourceViewPatcher.class);

    public static final String INSERTION_GROUP = "ExtSourceViewExtension::insertion";

    private final static Color COL_HIGHLIGHT_MAIN       = new Color(255, 0, 255);
    private final static Color COL_HIGHLIGHT_CHILDS     = new Color(255, 128, 255);
    private final static Color COL_HIGHLIGHT_INSERTIONS = null;
    private final static Color COL_HIGHLIGHT_INSLINE    = new Color(235, 235, 235);
    private final static Color COL_HIGHLIGHT_FORMULAS   = new Color(175, 200, 250);

    private final static String HL_KEY = "SourceViewPatcher::highlight";

    private final static int HIGHTLIGHT_LEVEL = 11;

    public final static java.util.List<Tuple<InsertionTerm, SourceViewInsertion>> ActiveInsertions = new ArrayList<>();

    public static void updateSourceview(MainWindow window,
                                        KeYMediator mediator,
                                        boolean enabled,
                                        boolean hideNonRelevant,
                                        boolean failOnCategorization,
                                        boolean failOnTranslation,
                                        boolean failOnPositioning,
                                        boolean recursiveLookup,
                                        boolean allowNoOriginFormulas,
                                        boolean translationFallback,
                                        int positioningStrategy,
                                        boolean colorized,
                                        boolean allowUnknownConstants,
                                        boolean allowDisjunctAssertions,
                                        boolean reInlineConstPullouts,
                                        boolean manuallyTranslateLoopAssertions,
                                        int scrollFix)
            throws TransformException, InternTransformException {

        SourceView sourceView = window.getSourceViewFrame().getSourceView();
        CurrentGoalView goalView = window.getGoalView();

        // currently we support only proofs with a single file
        URI fileUri = sourceView.getSelectedFile();

        if (fileUri == null) {
            throw new InternTransformException("No source loaded"); // no proof, or no source
        }

        var scrollPos = sourceView.getScrollPosition();

        var success = false;

        try {

            try {
                sourceView.clearInsertion(fileUri, INSERTION_GROUP);
                ActiveInsertions.clear();
            } catch (IOException | BadLocationException e) {
                throw new InternTransformException("Failed to clear existing insertions", e);
            }

            if (!enabled) {
                return;
            }

            sourceView.updateSymbExecHighlights();

            var services = mediator.getServices();
            var proof = mediator.getSelectedProof();
            var node = mediator.getSelectedNode();
            var sequent = node.sequent();

            if (!proof.getSettings().getStrategySettings().getActiveStrategyProperties().getProperty(StrategyProperties.LOOP_OPTIONS_KEY, "").equals(StrategyProperties.LOOP_INVARIANT)) {
                throw new TransformException("Must select Loop treatment 'Invariant (Transformation)'");
            }

            HeapSourceCollection hsc = new HeapSourceCollection(node.sequent());
            hsc.collect(node);
            SequentBackTransformer transformer = new SequentBackTransformer(
                    services,
                    proof,
                    node,
                    !failOnCategorization,
                    recursiveLookup,
                    allowNoOriginFormulas,
                    allowDisjunctAssertions,
                    reInlineConstPullouts);

            TermTranslator translator = new TermTranslator(fileUri, services, sequent, translationFallback, allowUnknownConstants, manuallyTranslateLoopAssertions);

            InsertionSet parts = transformer.extract();

            InsPositionProvider posProvider;
            if (positioningStrategy == 0) {
                posProvider = new DummyPositionProvider();
            } else if (positioningStrategy == 1) {
                posProvider = new MethodPositioner(fileUri, services, proof, node);
            } else if (positioningStrategy == 2) {
                posProvider = new HeapPositioner(fileUri, services, proof, node);
            } else if (positioningStrategy == 3) {
                posProvider = new MovingPositioner(fileUri, services, proof, node, hsc);
            } else {
                throw new InternTransformException("No positioning-strategy selected");
            }

            for (var iterm : parts.get()) {

                if (!iterm.IsRevelant() && hideNonRelevant) {
                    continue;
                }

                InsPositionProvider.InsertionPosition ppos = new InsPositionProvider.InsertionPosition(1, 1, 0);
                try {
                    ppos = posProvider.getPosition(sequent, iterm);
                } catch (Throwable e) {
                    if (failOnPositioning) throw e;
                }

                String jmlstr = " ".repeat(ppos.Indentation) + (failOnTranslation ? translator.translate(iterm, posProvider) : translator.translateSafe(iterm, posProvider));

                try {
                    preAddInsertion(mediator, sourceView, goalView, ppos.Line, iterm, jmlstr, colorized);
                } catch (IOException | BadLocationException e) {
                    throw new InternTransformException("Failed to add insertion", e);
                }

            }

            try {
                addAllInsertions(mediator, sourceView, fileUri);
            } catch (IOException | BadLocationException e) {
                throw new InternTransformException("Failed to add insertion", e);
            }

            success = true;
        } catch (Throwable e) {
            try {
                sourceView.clearInsertion(fileUri, INSERTION_GROUP);
                ActiveInsertions.clear();
            } catch (Exception e2) {
                //ignore
            }
            throw e;
        } finally {
            if (scrollFix == 1) {
                SwingUtilities.invokeLater(() -> sourceView.setScrollPosition(scrollPos));
            } else if (scrollFix == 2){
                if (success) SwingUtilities.invokeLater(sourceView::scrollToActiveStatement);
            }
        }
    }

    public static void clearInsertions(MainWindow window) {

        SourceView sourceView = window.getSourceViewFrame().getSourceView();
        CurrentGoalView goalView = window.getGoalView();

        // currently we support only proofs with a single file
        URI fileUri = sourceView.getSelectedFile();

        if (fileUri == null) {
            return; // no proof, or no source
        }
        try {
            sourceView.clearInsertion(fileUri, INSERTION_GROUP);
        } catch (IOException | BadLocationException e) {
            // nothing
        }
        ActiveInsertions.clear();
    }

    private static void preAddInsertion(KeYMediator mediator, SourceView sv, CurrentGoalView gv, int line, InsertionTerm ins, String str, boolean colorized) throws IOException, BadLocationException, InternTransformException {
        Color col;

        if (ins.Type == InsertionType.ASSERT_ERROR || ins.Type == InsertionType.ASSUME_ERROR) {

            col = new Color(0xCC0000);

        } else if (colorized) {

            switch (ins.Type) {
                case ASSERT:
                    col = new Color(0x55002b);
                    break;
                case ASSIGNABLE:
                    col = new Color(0x8d6000);
                    break;
                case ASSUME:
                    col = new Color(0x006231);
                    break;
                default:
                    throw new InternTransformException("unknown ins.Type");
            }

        } else {

            col = new Color(0x0000c0); // = ColorSettings: "[java]jml" ?

        }

        SourceViewInsertion svi = new SourceViewInsertion(INSERTION_GROUP, line, str, col, COL_HIGHLIGHT_INSERTIONS, COL_HIGHLIGHT_INSLINE);

        var originRefs = Utils.getSubOriginRefs(ins.Term, true, true);

        svi.addMouseEnterListener(e -> {

            try {
                for (OriginRef orig : originRefs) {
                    if (!orig.hasFile() || !sv.hasFile(orig.fileURI()))
                        continue;

                    if (orig.LineStart == orig.LineEnd) {
                        sv.addHighlight(orig.fileURI(), HL_KEY, orig.LineStart, orig.ColumnStart,
                            orig.ColumnEnd, COL_HIGHLIGHT_MAIN, HIGHTLIGHT_LEVEL);
                    } else {
                        for (int i = orig.LineStart; i <= orig.LineEnd; i++) {
                            sv.addHighlight(orig.fileURI(), HL_KEY, i, COL_HIGHLIGHT_MAIN,
                                HIGHTLIGHT_LEVEL);
                        }
                    }
                }

                gv.setSourceSelectionHighlight(ins.Pos(), COL_HIGHLIGHT_FORMULAS);

            } catch (IOException | BadLocationException ex) {
                LOGGER.error("failed to add highlight", ex);
            }
        });
        svi.addMouseLeaveListener(e -> {
            sv.removeHighlights(HL_KEY);
            gv.removeSourceSelectionHighlight();
        });

        svi.addRightClickListener(e -> {
            showInteractionContextMenu(mediator, ins, e);
        });

        ActiveInsertions.add(Tuple.of(ins, svi));
    }

    private static void addAllInsertions(KeYMediator mediator, SourceView sv, URI fileUri) throws IOException, BadLocationException {

        sv.addInsertions(fileUri, ActiveInsertions.stream().map(Tuple::getB).collect(Collectors.toList()));

    }

    public static void showInteractionContextMenu(KeYMediator mediator, @Nullable InsertionTerm ins, MouseEvent e) {
        if (!(e.getSource() instanceof JComponent)) return;

        var src = (JComponent) e.getSource();

        var selectedGoal = mediator.getSelectedGoal();
        if (selectedGoal == null) return;

        Collection<TacletApp> tacletsF = (ins == null || ins.PIOs.size() != 1) ? Collections.emptyList() : mediator.getUI().getProofControl().getFindTaclet(selectedGoal, ins.PIOs.head()).toList();
        Collection<TacletApp> tacletsR = (ins == null || ins.PIOs.size() != 1) ? Collections.emptyList() : mediator.getUI().getProofControl().getRewriteTaclet(selectedGoal, ins.PIOs.head()).toList();
        Collection<TacletApp> tacletsN = mediator.getUI().getProofControl().getNoFindTaclet(selectedGoal).toList();

        List<TacletApp> tacletsAll = Stream.concat(tacletsF.stream(), Stream.concat(tacletsR.stream(), tacletsN.stream())).collect(Collectors.toList());

        var topLevel = new PosInOccurrence(mediator.getSelectedNode().sequent().getFormulabyNr(1), PosInTerm.getTopLevel(), false);

        final JPopupMenu menu = new JPopupMenu("Menu");

        {
            SymbolicExecutionAndSimplificationRunner runner = new SymbolicExecutionAndSimplificationRunner(mediator, mediator.getSelectedNode(), true, false);

            JMenuItem item = new JMenuItem("Symbolic Execution and Simplification");
            menu.add(item);
            item.setEnabled(runner.canApply());
            item.addActionListener(ae -> runner.runAsync());
        }

        {
            SymbolicExecutionAndSimplificationRunner runner = new SymbolicExecutionAndSimplificationRunner(mediator, mediator.getSelectedNode(), true, true);

            JMenuItem item = new JMenuItem("Symbolic Execution, Simplification, and Close Provable Goals");
            menu.add(item);
            item.setEnabled(runner.canApply());
            item.addActionListener(ae -> runner.runAsync());
        }

        menu.add(new JSeparator());

        {
            var macro = new TryCloseMacro(Integer.getInteger("key.autopilot.closesteps", 1000));
            JMenuItem item = new JMenuItem("Close If Provable");
            menu.add(item);
            item.setEnabled(macro.canApplyTo(mediator.getSelectedNode(), topLevel));
            item.addActionListener(ae -> runMacro(mediator, topLevel, macro));
        }

        menu.add(new JSeparator());

        {
            var taclet = tacletsAll.stream().filter(p -> p.taclet().name().toString().equals("cut_direct")).findFirst();
            JMenuItem item = new JMenuItem("Cut on this term (cut_direct)");
            menu.add(item);
            item.setEnabled(ins != null && ins.PIOs.size() == 1 && taclet.isPresent());
            item.addActionListener(ae -> runTaclet(mediator, taclet.orElseThrow(), Objects.requireNonNull(ins).PIOs.head()));
        }
        {
            var taclet = tacletsN.stream().filter(p -> p.taclet().name().toString().equals("cut")).findFirst();
            JMenuItem item = new JMenuItem("Cut");
            menu.add(item);
            item.setEnabled(ins != null && ins.PIOs.size() == 1 && taclet.isPresent());
            item.addActionListener(ae -> runTaclet(mediator, taclet.orElseThrow(), Objects.requireNonNull(ins).PIOs.head()));
        }

        menu.add(new JSeparator());

        {
            SplitRunner runner = new SplitRunner(mediator, mediator.getSelectedNode(), false, false);

            JMenuItem item = new JMenuItem("Split");
            menu.add(item);
            item.setEnabled(ins != null && runner.canApply(ins.PIOs));
            item.addActionListener(ae -> runner.runAsync(Objects.requireNonNull(ins).PIOs));
        }

        {
            SplitRunner runner = new SplitRunner(mediator, mediator.getSelectedNode(), false, true);

            JMenuItem item = new JMenuItem("Split, and Close Provable Goals");
            menu.add(item);
            item.setEnabled(ins != null && runner.canApply(ins.PIOs));
            item.addActionListener(ae -> runner.runAsync(Objects.requireNonNull(ins).PIOs));
        }

        menu.add(new JSeparator());

        {
            var taclet = tacletsAll
                    .stream()
                    .filter(p -> p.taclet().name().toString().equals("hide_left") || p.taclet().name().toString().equals("hide_right"))
                    .findFirst();
            JMenuItem item = new JMenuItem("Hide this term");
            menu.add(item);
            item.setEnabled(ins != null && ins.PIOs.size() == 1 && taclet.isPresent());
            item.addActionListener(ae -> runTaclet(mediator, taclet.orElseThrow(), Objects.requireNonNull(ins).PIOs.head()));
        }
        {
            var items = tacletsN.stream().filter(p -> p.taclet().displayName().startsWith("insert_hidden")).collect(Collectors.toList());

            JMenu item = new JMenu("Insert Hidden ("+items.size()+" items)");
            menu.add(item);
            item.setEnabled(!items.isEmpty());
            for (var itm : items) {
                var subitem  = new JMenuItem(itm.taclet().name().toString());
                item.add(subitem);
                item.setEnabled(true);
                item.addActionListener(ae -> runTaclet(mediator, itm, topLevel));
            }
        }

        menu.add(new JSeparator());

        {
            var taclet = tacletsAll
                    .stream()
                    .filter(p -> p.taclet().name().toString().equals("allLeft") || p.taclet().name().toString().equals("exRight"))
                    .findFirst();
            JMenuItem item = new JMenuItem("Instantiate Quantifier");
            menu.add(item);
            item.setEnabled(ins != null && ins.PIOs.size() == 1 && taclet.isPresent());
            item.addActionListener(ae -> runTaclet(mediator, taclet.orElseThrow(), Objects.requireNonNull(ins).PIOs.head()));
        }

        if (ExtSourceViewExtension.Inst.ShowExtInteractions) {
            menu.add(new JSeparator());
            {
                JMenuItem itemFind = new JMenu("[EXT] ALL FIND TACLETS");
                menu.add(itemFind);
                for (var t: tacletsF) {
                    JMenuItem subitem = new JMenuItem(t.taclet().name().toString());
                    itemFind.add(subitem);
                    subitem.addActionListener(ae -> runTaclet(mediator, t, ins.PIOs.head()));
                }
                JMenuItem itemRewrite = new JMenu("[EXT] ALL REWRITE TACLETS");
                menu.add(itemRewrite);
                for (var t: tacletsR) {
                    JMenuItem subitem = new JMenuItem(t.taclet().name().toString());
                    itemRewrite.add(subitem);
                    subitem.addActionListener(ae -> runTaclet(mediator, t, ins.PIOs.head()));
                }
                JMenuItem itemNoFind = new JMenu("[EXT] ALL NOFIND TACLETS");
                menu.add(itemNoFind);
                for (var t: tacletsN) {
                    JMenuItem subitem = new JMenuItem(t.taclet().name().toString());
                    itemNoFind.add(subitem);
                    subitem.addActionListener(ae -> runTaclet(mediator, t, topLevel));
                }
            }
        }

        menu.show(src, e.getX(), e.getY());
    }

    private static void runTaclet(KeYMediator mediator, TacletApp t, PosInOccurrence pio) {
        mediator.getUI().getProofControl().selectedTaclet(t.taclet(), mediator.getSelectedGoal(), pio);
        //t.execute(mediator.getSelectedGoal(), mediator.getServices());
    }

    private static void runMacro(KeYMediator mediator, PosInOccurrence pio, AbstractProofMacro tcm) {
        if (!tcm.canApplyTo(mediator.getSelectedNode(), pio)) {
            return;
        }

        final ProofMacroWorker worker = new ProofMacroWorker(mediator.getSelectedNode(), tcm, mediator, pio);
        mediator.stopInterface(true);
        mediator.setInteractive(false);
        mediator.addInterruptedListener(worker);

        worker.execute();
    }

}
