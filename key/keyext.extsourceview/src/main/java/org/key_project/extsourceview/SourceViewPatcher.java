package org.key_project.extsourceview;

import bibliothek.util.container.Tuple;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.nodeviews.CurrentGoalView;
import de.uka.ilkd.key.gui.sourceview.SourceView;
import de.uka.ilkd.key.gui.sourceview.SourceViewInsertion;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.origin.OriginRef;
import de.uka.ilkd.key.macros.AbstractProofMacro;
import de.uka.ilkd.key.macros.TryCloseMacro;
import de.uka.ilkd.key.macros.UpdateSimplificationMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.prover.TaskFinishedInfo;
import de.uka.ilkd.key.prover.TaskStartedInfo;
import de.uka.ilkd.key.rule.TacletApp;
import org.key_project.extsourceview.transformer.*;
import org.key_project.util.collection.ImmutableList;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.swing.*;
import javax.swing.event.PopupMenuEvent;
import javax.swing.event.PopupMenuListener;
import javax.swing.text.BadLocationException;
import java.awt.*;
import java.io.IOException;
import java.net.URI;
import java.util.ArrayList;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Main class for transforming current sequent back to InsertionTerms
 * and then positioning them in the SourceView
 */
public class SourceViewPatcher {

    private static final Logger LOGGER = LoggerFactory.getLogger(SourceViewPatcher.class);

    public static final String INSERTION_GROUP = "ExtSourceViewExtension::insertion";

    public final static Color COL_HIGHLIGHT_MAIN = new Color(255, 0, 255);
    public final static Color COL_HIGHLIGHT_CHILDS = new Color(255, 128, 255);
    public final static Color COL_HIGHLIGHT_INSERTIONS = new Color(255, 255, 255);
    private final static Color COL_HIGHLIGHT_FORMULAS = new Color(175, 200, 250);

    private final static String HL_KEY = "SourceViewPatcher::highlight";

    private final static int HIGHTLIGHT_LEVEL = 11;

    public final static java.util.List<Tuple<InsertionTerm, SourceViewInsertion>> ActiveInsertions = new ArrayList<>();

    public static void updateSourceview(MainWindow window,
                                        KeYMediator mediator,
                                        boolean enabled,
                                        boolean hideNonRelevant,
                                        boolean continueOnError,
                                        boolean recursiveLookup,
                                        boolean allowNoOriginFormulas,
                                        boolean translationFallback,
                                        int positioningStrategy,
                                        boolean colorized)
            throws TransformException, InternTransformException {

        SourceView sourceView = window.getSourceViewFrame().getSourceView();
        CurrentGoalView goalView = window.getGoalView();

        // currently we support only proofs with a single file
        URI fileUri = sourceView.getSelectedFile();

        if (fileUri == null) {
            throw new InternTransformException("No source loaded"); // no proof, or no source
        }

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

            SequentBackTransformer transformer = new SequentBackTransformer(
                    mediator.getServices(),
                    mediator.getSelectedProof(),
                    mediator.getSelectedNode(),
                    continueOnError,
                    recursiveLookup,
                    allowNoOriginFormulas);

            TermTranslator translator = new TermTranslator(mediator.getServices(), translationFallback);

            InsertionSet parts = transformer.extract();

            InsPositionProvider posProvider;
            if (positioningStrategy == 0) {
                posProvider = new MethodPositioner(mediator.getServices(), mediator.getSelectedProof(), mediator.getSelectedNode());
            } else if (positioningStrategy == 1) {
                posProvider = new HeapPositioner(mediator.getServices(), mediator.getSelectedProof(), mediator.getSelectedNode(), continueOnError);
            } else {
                throw new InternTransformException("No positioning-strategy selected");
            }

            for (var iterm : parts.get()) {

                if (!iterm.IsRevelant() && hideNonRelevant) {
                    continue;
                }

                var ppos = posProvider.getPosition(fileUri, iterm);

                String jmlstr = " ".repeat(ppos.Indentation) + (continueOnError ? translator.translateSafe(iterm) : translator.translate(iterm));

                try {
                    addInsertion(mediator, sourceView, goalView, fileUri, ppos.Line, iterm, jmlstr, colorized);
                } catch (IOException | BadLocationException e) {
                    throw new InternTransformException("Failed to add insertion", e);
                }
            }

        } catch (Throwable e) {
            try {
                sourceView.clearInsertion(fileUri, INSERTION_GROUP);
                ActiveInsertions.clear();
            } catch (Exception e2) {
                //ignore
            }
            throw e;
        }
    }

    private static void addInsertion(KeYMediator mediator, SourceView sv, CurrentGoalView gv, URI fileUri, int line, InsertionTerm ins, String str, boolean colorized) throws IOException, BadLocationException, InternTransformException {
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

        SourceViewInsertion svi = new SourceViewInsertion(INSERTION_GROUP, line, str, col, COL_HIGHLIGHT_INSERTIONS);

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
            if (!(e.getSource() instanceof JComponent)) return;

            var src = (JComponent)e.getSource();

            var tacletsF = mediator.getUI().getProofControl().getFindTaclet(mediator.getSelectedGoal(), ins.PIO);
            var tacletsR = mediator.getUI().getProofControl().getRewriteTaclet(mediator.getSelectedGoal(), ins.PIO);
            var tacletsN = mediator.getUI().getProofControl().getNoFindTaclet(mediator.getSelectedGoal());

            var tacletsAll = Stream.concat(tacletsF.stream(), Stream.concat(tacletsR.stream(), tacletsN.stream())).collect(Collectors.toList());

            final JPopupMenu menu = new JPopupMenu("Menu");

            {
                var macro = new UpdateSimplificationMacro();
                JMenuItem item = new JMenuItem("[TODO] One Step Simplification / Update Simpleification Only");
                menu.add(item);
                item.setEnabled(macro.canApplyTo(mediator.getSelectedNode(), ins.PIO));
                item.addActionListener(ae -> runMacro(mediator, ins, macro));
            }
            menu.add(new JSeparator());
            {
                var macro = new TryCloseMacro(Integer.getInteger("key.autopilot.closesteps", 1000));
                JMenuItem item = new JMenuItem("[TODO] Try close");
                menu.add(item);
                item.setEnabled(macro.canApplyTo(mediator.getSelectedNode(), ins.PIO));
                item.addActionListener(ae -> runMacro(mediator, ins, macro));
            }
            menu.add(new JSeparator());
            {
                var taclet = tacletsAll.stream().filter(p -> p.taclet().name().toString().equals("cut_direct")).findFirst();
                JMenuItem item = new JMenuItem("[TODO] Cut on this term (cut_direct)");
                menu.add(item);
                item.setEnabled(taclet.isPresent());
                item.addActionListener(ae -> runTaclet(mediator, taclet.orElseThrow(), ins.PIO));
            }
            {
                var taclet = tacletsAll.stream().filter(p -> p.taclet().name().toString().equals("cut_direct_l")).findFirst();
                JMenuItem item = new JMenuItem("[TODO] Cut on this term (cut_direct_l)");
                menu.add(item);
                item.setEnabled(taclet.isPresent());
                item.addActionListener(ae -> runTaclet(mediator, taclet.orElseThrow(), ins.PIO));
            }
            {
                var taclet = tacletsAll.stream().filter(p -> p.taclet().name().toString().equals("cut_direct_r")).findFirst();
                JMenuItem item = new JMenuItem("[TODO] Cut on this term (cut_direct_r)");
                menu.add(item);
                item.setEnabled(taclet.isPresent());
                item.addActionListener(ae -> runTaclet(mediator, taclet.orElseThrow(), ins.PIO));
            }
            menu.add(new JSeparator());
            {
                var taclet = tacletsAll.stream().filter(p -> p.taclet().name().toString().equals("hide_left")).findFirst();
                JMenuItem item = new JMenuItem("[TODO] Hide this term (hide_left)");
                menu.add(item);
                item.setEnabled(taclet.isPresent());
                item.addActionListener(ae -> runTaclet(mediator, taclet.orElseThrow(), ins.PIO));
            }
            {
                var taclet = tacletsAll.stream().filter(p -> p.taclet().name().toString().equals("hide_right")).findFirst();
                JMenuItem item = new JMenuItem("[TODO] Hide this term (hide_right)");
                menu.add(item);
                item.setEnabled(taclet.isPresent());
                item.addActionListener(ae -> runTaclet(mediator, taclet.orElseThrow(), ins.PIO));
            }
            menu.add(new JSeparator());
            {
                var taclet = tacletsAll.stream().filter(p -> p.taclet().name().toString().equals("or_left")).findFirst();
                JMenuItem item = new JMenuItem("[TODO] or_left");
                menu.add(item);
                item.setEnabled(taclet.isPresent());
                item.addActionListener(ae -> runTaclet(mediator, taclet.orElseThrow(), ins.PIO));
            }
            {
                var taclet = tacletsAll.stream().filter(p -> p.taclet().name().toString().equals("and_right")).findFirst();
                JMenuItem item = new JMenuItem("[TODO] and_right (should never happen?)");
                menu.add(item);
                item.setEnabled(taclet.isPresent());
                item.addActionListener(ae -> runTaclet(mediator, taclet.orElseThrow(), ins.PIO));
            }
            menu.add(new JSeparator());
            {
                var taclet = tacletsAll.stream().filter(p -> p.taclet().name().toString().equals("allRight")).findFirst();
                JMenuItem item = new JMenuItem("[TODO] Instantiate Quantifier (allRight)");
                menu.add(item);
                item.setEnabled(taclet.isPresent());
                item.addActionListener(ae -> runTaclet(mediator, taclet.orElseThrow(), ins.PIO));
            }
            {
                var taclet = tacletsAll.stream().filter(p -> p.taclet().name().toString().equals("exLeft")).findFirst();
                JMenuItem item = new JMenuItem("[TODO] Instantiate Quantifier (exLeft)");
                menu.add(item);
                item.setEnabled(taclet.isPresent());
                item.addActionListener(ae -> runTaclet(mediator, taclet.orElseThrow(), ins.PIO));
            }
            {
                var taclet = tacletsAll.stream().filter(p -> p.taclet().name().toString().equals("instAll")).findFirst();
                JMenuItem item = new JMenuItem("[TODO] Instantiate Quantifier (instAll)");
                menu.add(item);
                item.setEnabled(taclet.isPresent());
                item.addActionListener(ae -> runTaclet(mediator, taclet.orElseThrow(), ins.PIO));
            }
            {
                var taclet = tacletsAll.stream().filter(p -> p.taclet().name().toString().equals("instEx")).findFirst();
                JMenuItem item = new JMenuItem("[TODO] Instantiate Quantifier (instEx)");
                menu.add(item);
                item.setEnabled(taclet.isPresent());
                item.addActionListener(ae -> runTaclet(mediator, taclet.orElseThrow(), ins.PIO));
            }
            {
                var taclet = tacletsAll.stream().filter(p -> p.taclet().name().toString().equals("allLeft")).findFirst();
                JMenuItem item = new JMenuItem("[TODO] Instantiate Quantifier (allLeft)");
                menu.add(item);
                item.setEnabled(taclet.isPresent());
                item.addActionListener(ae -> runTaclet(mediator, taclet.orElseThrow(), ins.PIO));
            }
            {
                var taclet = tacletsAll.stream().filter(p -> p.taclet().name().toString().equals("exRight")).findFirst();
                JMenuItem item = new JMenuItem("[TODO] Instantiate Quantifier (exRight)");
                menu.add(item);
                item.setEnabled(taclet.isPresent());
                item.addActionListener(ae -> runTaclet(mediator, taclet.orElseThrow(), ins.PIO));
            }
            menu.add(new JSeparator());
            {
                JMenuItem itemFind = new JMenu("[TEST] ALL FIND TACLETS");
                menu.add(itemFind);
                for (var t: tacletsF) {
                    JMenuItem subitem = new JMenuItem(t.taclet().name().toString());
                    itemFind.add(subitem);
                    subitem.addActionListener(ae -> runTaclet(mediator, t, ins.PIO));
                }
                JMenuItem itemRewrite = new JMenu("[TEST] ALL REWRITE TACLETS");
                menu.add(itemRewrite);
                for (var t: tacletsR) {
                    JMenuItem subitem = new JMenuItem(t.taclet().name().toString());
                    itemRewrite.add(subitem);
                    subitem.addActionListener(ae -> runTaclet(mediator, t, ins.PIO));
                }
                JMenuItem itemNoFind = new JMenu("[TEST] ALL NOFIND TACLETS");
                menu.add(itemNoFind);
                for (var t: tacletsN) {
                    JMenuItem subitem = new JMenuItem(t.taclet().name().toString());
                    itemNoFind.add(subitem);
                    subitem.addActionListener(ae -> runTaclet(mediator, t, ins.PIO));
                }
            }

            menu.show(src, e.getX(), e.getY());
        });

        sv.addInsertion(fileUri, svi);

        ActiveInsertions.add(Tuple.of(ins, svi));
    }

    private static void runTaclet(KeYMediator mediator, TacletApp t, PosInOccurrence pio) {
        mediator.getUI().getProofControl().selectedTaclet(t.taclet(), mediator.getSelectedGoal(), pio);
        //t.execute(mediator.getSelectedGoal(), mediator.getServices());
    }

    private static void runMacro(KeYMediator mediator, InsertionTerm ins, AbstractProofMacro tcm) {
        if (!tcm.canApplyTo(mediator.getSelectedNode(), ins.PIO)) {
            return;
        }
        try {
            tcm.applyTo(mediator.getUI(), mediator.getSelectedNode(), ins.PIO, new ProverTaskListener() {
                @Override
                public void taskStarted(TaskStartedInfo info) { /**/ }
                @Override
                public void taskProgress(int position) { /**/ }
                @Override
                public void taskFinished(TaskFinishedInfo info) { /**/ }
            });
        } catch (Exception ex) {
            LOGGER.error(ex.toString());
        }
    }
}
