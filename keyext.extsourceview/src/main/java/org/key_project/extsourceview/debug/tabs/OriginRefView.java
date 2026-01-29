package org.key_project.extsourceview.debug.tabs;

import bibliothek.util.container.Tuple;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.SequentInteractionListener;
import de.uka.ilkd.key.gui.sourceview.SourceView;
import org.jspecify.annotations.NonNull;
import org.key_project.logic.Term;
import de.uka.ilkd.key.logic.origin.OriginRef;
import de.uka.ilkd.key.pp.PosInSequent;
import org.key_project.extsourceview.SourceViewPatcher;
import org.key_project.extsourceview.Utils;
import org.key_project.extsourceview.debug.DebugTab;
import org.key_project.extsourceview.transformer.*;

import javax.swing.*;
import javax.swing.text.BadLocationException;
import java.awt.*;
import java.io.IOException;
import java.net.URISyntaxException;
import java.util.ArrayList;
import java.util.stream.Collectors;

import static org.key_project.extsourceview.debug.tabs.GUIUtil.gbc;

/**
 * Class for the [TermOrigin Inspector] Tab in the debug panel
 *
 * Displays a bunch of information about the currently hovered term (in GoalView)
 */
public class OriginRefView extends DebugTab {

    private final static Color COL_HIGHLIGHT_MAIN = new Color(255, 0, 255);
    private final static Color COL_HIGHLIGHT_INS = new Color(175, 200, 250);
    private final static Color COL_HIGHLIGHT_CHILDS = new Color(255, 128, 255);

    private final static String HL_KEY = "OriginRefView::highlight";

    private final static int HIGHTLIGHT_LEVEL = 11;

    private JTextArea taSource;

    private boolean triggerOnClick = false;

    private boolean showSectionRepr = true;
    private boolean showSectionSelf = true;
    private boolean showSectionSource = true;
    private boolean showSectionChildren = true;
    private boolean showSectionParent = true;
    private boolean showSectionHeaps = true;
    private boolean highlightEnabled = true;
    private boolean highlightOnlyAtoms = true;
    private boolean highlightParents = true;
    private boolean highlightAllChildren = true;

    private Tuple<PosInSequent, Term> shownTerm = null;

    public OriginRefView(@NonNull MainWindow window, @NonNull KeYMediator mediator) {
        super();

        // add a listener for hover in the proof tree
        mediator.addSequentInteractionListener(new SequentInteractionListener() {
            @Override
            public void hover(PosInSequent pos, Term t) {
                highlightTerm(window, mediator, pos, t);
                if (!OriginRefView.this.triggerOnClick)
                    showTerm(window, mediator, pos, t);
            }

            @Override
            public void leaveHover() {
                unhighlightTerm(window, mediator);
                if (!OriginRefView.this.triggerOnClick)
                    unshowTerm(window, mediator);
            }

            @Override
            public void click(PosInSequent pos, Term t) {
                if (OriginRefView.this.triggerOnClick)
                    showTerm(window, mediator, pos, t);
            }
        });

        initGUI(window, mediator);
    }

    private void initGUI(@NonNull MainWindow window, @NonNull KeYMediator mediator) {
        setLayout(new BorderLayout());

        taSource = new JTextArea();
        taSource.setEditable(false);
        taSource.setFont(new Font("Courier New", Font.PLAIN, 12));
        taSource.setLineWrap(true);

        this.add(new JScrollPane(taSource), BorderLayout.CENTER);


        var pnlConf = new JPanel(new GridBagLayout());

        {
            var cbClick = new JCheckBox("Trigger on click", false);
            pnlConf.add(cbClick, gbc(0, 0));
            cbClick.addItemListener(e -> {
                OriginRefView.this.triggerOnClick = cbClick.isSelected();
                refreshShownTerm(window, mediator);
            });
            OriginRefView.this.triggerOnClick = cbClick.isSelected();
        }
        {
            var cbSec = new JCheckBox("Section [ToString]", true);
            pnlConf.add(cbSec, gbc(1, 0));
            cbSec.addItemListener(e -> {
                OriginRefView.this.showSectionRepr = cbSec.isSelected();
                refreshShownTerm(window, mediator);
            });
            OriginRefView.this.showSectionRepr = cbSec.isSelected();
        }
        {
            var cbSec = new JCheckBox("Section [Self]", true);
            pnlConf.add(cbSec, gbc(1, 1));
            cbSec.addItemListener(e -> {
                OriginRefView.this.showSectionSelf = cbSec.isSelected();
                refreshShownTerm(window, mediator);
            });
            OriginRefView.this.showSectionSelf = cbSec.isSelected();
        }
        {
            var cbSec = new JCheckBox("Section [Source]", false);
            pnlConf.add(cbSec, gbc(1, 2));
            cbSec.addItemListener(e -> {
                OriginRefView.this.showSectionSource = cbSec.isSelected();
                refreshShownTerm(window, mediator);
            });
            OriginRefView.this.showSectionSource = cbSec.isSelected();
        }
        {
            var cbSec = new JCheckBox("Section [Children]", false);
            pnlConf.add(cbSec, gbc(2, 0));
            cbSec.addItemListener(e -> {
                OriginRefView.this.showSectionChildren = cbSec.isSelected();
                refreshShownTerm(window, mediator);
            });
            OriginRefView.this.showSectionChildren = cbSec.isSelected();
        }
        {
            var cbSec = new JCheckBox("Section [Parent]", false);
            pnlConf.add(cbSec, gbc(2, 1));
            cbSec.addItemListener(e -> {
                OriginRefView.this.showSectionParent = cbSec.isSelected();
                refreshShownTerm(window, mediator);
            });
            OriginRefView.this.showSectionParent = cbSec.isSelected();
        }
        {
            var cbSec = new JCheckBox("Section [Heaps]", true);
            pnlConf.add(cbSec, gbc(2, 2));
            cbSec.addItemListener(e -> {
                OriginRefView.this.showSectionHeaps = cbSec.isSelected();
                refreshShownTerm(window, mediator);
            });
            OriginRefView.this.showSectionHeaps = cbSec.isSelected();
        }
        {
            var cbSec = new JCheckBox("Enable Highlights", true);
            pnlConf.add(cbSec, gbc(3, 0));
            cbSec.addItemListener(e -> {
                OriginRefView.this.highlightEnabled = cbSec.isSelected();
            });
            OriginRefView.this.highlightEnabled = cbSec.isSelected();
        }
        {
            var cbSec = new JCheckBox("Highlight Only Atoms", true);
            pnlConf.add(cbSec, gbc(3, 1));
            cbSec.addItemListener(e -> {
                OriginRefView.this.highlightOnlyAtoms = cbSec.isSelected();
            });
            OriginRefView.this.highlightOnlyAtoms = cbSec.isSelected();
        }
        {
            var cbSec = new JCheckBox("Search for Parent", true);
            pnlConf.add(cbSec, gbc(3, 2));
            cbSec.addItemListener(e -> {
                OriginRefView.this.highlightParents = cbSec.isSelected();
            });
            OriginRefView.this.highlightParents = cbSec.isSelected();
        }
        {
            var cbSec = new JCheckBox("Highlight union of all children", true);
            pnlConf.add(cbSec, gbc(3, 3));
            cbSec.addItemListener(e -> {
                OriginRefView.this.highlightAllChildren = cbSec.isSelected();
            });
            OriginRefView.this.highlightAllChildren = cbSec.isSelected();
        }

        pnlConf.setMinimumSize(new Dimension(0, 0));

        this.add(pnlConf, BorderLayout.NORTH);
    }

    private void refreshShownTerm(@NonNull MainWindow window, @NonNull KeYMediator mediator) {
        if (shownTerm != null) {
            showTerm(window, mediator, shownTerm.getA(), shownTerm.getB());
        }
    }

    @NonNull
    @Override
    public String getTitle() {
        return "TermOrigin Inspector";
    }

    private void highlightTerm(@NonNull MainWindow window, @NonNull KeYMediator mediator, PosInSequent pos, Term t) {
        try {
            SourceView sv = window.getSourceViewFrame().getSourceView();

            sv.removeHighlights(HL_KEY);

            for (var ai: SourceViewPatcher.ActiveInsertions) {
                ai.getB().clearBackgroundOverride();
            }
            sv.repaintInsertion(null);

            if (!highlightEnabled)
                return;

            var originRefs = new ArrayList<OriginRef>();
            if (highlightAllChildren) {
                originRefs = Utils.getSubOriginRefs(t, true, highlightOnlyAtoms);
            } else {
                originRefs.addAll(t.getOriginRef().stream().filter(p -> !highlightOnlyAtoms || p.isAtom()).collect(Collectors.toList()));
            }

            if (originRefs.isEmpty() && highlightParents) {
                var parentTerm = Utils.getParentWithOriginRef(pos, true, true);
                if (parentTerm != null) {
                    originRefs.addAll(parentTerm.getOriginRef().toList());
                }
            }

            for (OriginRef orig : originRefs) {
                if (!orig.hasFile())
                    continue;

                if (!sv.hasFile(orig.fileURI()))
                    continue;

                if (orig.LineStart == orig.LineEnd) {
                    sv.addHighlight(orig.fileURI(), HL_KEY, orig.LineStart, orig.ColumnStart,
                        orig.ColumnEnd, COL_HIGHLIGHT_MAIN, HIGHTLIGHT_LEVEL);
                } else {
                    for (int i = orig.LineStart; i <= orig.LineEnd; i++) {
                        if (orig.hasFile()) {
                            sv.addHighlight(orig.fileURI(), HL_KEY, i, COL_HIGHLIGHT_MAIN,
                                HIGHTLIGHT_LEVEL);
                        }
                    }
                }
            }

            PosInOccurrence rootPos = pos.getPosInOccurrence();
            while (true) {
                final Term rpTerm = rootPos.subTerm();
                var insertion = SourceViewPatcher.ActiveInsertions.stream().filter(p -> p.getA().Term == rpTerm).findFirst();
                if (insertion.isPresent()) {
                    var insterm = insertion.get().getB();
                    insterm.setBackgroundOverride(COL_HIGHLIGHT_INS);
                    sv.repaintInsertion(insterm);
                    break;
                } else if (rootPos.isTopLevel()) {
                    break;
                } else {
                    rootPos = rootPos.up();
                }
            }

        } catch (IOException | BadLocationException e) {
            e.printStackTrace();
        }
    }

    private void unhighlightTerm(@NonNull MainWindow window, @NonNull KeYMediator mediator) {
        SourceView sv = window.getSourceViewFrame().getSourceView();

        sv.removeHighlights(HL_KEY);

        for (var ai: SourceViewPatcher.ActiveInsertions) {
            ai.getB().clearBackgroundOverride();
        }
        sv.repaintInsertion(null);

    }

    private void showTerm(@NonNull MainWindow window, @NonNull KeYMediator mediator, PosInSequent pos, Term t) {
        shownTerm = new Tuple<>(pos, t);

        var proof = mediator.getSelectedProof();
        var sequent = mediator.getSelectedNode().sequent();

        var fileUri = window.getSourceViewFrame().getSourceView().getSelectedFile();

        var translator = new TermTranslator(fileUri, mediator.getServices(), mediator.getSelectedNode().sequent(), true, true, false);

        try {
            StringBuilder txt = new StringBuilder();

            if (showSectionRepr) {
                txt.append("----------<TOSTRING>----------\n");
                txt.append("\n");
                txt.append("ToStr<Translate>: ").append(translator.translateSafe(t, InsertionType.ASSERT)).append("\n");
                txt.append("ToStr<OriginRef>: ").append(translator.translateWithOrigin(t))
                        .append("\n");
                txt.append("ToStr<Fallback>:  ").append(translator.translateRaw(t, true))
                        .append("\n");
                txt.append("\n");
            }

            if (showSectionSelf) {
                txt.append("----------<SELF>----------\n");
                txt.append("\n");

                if (t instanceof TermImpl) {
                    TermImpl term = (TermImpl) t;

                    {
                        for (var o: term.getOriginRef()) {
                            txt.append(origRefToString(term, o));
                            txt.append("\n");
                        }
                    }
                }
                txt.append("\n");
            }

            if (showSectionSource) {
                txt.append("----------<SOURCE>----------\n");
                txt.append("\n");
                if (t instanceof TermImpl) {
                    TermImpl term = (TermImpl) t;

                    for (var o: term.getOriginRef().stream().filter(OriginRef::hasFile).collect(Collectors.toList())) {
                        for (int i = o.LineStart; i <= o.LineEnd; i++) {
                            var str = Utils.getLines(o.File, i, i);
                            txt.append(str.stripTrailing()).append("\n");
                            str = " ".repeat(o.ColumnStart - 1) + "["
                                + Utils.safeSubstring(str, o.ColumnStart, o.ColumnEnd) + "]"
                                + " ".repeat(o.ColumnEnd - 1);
                            txt.append(str).append("\n");
                            txt.append("\n");
                        }
                    }
                }
            }

            if (showSectionChildren) {
                txt.append("----------<CHILDREN>----------\n");
                txt.append("\n");

                if (t instanceof TermImpl) {
                    TermImpl term = (TermImpl) t;

                    for (OriginRef o : Utils.getSubOriginRefs(term, false, false)) {
                        txt.append(origRefToString(term, o));
                        txt.append("\n");
                    }

                }

                txt.append("\n");
            }

            if (showSectionParent) {
                txt.append("----------<PARENT>----------\n");
                txt.append("\n");

                Term parent = Utils.getParentWithOriginRef(pos, true, false);
                if (parent != null && parent != pos.getPosInOccurrence().subTerm()) {
                    txt.append("ToStr<Translate>: ").append(translator.translateSafe(parent, InsertionType.ASSERT)).append("\n");
                    txt.append("ToStr<OriginRef>: ").append(translator.translateWithOrigin(parent)).append("\n");
                    txt.append("ToStr<Fallback>:  ").append(translator.translateRaw(parent, true)).append("\n");
                    txt.append("\n");
                    for (var o: parent.getOriginRef()) {
                        txt.append(origRefToString(parent, o));
                        txt.append("\n");
                    }
                }

                txt.append("\n");
            }

            if (showSectionHeaps) {
                txt.append("----------<HEAPS>----------\n");
                txt.append("\n");

                try {

                    var mpos = new MovingPositioner(fileUri, mediator.getServices(), proof, mediator.getSelectedNode(), null);

                    var heaps = MovingPositioner.listHeaps(sequent, t, false);

                    var methodPosition = mpos.getMethodPositionMap();

                    for (var h: heaps) {

                        txt.append("HEAP @ ").append(h.getLineNumber(methodPosition)).append("\n");
                        txt.append("{").append("\n");

                        txt.append(heapRefToString("  ", translator, h));

                        txt.append("}").append("\n");
                        txt.append("\n");

                    }

                } catch (InternTransformException | TransformException e) {
                    txt.append("[[EXCEPTION]]\n");
                }

                txt.append("\n");
            }

            taSource.setText(txt.toString().stripTrailing());
        } catch (IOException | URISyntaxException e) {
            taSource.setText(e.toString());
        }
    }

    private String heapRefToString(String indent, TermTranslator translator, HeapReference heapref) {
        StringBuilder txt = new StringBuilder();


        var tablen1 = heapref.updates.stream().filter(p -> p.Term1 != null).map(p -> translator.translateRaw(p.Term1, true).length()).max(Integer::compareTo).orElse(0);
        var tablen2 = heapref.updates.stream().filter(p -> p.Term2 != null).map(p -> translator.translateRaw(p.Term2, true).length()).max(Integer::compareTo).orElse(0);
        var tablen3 = heapref.updates.stream().filter(p -> p.Term3 != null).map(p -> translator.translateRaw(p.Term3, true).length()).max(Integer::compareTo).orElse(0);

        for (var upd: heapref.updates) {

            var orstr = "";
            if (upd.Origin != null) {
                orstr = upd.Origin.sourcetoString();
            }

            var str1 = "";
            if (upd.Term1 != null) {
                str1 = String.format("%-" + tablen1 + "s", translator.translateRaw(upd.Term1, true));
            }
            var str2 = "";
            if (upd.Term2 != null) {
                str2 = String.format("%-" + tablen2 + "s", translator.translateRaw(upd.Term2, true));
            }
            var str3 = "";
            if (upd.Term3 != null) {
                str3 = String.format("%-" + tablen3 + "s", translator.translateRaw(upd.Term3, true));
            }

            txt.
                    append(indent).
                    append(String.format("%-6s", upd.Type)).
                    append("  ").
                    append(String.format("%-32s", orstr)).
                    append("  ").
                    append(str1).
                    append("  ").
                    append(str2).
                    append("  ").
                    append(str3).
                    append("\n");
        }

        return txt.toString();
    }

    private String origRefToString(Term t, OriginRef o) {

        var f0 = (o.isAtom() ? "A" : " ");
        var f1 = (o.isBooleanTerm() ? "B" : " ");
        var f2 = (o.SourceTerm == null) ? "/" : (t.getOriginRef().size() > 9 ? "+" : (""+t.getOriginRef().size()));

        return "["+f0+"|"+f1+"|"+f2+"] " + o.toString();
    }

    private void unshowTerm(@NonNull MainWindow window, @NonNull KeYMediator mediator) {
        shownTerm = null;

        taSource.setText("");
    }
}
