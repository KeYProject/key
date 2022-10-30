package org.key_project.extsourceview.debug.tabs;

import bibliothek.util.container.Tuple;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.SequentInteractionListener;
import de.uka.ilkd.key.gui.sourceview.SourceView;
import de.uka.ilkd.key.gui.sourceview.SourceViewHighlight;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermImpl;
import de.uka.ilkd.key.logic.origin.OriginRef;
import de.uka.ilkd.key.pp.PosInSequent;
import org.key_project.extsourceview.Utils;
import org.key_project.extsourceview.debug.DebugTab;

import javax.annotation.Nonnull;
import javax.swing.*;
import javax.swing.text.BadLocationException;
import java.awt.*;
import java.io.IOException;
import java.net.URISyntaxException;
import java.util.ArrayList;

public class OriginRefView extends DebugTab {

    private final static Color COL_HIGHLIGHT_MAIN = new Color(255, 0, 255);
    private final static Color COL_HIGHLIGHT_CHILDS = new Color(255, 128, 255);

    private final static String HL_KEY = "OriginRefView::highlight";

    private final static int HIGHTLIGHT_LEVEL = 11;

    private JTextArea taSource;

    private boolean showOnlyAtoms = true;
    private boolean triggerOnClick = false;

    private boolean showSectionRepr = true;
    private boolean showSectionSelf = true;
    private boolean showSectionSource = true;
    private boolean showSectionChildren = true;
    private boolean showSectionParent = true;
    private boolean highlightEnabled = true;
    private boolean highlightOnlyAtoms = true;
    private boolean highlightParents = true;
    private boolean highlightAllChildren = true;

    private Tuple<PosInSequent, Term> shownTerm = null;

    public OriginRefView(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        super();

        // add a listener for hover in the proof tree
        mediator.addSequentInteractionListener(new SequentInteractionListener() {
            @Override
            public void hover(PosInSequent pos, Term t) {
                highlightTerm(window, mediator, pos, t);
                if (!OriginRefView.this.triggerOnClick) showTerm(window, mediator, pos, t);
            }

            @Override
            public void leaveHover() {
                unhighlightTerm(window, mediator);
                if (!OriginRefView.this.triggerOnClick) unshowTerm(window, mediator);
            }

            @Override
            public void click(PosInSequent pos, Term t) {
                if (OriginRefView.this.triggerOnClick) showTerm(window, mediator, pos, t);
            }
        });

        initGUI(window, mediator);
    }

    private void initGUI(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        setLayout(new BorderLayout());

        taSource = new JTextArea();
        taSource.setEditable(false);
        taSource.setFont(new Font("Courier New", Font.PLAIN, 12));

        this.add(new JScrollPane(taSource), BorderLayout.CENTER);


        var pnlConf = new JPanel(new GridBagLayout());

        {
            var cbClick = new JCheckBox("Trigger on click");
            pnlConf.add(cbClick, gbc(0, 0));
            cbClick.addItemListener(e -> { OriginRefView.this.triggerOnClick = cbClick.isSelected(); refreshShownTerm(window, mediator); });
        }
        {
            var cbAtom = new JCheckBox("Only show atoms", true);
            pnlConf.add(cbAtom, gbc(0, 1));
            cbAtom.addItemListener(e -> { OriginRefView.this.showOnlyAtoms = cbAtom.isSelected(); refreshShownTerm(window, mediator); });
        }
        {
            var cbSec = new JCheckBox("Section [ToString]", true);
            pnlConf.add(cbSec, gbc(1, 0));
            cbSec.addItemListener(e -> { OriginRefView.this.showSectionRepr = cbSec.isSelected(); refreshShownTerm(window, mediator); });
        }
        {
            var cbSec = new JCheckBox("Section [Self]", true);
            pnlConf.add(cbSec, gbc(1, 1));
            cbSec.addItemListener(e -> { OriginRefView.this.showSectionSelf = cbSec.isSelected(); refreshShownTerm(window, mediator); });
        }
        {
            var cbSec = new JCheckBox("Section [Source]", true);
            pnlConf.add(cbSec, gbc(1, 2));
            cbSec.addItemListener(e -> { OriginRefView.this.showSectionSource = cbSec.isSelected(); refreshShownTerm(window, mediator); });
        }
        {
            var cbSec = new JCheckBox("Section [Children]", true);
            pnlConf.add(cbSec, gbc(1, 3));
            cbSec.addItemListener(e -> { OriginRefView.this.showSectionChildren = cbSec.isSelected(); refreshShownTerm(window, mediator); });
        }
        {
            var cbSec = new JCheckBox("Section [Parent]", true);
            pnlConf.add(cbSec, gbc(1, 4));
            cbSec.addItemListener(e -> { OriginRefView.this.showSectionParent = cbSec.isSelected(); refreshShownTerm(window, mediator); });
        }
        {
            var cbSec = new JCheckBox("Enable Highlights", true);
            pnlConf.add(cbSec, gbc(2, 0));
            cbSec.addItemListener(e -> { OriginRefView.this.highlightEnabled = cbSec.isSelected(); });
        }
        {
            var cbSec = new JCheckBox("Highlight Only Atoms", true);
            pnlConf.add(cbSec, gbc(2, 1));
            cbSec.addItemListener(e -> { OriginRefView.this.highlightOnlyAtoms = cbSec.isSelected(); });
        }
        {
            var cbSec = new JCheckBox("Search for Parent", true);
            pnlConf.add(cbSec, gbc(2, 2));
            cbSec.addItemListener(e -> { OriginRefView.this.highlightParents = cbSec.isSelected(); });
        }
        {
            var cbSec = new JCheckBox("Highlight union of all children", true);
            pnlConf.add(cbSec, gbc(2, 3));
            cbSec.addItemListener(e -> { OriginRefView.this.highlightAllChildren = cbSec.isSelected(); });
        }

        this.add(pnlConf, BorderLayout.NORTH);
    }

    private static GridBagConstraints gbc(int x, int y) {
        return new GridBagConstraints
        (
            x, y,
            1, 1,
            1.0 , 1.0,
            GridBagConstraints.CENTER,
            GridBagConstraints.BOTH,
            new Insets(0, 0, 0, 0),
            0, 0
        );
    }

    private void refreshShownTerm(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        if (shownTerm != null) {
            showTerm(window, mediator, shownTerm.getA(), shownTerm.getB());
        }
    }

    @Nonnull
    @Override
    public String getTitle() {
        return "TermOrigin Inspector";
    }

    private void highlightTerm(@Nonnull MainWindow window, @Nonnull KeYMediator mediator, PosInSequent pos, Term t) {
        try {
            SourceView sv = window.getSourceViewFrame().getSourceView();

            sv.removeHighlights(HL_KEY);

            if (!highlightEnabled) return;

            var originRefs = new ArrayList<OriginRef>();
            if (highlightAllChildren) {
                originRefs = Utils.getSubOriginRefs(t, true, highlightOnlyAtoms);
            } else {
                if (t.getOriginRef() != null && (!highlightOnlyAtoms || t.getOriginRef().IsAtom)) {
                    originRefs.add(t.getOriginRef());
                }
            }

            if (originRefs.isEmpty() && highlightParents) {
                var parentTerm = Utils.getParentWithOriginRef(pos, true, true);
                if (parentTerm != null) {
                    originRefs.add(parentTerm.getOriginRef());
                }
            }

            for (OriginRef orig : originRefs) {
                if (!orig.hasFile()) continue;

                if (!sv.hasFile(orig.fileURI())) continue;

                if (orig.LineStart == orig.LineEnd) {
                    sv.addHighlight(orig.fileURI(), HL_KEY, orig.LineStart, orig.ColumnStart, orig.ColumnEnd, COL_HIGHLIGHT_MAIN, HIGHTLIGHT_LEVEL);
                } else {
                    for (int i = orig.LineStart; i <= orig.LineEnd; i++) {
                        if (orig.hasFile()) {
                            sv.addHighlight(orig.fileURI(), HL_KEY, i, COL_HIGHLIGHT_MAIN, HIGHTLIGHT_LEVEL);
                        }
                    }
                }
            }

        } catch (IOException | BadLocationException e) {
            e.printStackTrace();
        }
    }

    private void unhighlightTerm(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        window.getSourceViewFrame().getSourceView().removeHighlights(HL_KEY);
    }

    private void showTerm(@Nonnull MainWindow window, @Nonnull KeYMediator mediator, PosInSequent pos, Term t) {
        shownTerm = new Tuple<>(pos, t);

        var proof = mediator.getSelectedProof();

        try {
            StringBuilder txt = new StringBuilder();

            if (showSectionRepr) {
                txt.append("----------<TOSTRING>----------\n");
                txt.append("\n");
                txt.append("ToStr<OriginRef>: ").append(Utils.TermToOrigString(t, proof.getServices())).append("\n");
                txt.append("ToStr<Fallback>:  ").append(Utils.TermToString(t, proof.getServices(), true)).append("\n");
                txt.append("\n");
            }

            if (showSectionSelf) {
                txt.append("----------<SELF>----------\n");
                txt.append("\n");

                if (t instanceof TermImpl) {
                    TermImpl term = (TermImpl)t;

                    {
                        OriginRef o = term.getOriginRef();
                        if(o != null) {
                            txt.append(o.toString());
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

                    OriginRef o = term.getOriginRef();
                    if (o != null && o.hasFile()) {
                        for (int i = o.LineStart; i <= o.LineEnd; i++) {
                            var str = Utils.getLines(mediator, o.File, i, i);
                            txt.append(str.stripTrailing()).append("\n");
                            str = " ".repeat(o.ColumnStart - 1) + "[" + Utils.safeSubstring(str, o.ColumnStart, o.ColumnEnd) + "]" + " ".repeat(o.ColumnEnd - 1);
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
                    TermImpl term = (TermImpl)t;

                    for (OriginRef o : Utils.getSubOriginRefs(term, false, showOnlyAtoms)) {
                        txt.append(o.toString());
                        txt.append("\n");
                    }

                }

                txt.append("\n");
            }

            if (showSectionParent) {
                txt.append("----------<PARENT>----------\n");
                txt.append("\n");

                Term parent = Utils.getParentWithOriginRef(pos, showOnlyAtoms, false);
                if (parent != null && parent != pos.getPosInOccurrence().subTerm() && parent.getOriginRef() != null) {
                    txt.append("ToStr<OriginRef>: ").append(Utils.TermToOrigString(parent, proof.getServices())).append("\n");
                    txt.append("ToStr<Fallback>:  ").append(Utils.TermToString(parent, proof.getServices(), true)).append("\n");
                    txt.append("\n");
                    {
                        OriginRef o = parent.getOriginRef();
                        if (o != null) {
                            txt.append(o.toString());
                            txt.append("\n");
                        }
                    }
                }

                txt.append("\n");
            }

            taSource.setText(txt.toString());
        } catch (IOException | URISyntaxException e) {
            taSource.setText(e.toString());
        }
    }

    private void unshowTerm(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        shownTerm = null;

        taSource.setText("");
    }
}