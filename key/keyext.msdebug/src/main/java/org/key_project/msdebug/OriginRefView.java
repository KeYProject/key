package org.key_project.msdebug;

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

import javax.annotation.Nonnull;
import javax.swing.*;
import javax.swing.text.BadLocationException;
import java.awt.*;
import java.io.IOException;
import java.net.URISyntaxException;
import java.util.ArrayList;

public class OriginRefView extends MSDebugTab {

    private final static Color COL_HIGHLIGHT_MAIN = new Color(255, 0, 255);
    private final static Color COL_HIGHLIGHT_CHILDS = new Color(255, 128, 255);

    private final static String HL_KEY = "OriginRefView::highlight";

    private JTextArea taSource;

    private final static int HIGHTLIGHT_LEVEL = 11;

    private boolean showOnlyAtoms = true;
    private boolean triggerOnClick = false;

    private boolean showSectionRepr = true;
    private boolean showSectionSelf = true;
    private boolean showSectionSource = true;
    private boolean showSectionChildren = true;
    private boolean showSectionParent = true;

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

    private final ArrayList<SourceViewHighlight> existingHighlights = new ArrayList<>();

    private void highlightTerm(@Nonnull MainWindow window, @Nonnull KeYMediator mediator, PosInSequent pos, Term t) {
        try {
            SourceView sv = window.getSourceViewFrame().getSourceView();
            for (SourceViewHighlight h : existingHighlights) sv.removeHighlight(h);
            existingHighlights.clear();

            for (OriginRef orig : MSDUtil.getSubOriginRefs(pos.getPosInOccurrence().subTerm(), true, true)) {
                if (!orig.hasFile()) continue;

                if (!sv.hasFile(orig.fileURI())) continue;

                if (orig.LineStart == orig.LineEnd) {
                    existingHighlights.add(sv.addHighlight(orig.fileURI(), HL_KEY, orig.LineStart, orig.ColumnStart, orig.ColumnEnd, COL_HIGHLIGHT_MAIN, HIGHTLIGHT_LEVEL));
                } else {
                    for (int i = orig.LineStart; i <= orig.LineEnd; i++) {
                        if (orig.hasFile()) {
                            existingHighlights.add(sv.addHighlight(orig.fileURI(), HL_KEY, i, COL_HIGHLIGHT_MAIN, HIGHTLIGHT_LEVEL));
                        }
                    }
                }
            }

        } catch (IOException | BadLocationException e) {
            e.printStackTrace();
        }
    }

    private void unhighlightTerm(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        SourceView sv = window.getSourceViewFrame().getSourceView();
        for (SourceViewHighlight h: existingHighlights) sv.removeHighlight(h);
        existingHighlights.clear();
    }

    private void showTerm(@Nonnull MainWindow window, @Nonnull KeYMediator mediator, PosInSequent pos, Term t) {
        shownTerm = new Tuple<>(pos, t);

        var proof = mediator.getSelectedProof();

        try {
            String txt = "";

            if (showSectionRepr) {
                txt += "----------<TOSTRING>----------\n";
                txt += "\n";
                txt += "ToStr<OriginRef>: " + MSDUtil.TermToOrigString(t, proof.getServices()) + "\n";
                txt += "ToStr<Fallback>:  " + MSDUtil.TermToString(t, proof.getServices(), true) + "\n";
                txt += "\n";
            }

            if (showSectionSelf) {
                txt += "----------<SELF>----------\n";
                txt += "\n";

                if (t instanceof TermImpl) {
                    TermImpl term = (TermImpl)t;

                    {
                        OriginRef o = term.getOriginRef();
                        if(o != null) {
                            txt += o.toString();
                            txt += "\n";
                        }
                    }
                }
                txt += "\n";
            }

            if (showSectionSource) {
                txt += "----------<SOURCE>----------\n";
                txt += "\n";
                if (t instanceof TermImpl) {
                    TermImpl term = (TermImpl) t;

                    OriginRef o = term.getOriginRef();
                    if (o != null && o.hasFile()) {
                        for (int i = o.LineStart; i <= o.LineEnd; i++) {
                            var str = MSDUtil.getLines(mediator, o.File, i, i);
                            txt += str.stripTrailing() + "\n";
                            str = " ".repeat(o.ColumnStart - 1) + "[" + MSDUtil.safeSubstring(str, o.ColumnStart, o.ColumnEnd) + "]" + " ".repeat(o.ColumnEnd - 1);
                            txt += str + "\n";
                            txt += "\n";
                        }
                    }
                }
            }

            if (showSectionChildren) {
                txt += "----------<CHILDREN>----------\n";
                txt += "\n";

                if (t instanceof TermImpl) {
                    TermImpl term = (TermImpl)t;

                    for (OriginRef o : MSDUtil.getSubOriginRefs(term, false, showOnlyAtoms)) {
                        txt += o.toString();
                        txt += "\n";
                    }

                }

                txt += "\n";
            }

            if (showSectionParent) {
                txt += "----------<PARENT>----------\n";
                txt += "\n";

                Term parent = MSDUtil.getParentWithOriginRef(pos, showOnlyAtoms);
                if (parent != pos.getPosInOccurrence().subTerm() && parent.getOriginRef() != null) {
                    txt += "ToStr<OriginRef>: " + MSDUtil.TermToOrigString(parent, proof.getServices()) + "\n";
                    txt += "ToStr<Fallback>:  " + MSDUtil.TermToString(parent, proof.getServices(), true) + "\n";
                    txt += "\n";
                    {
                        OriginRef o = parent.getOriginRef();
                        if (o != null) {
                            txt += o.toString();
                            txt += "\n";
                        }
                    }
                }

                txt += "\n";
            }

            taSource.setText(txt);
        } catch (IOException | URISyntaxException e) {
            taSource.setText(e.toString());
        }
    }

    private void unshowTerm(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        shownTerm = null;

        taSource.setText("");
    }
}