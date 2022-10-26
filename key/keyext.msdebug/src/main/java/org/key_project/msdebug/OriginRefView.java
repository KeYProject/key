package org.key_project.msdebug;

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

    private JTextArea taSource;

    private final static int HIGHTLIGHT_LEVEL = 11;

    private boolean showOnlyAtoms = true;
    private boolean triggerOnClick = false;

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

        initGUI();
    }

    private void initGUI() {
        setLayout(new BorderLayout());

        taSource = new JTextArea();
        taSource.setEditable(false);
        taSource.setFont(new Font("Courier New", Font.PLAIN, 12));

        this.add(new JScrollPane(taSource), BorderLayout.CENTER);


        var pnlConf = new JPanel(new GridLayout(2, 1, 8, 8));

        var cbClick = new JCheckBox("trigger on click");
        pnlConf.add(cbClick);
        cbClick.addItemListener(e -> { OriginRefView.this.triggerOnClick = cbClick.isSelected(); });


        var cbAtom = new JCheckBox("only show atoms", true);
        pnlConf.add(cbAtom);
        cbAtom.addItemListener(e -> { OriginRefView.this.showOnlyAtoms = cbAtom.isSelected(); });

        this.add(pnlConf, BorderLayout.NORTH);
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
                    existingHighlights.add(sv.addHighlight(orig.fileURI(), orig.LineStart, orig.ColumnStart, orig.ColumnEnd, COL_HIGHLIGHT_MAIN, HIGHTLIGHT_LEVEL));
                } else {
                    for (int i = orig.LineStart; i <= orig.LineEnd; i++) {
                        if (orig.hasFile()) {
                            existingHighlights.add(sv.addHighlight(orig.fileURI(), i, COL_HIGHLIGHT_MAIN, HIGHTLIGHT_LEVEL));
                        }
                    }
                }
            }

        } catch (IOException | BadLocationException e) {
            e.printStackTrace();
        }
    }

    private void showTerm(@Nonnull MainWindow window, @Nonnull KeYMediator mediator, PosInSequent pos, Term t) {
        var proof = mediator.getSelectedProof();

        try {
            String txt = "";
            txt += MSDUtil.TermToString(t, proof.getServices()) + "\n";
            txt += "\n";
            txt += "----------<SELF>----------";
            txt += "\n";
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
                txt += "\n";
                txt += "----------<SOURCE>----------";
                txt += "\n";
                txt += "\n";

                {
                    OriginRef o = term.getOriginRef();
                    if (o != null && o.hasFile()) {
                        for (int i = o.LineStart; i <= o.LineEnd; i++) {
                            var str = MSDUtil.getLines(mediator, o.File, i, i);
                            txt += str.stripTrailing() + "\n";
                            str = " ".repeat(o.ColumnStart -1) + "[" + MSDUtil.safeSubstring(str, o.ColumnStart, o.ColumnEnd) + "]" + " ".repeat(o.ColumnEnd -1);
                            txt += str + "\n";
                            txt += "\n";
                        }
                    }
                }

            }

            txt += "----------<CHILDREN>----------";
            txt += "\n";
            txt += "\n";

            if (t instanceof TermImpl) {
                TermImpl term = (TermImpl)t;

                for (OriginRef o : MSDUtil.getSubOriginRefs(term, false, showOnlyAtoms)) {
                    txt += o.toString();
                    txt += "\n";
                }

            }

            txt += "\n";

            txt += "----------<PARENT>----------";
            txt += "\n";
            txt += "\n";

            Term parent = MSDUtil.getParentWithOriginRef(pos, showOnlyAtoms);
            if (parent != pos.getPosInOccurrence().subTerm() && parent.getOriginRef() != null) {
                txt += MSDUtil.TermToString(parent, proof.getServices()) + "\n";
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

            taSource.setText(txt);
        } catch (IOException | URISyntaxException e) {
            taSource.setText(e.toString());
        }
    }

    private void unhighlightTerm(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        SourceView sv = window.getSourceViewFrame().getSourceView();
        for (SourceViewHighlight h: existingHighlights) sv.removeHighlight(h);
        existingHighlights.clear();
    }

    private void unshowTerm(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        taSource.setText("");
    }
}