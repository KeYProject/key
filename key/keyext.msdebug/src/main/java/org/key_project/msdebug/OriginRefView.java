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

    public OriginRefView(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        super();

        // add a listener for hover in the proof tree
        mediator.addSequentInteractionListener(new SequentInteractionListener() {
            @Override
            public void hover(PosInSequent pos, Term t) {
                highlightTerm(window, mediator, pos, t);
                showTerm(window, mediator, pos, t);
            }

            @Override
            public void leaveHover() {
                unshowTerm(window, mediator);
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

            boolean anyRefs = false;

            for (OriginRef o : MSDUtil.getParentWithOriginRef(pos).getOriginRef()) {
                highlightOriginRef(sv, o);
                anyRefs = true;
            }

            if (!anyRefs) {
                for (OriginRef o : MSDUtil.getSubOriginRefs(pos.getPosInOccurrence().subTerm(), false)) {
                    highlightOriginRef(sv, o);
                }
            }

        } catch (IOException | BadLocationException e) {
            e.printStackTrace();
        }
    }

    private void highlightOriginRef(SourceView sv, OriginRef orig) throws BadLocationException, IOException {
        if (!orig.hasFile()) return;

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

                for (OriginRef o : term.getOriginRef()) {
                    txt += o.toString();
                    txt += "\n";
                }
                txt += "\n";
                txt += "----------<SOURCE>----------";
                txt += "\n";
                txt += "\n";

                for (OriginRef o : term.getOriginRef()) {
                    if (o.hasFile()) {
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

                for (OriginRef o : MSDUtil.getSubOriginRefs(term, false)) {
                    txt += o.toString();
                    txt += "\n";
                }

            }

            txt += "\n";

            txt += "----------<PARENT>----------";
            txt += "\n";
            txt += "\n";

            Term parent = MSDUtil.getParentWithOriginRef(pos);
            if (parent != pos.getPosInOccurrence().subTerm() && !parent.getOriginRef().isEmpty()) {
                txt += MSDUtil.TermToString(parent, proof.getServices()) + "\n";
                txt += "\n";
                for (OriginRef o : parent.getOriginRef()) {
                    txt += o.toString();
                    txt += "\n";
                }
            }

            txt += "\n";

            taSource.setText(txt);
        } catch (IOException | URISyntaxException e) {
            taSource.setText(e.toString());
        }
    }

    private void unshowTerm(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        SourceView sv = window.getSourceViewFrame().getSourceView();
        for (SourceViewHighlight h: existingHighlights) sv.removeHighlight(h);
        existingHighlights.clear();

        taSource.setText("");
    }
}