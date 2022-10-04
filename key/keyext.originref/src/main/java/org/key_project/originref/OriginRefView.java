package org.key_project.originref;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.SequentInteractionListener;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.sourceview.SourceView;
import de.uka.ilkd.key.logic.PosInOccurrence;
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
import java.util.stream.Collectors;

public class OriginRefView extends JPanel implements TabPanel {

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

    }

    @Nonnull
    @Override
    public String getTitle() {
        return "TermOrigin Inspector";
    }

    private JPanel pnlMain;
    private JTextArea taSource;

    private final ArrayList<SourceView.Highlight> existingHighlights = new ArrayList<>();

    private void highlightTerm(@Nonnull MainWindow window, @Nonnull KeYMediator mediator, PosInSequent pos, Term t) {
        try {
            SourceView sv = window.getSourceViewFrame().getSourceView();
            for (SourceView.Highlight h : existingHighlights) sv.removeHighlight(h);
            existingHighlights.clear();

            for (OriginRef o : ESVUtil.getParentWithOriginRef(pos).getOriginRef()) {
                for (int i = o.LineStart; i <= o.LineEnd; i++) {
                    existingHighlights.add(sv.addHighlight(o.fileURI(), i, Color.MAGENTA, 11));
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
            txt += ESVUtil.TermToString(t, proof.getServices()) + "\n";
            txt += "\n";
            txt += "----------<SELF>----------";
            txt += "\n";
            txt += "\n";

            if (t instanceof TermImpl) {
                TermImpl term = (TermImpl)t;

                for (OriginRef o : term.getOriginRef()) {
                    txt += "File: " + o.File + "\n";
                    txt += "Line: " + o.LineStart + " - " + o.LineEnd + "\n";
                    txt += "Pos:  " + o.PositionStart + " - " + o.PositionEnd + "\n";
                    txt += "Type: " + o.Type + "\n";
                    txt += "\n";
                }
                txt += "----------";
                txt += "\n";
                txt += "\n";

                for (OriginRef o : term.getOriginRef()) {
                    txt += ESVUtil.getLines(mediator, o.File, o.LineStart, o.LineEnd) + "\n";
                    txt += "\n";
                }

            }

            txt += "----------<CHILDS>----------";
            txt += "\n";
            txt += "\n";

            if (t instanceof TermImpl) {
                TermImpl term = (TermImpl)t;

                for (OriginRef o : getSubOrigins(term, false)) {
                    txt += "File: " + o.File + "\n";
                    txt += "Line: " + o.LineStart + " - " + o.LineEnd + "\n";
                    txt += "Pos:  " + o.PositionStart + " - " + o.PositionEnd + "\n";
                    txt += "Type: " + o.Type + "\n";
                    txt += "\n";
                }

            }

            txt += "----------<PARENT>----------";
            txt += "\n";
            txt += "\n";

            Term parent = ESVUtil.getParentWithOriginRef(pos);
            if (!parent.getOriginRef().isEmpty()) {
                txt += ESVUtil.TermToString(parent, proof.getServices()) + "\n";
                txt += "\n";
                for (OriginRef o : parent.getOriginRef()) {
                    txt += "File: " + o.File + "\n";
                    txt += "Line: " + o.LineStart + " - " + o.LineEnd + "\n";
                    txt += "Pos:  " + o.PositionStart + " - " + o.PositionEnd + "\n";
                    txt += "Type: " + o.Type + "\n";
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
        for (SourceView.Highlight h: existingHighlights) sv.removeHighlight(h);
        existingHighlights.clear();

        taSource.setText("");
    }

    private ArrayList<OriginRef> getSubOrigins(TermImpl term, boolean includeSelf) {
        ArrayList<OriginRef> r = new ArrayList<>();

        if (includeSelf) {
            for (OriginRef o: term.getOriginRef()) r.add(o);
        }

        for (Term t : term.subs()) {
            if (t instanceof TermImpl) {
                for (OriginRef o: t.getOriginRef()) r.add(o);
                r.addAll(getSubOrigins((TermImpl)t, false));
            }
        }

        return r;
    }

    @Nonnull
    @Override
    public JComponent getComponent() {
        if (pnlMain == null)
        {
            pnlMain = new JPanel(new BorderLayout());
            taSource = new JTextArea();
            taSource.setEditable(false);
            taSource.setFont(new Font("Courier New", Font.PLAIN, 12));
            pnlMain.add(new JScrollPane(taSource), BorderLayout.CENTER);
        }
        return pnlMain;
    }
}