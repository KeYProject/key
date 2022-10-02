package org.key_project.termorigin;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.SequentInteractionListener;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermImpl;
import de.uka.ilkd.key.logic.origin.OriginRef;

import javax.annotation.Nonnull;
import javax.swing.*;
import java.awt.*;
import java.io.IOException;
import java.util.ArrayList;

public class TermOriginView extends JPanel implements TabPanel {

    public TermOriginView(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        super();

        // add a listener for changes in the proof tree
        mediator.addSequentInteractionListener(new SequentInteractionListener() {
            @Override
            public void hover(Term t) {
                showTerm(mediator, t);
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

    private void showTerm(@Nonnull KeYMediator mediator, Term t) {
        var proof = mediator.getSelectedProof();

        try {
            String txt = "";
            txt += ESVUtil.TermToString(t, proof.getServices()) + "\n";
            txt += "\n";
            txt += "-------------------------";
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

            }

            txt += "-------------------------";
            txt += "\n";
            txt += "\n";

            if (t instanceof TermImpl) {
                TermImpl term = (TermImpl)t;

                for (OriginRef o : getSubOrigins(term)) {
                    txt += "File: " + o.File + "\n";
                    txt += "Line: " + o.LineStart + " - " + o.LineEnd + "\n";
                    txt += "Pos:  " + o.PositionStart + " - " + o.PositionEnd + "\n";
                    txt += "Type: " + o.Type + "\n";
                    txt += "\n";
                }

            }

            txt += "\n";

            taSource.setText(txt);
        } catch (IOException e) {
            taSource.setText(e.toString());
        }
    }

    private ArrayList<OriginRef> getSubOrigins(TermImpl term) {
        ArrayList<OriginRef> r = new ArrayList<>();

        for (Term t : term.subs()) {
            if (t instanceof TermImpl) {
                for (OriginRef o: t.getOriginRef()) r.add(o);
                r.addAll(getSubOrigins((TermImpl)t));
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