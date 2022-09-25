package org.key_project.termorigin;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.SequentInteractionListener;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.nodeviews.SequentView;
import de.uka.ilkd.key.gui.sourceview.SourceView;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermImpl;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.origin.TermOrigin;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofJavaSourceCollection;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.java.IOUtil;

import javax.annotation.Nonnull;
import javax.swing.*;
import java.awt.*;
import java.io.IOException;
import java.io.InputStream;
import java.net.MalformedURLException;
import java.net.URI;
import java.util.ArrayList;
import java.util.Objects;
import java.util.stream.Collectors;

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

                for (TermOrigin o : term.getTermOrigin()) {
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

                for (TermOrigin o : getSubOrigins(term)) {
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

    private ArrayList<TermOrigin> getSubOrigins(TermImpl term) {
        ArrayList<TermOrigin> r = new ArrayList<>();

        for (Term t : term.subs()) {
            if (t instanceof TermImpl) {
                r.addAll(((TermImpl)t).getTermOrigin().toList());
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