package org.key_project.extsourceview.debug.tabs;

import bibliothek.util.container.Tuple;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.SequentInteractionListener;
import de.uka.ilkd.key.gui.sourceview.SourceView;
import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermImpl;
import de.uka.ilkd.key.logic.origin.OriginRef;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;
import org.key_project.extsourceview.SourceViewPatcher;
import org.key_project.extsourceview.Utils;
import org.key_project.extsourceview.debug.DebugTab;
import org.key_project.extsourceview.transformer.*;

import javax.annotation.Nonnull;
import javax.swing.*;
import javax.swing.text.BadLocationException;
import java.awt.*;
import java.io.IOException;
import java.net.URI;
import java.net.URISyntaxException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.stream.Collectors;

import static org.key_project.extsourceview.debug.tabs.GUIUtil.gbc;

/**
 * Class for the [Java Stmts Position] Tab in the debug panel
 *
 * Displays a bunch of information about the currently hovered term (in GoalView)
 */
public class JavaPosView extends DebugTab {

    private JTextArea taSource;

    private HashMap<PositionInfo, String> sourceStringCache = new HashMap<>();

    private boolean triggerOnClick = false;

    public JavaPosView(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        super();

        // add a listener for hover in the proof tree
        mediator.addSequentInteractionListener(new SequentInteractionListener() {
            @Override
            public void hover(PosInSequent pos, Term t) {
                if (!JavaPosView.this.triggerOnClick) {
                    show(window, mediator, pos, t);
                }
            }

            @Override
            public void leaveHover() {
                if (!JavaPosView.this.triggerOnClick) {
                    unshow(window, mediator);
                }
            }

            @Override
            public void click(PosInSequent pos, Term t) {
                if (JavaPosView.this.triggerOnClick) {
                    show(window, mediator, pos, t);
                }
            }
        });

        initGUI(window, mediator);
    }

    private void initGUI(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        setLayout(new BorderLayout());

        taSource = new JTextArea();
        taSource.setEditable(false);
        taSource.setFont(new Font("Courier New", Font.PLAIN, 12));
        taSource.setLineWrap(false);

        this.add(new JScrollPane(taSource), BorderLayout.CENTER);


        var pnlConf = new JPanel(new GridBagLayout());

        {
            var cbClick = new JCheckBox("Trigger on click", false);
            pnlConf.add(cbClick, gbc(0, 0));
            cbClick.addItemListener(e -> {
                JavaPosView.this.triggerOnClick = cbClick.isSelected();
            });
            JavaPosView.this.triggerOnClick = cbClick.isSelected();
        }

        this.add(pnlConf, BorderLayout.NORTH);
    }

    @Nonnull
    @Override
    public String getTitle() {
        return "Java Stmt Pos";
    }

    private void show(@Nonnull MainWindow window, @Nonnull KeYMediator mediator, PosInSequent pos, Term t) {
        if (t.javaBlock().isEmpty()) {
            taSource.setText("NO JAVA BLOCK");
            return;
        }

        StringBuilder strbuilder = new StringBuilder();

        for (var elem: listAll(t.javaBlock().program())) {
            var pi = elem.first.getPositionInfo();

            strbuilder.
                    append(String.format("%-48s", "  ".repeat(elem.second) + elem.first.getClass().getSimpleName())).
                    append(" ").
                    append(fmtPosInfo(pi)).
                    append(" ").
                    append(fmtSource(pi)).
                    append(" ").
                    append(fmtURI(pi.getURI())).
                    append("\n");

        }

        taSource.setText(strbuilder.toString());
    }

    private String fmtPosInfo(PositionInfo pi) {

        if (!pi.startEndValid()) {
            return "                 ";
        }

        var sb = new StringBuilder();

        sb.append("[");
        sb.append(String.format("%02d", pi.getStartPosition().getLine()));
        sb.append(":");
        sb.append(String.format("%02d", pi.getStartPosition().getColumn()));
        sb.append("]");
        sb.append(" - ");
        sb.append("[");
        sb.append(String.format("%02d", pi.getEndPosition().getLine()));
        sb.append(":");
        sb.append(String.format("%02d", pi.getEndPosition().getColumn()));
        sb.append("]");

        return sb.toString();
    }

    private String fmtSource(PositionInfo pi) {
        if (pi.getStartPosition().getLine() != pi.getEndPosition().getLine()) {
            return "= " + String.format("%-16s", "(multi-line)") + "  ";
        }

        return "= " + String.format("%-16s", "'"+getSourceString(pi)+"'") + "  ";
    }

    private String getSourceString(PositionInfo pi) {
        if (pi.getURI() == PositionInfo.UNKNOWN_URI) {
            return "";
        }

        if (sourceStringCache.containsKey(pi)) {
            return sourceStringCache.get(pi);
        }

        try {
            List<String> lines = Files.readAllLines(Path.of(pi.getURI()));

            var LineStart = pi.getStartPosition().getLine();
            var LineEnd = pi.getEndPosition().getLine();

            var ColumnStart = pi.getStartPosition().getColumn();
            var ColumnEnd = pi.getEndPosition().getColumn();

            StringBuilder r = new StringBuilder();
            for (int i = LineStart; i <= LineEnd; i++) {
                if (i - 1 < lines.size()) {
                    String line = lines.get(i - 1);
                    if (i == LineStart && i == LineEnd) {
                        r.append(Utils.safeSubstring(line, ColumnStart, ColumnEnd));
                    } else if (i == LineStart) {
                        r.append(Utils.safeSubstring(line, ColumnStart, line.length()));
                        r.append("\n");
                    } else if (i == LineEnd) {
                        r.append(Utils.safeSubstring(line, 0, ColumnEnd));
                    } else {
                        r.append(line);
                        r.append("\n");
                    }
                }
            }
            sourceStringCache.put(pi, r.toString());
            return r.toString();
        } catch (Exception e) {
            sourceStringCache.put(pi, null);
            return null;
        }
    }

    private String fmtURI(URI u) {
        if (u == PositionInfo.UNKNOWN_URI) {
            return "UNKNOWN";
        }

        String str = u.toString();
        if (str.startsWith("file:/") && str.endsWith(".java")) {
            String[] arr = str.split("/");
            return arr[arr.length-1];
        }
        return str;
    }

    private void unshow(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        taSource.setText("");
    }

    private java.util.List<Pair<ProgramElement, Integer>> listAll(ProgramElement base) {
        var ls = new ArrayList<Pair<ProgramElement, Integer>>();
        listAll(ls, base, 0);
        return ls;
    }

    private void listAll(java.util.List<Pair<ProgramElement, Integer>> ls, ProgramElement elem, int depth) {
        ls.add(new Pair<>(elem, depth));

        if (elem instanceof NonTerminalProgramElement) {
            var ntpe = (NonTerminalProgramElement)elem;
            for (int i = 0; i < ntpe.getChildCount(); i++) {
                listAll(ls, ntpe.getChildAt(i), depth+1);
            }
        }
    }
}
