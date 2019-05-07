package de.uka.ilkd.key.gui.interactionlog.algo;

import de.uka.ilkd.key.gui.interactionlog.model.InteractionLog;
import de.uka.ilkd.key.proof.Node;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.function.Function;

/**
 * @author Alexander Weigl
 */
public class LogPrinter {
    public static String SEPARATOR = " // ";

    public static String RANGE_SEPARATOR = " -- ";

    public static String END_MARKER = "$$";
    private StringWriter w;
    private PrintWriter out;
    private Function<Node, String> matchExpr = LogPrinter::getBranchingLabel;
    private int indent = 0;
    private InteractionLog state;

    public LogPrinter() {
    }


    public static String getBranchingLabel(Node node) {
        StringBuilder sb = new StringBuilder();
        while (node != null) {
            Node p = node.parent();
            if (p != null && p.childrenCount() != 1) {
                String branchLabel = node.getNodeInfo().getBranchLabel();
                sb.append(branchLabel != null && !branchLabel.isEmpty()
                        ? branchLabel
                        : "#" + p.getChildNr(node))
                        .append(SEPARATOR);
            }
            node = p;
        }
        sb.append(END_MARKER);
        return sb.toString();
    }

    /**
     * prints an interaction log as a proof script.
     *
     * @param state a state
     * @return
     */
    public String print(InteractionLog state) {
        w = new StringWriter();
        out = new PrintWriter(w);
        this.state = state;
        indent = 0;
        header();
        body();
        footer();
        return w.toString();
    }

    private void header() {
        out.print("script main {");
        ++indent;
    }

    private void body() {
        if (state.getInteractions().size() != 0) {
            //HashMap<Interaction, List<Interaction>> tree = state.getInteractionTree();
            //body(tree, state.getInteractions().get(0));
        }
    }

    private void newline() {
        out.write("\n");
        for (int i = 0; i < indent; i++) {
            out.write("    ");
        }
    }

    private void footer() {
        --indent;
        newline();
        out.write("}\n");
    }

    public Function<Node, String> getMatchExpr() {
        return matchExpr;
    }

    public void setMatchExpr(Function<Node, String> matchExpr) {
        this.matchExpr = matchExpr;
    }
}
