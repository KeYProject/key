package de.uka.ilkd.key.gui.interactionlog.algo;

import de.uka.ilkd.key.gui.interactionlog.model.Interaction;
import de.uka.ilkd.key.gui.interactionlog.model.InteractionLog;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Node;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.HashMap;
import java.util.List;
import java.util.function.Function;

/**
 * @author weigl
 */
public class LogPrinter {
    public static String SEPARATOR = " // ";

    public static String RANGE_SEPARATOR = " -- ";

    public static String END_MARKER = "$$";
    private final Services services;
    private StringWriter w;
    private PrintWriter out;
    private Function<Node, String> matchExpr = LogPrinter::getBranchingLabel;
    private int indent = 0;
    private InteractionLog state;

    public LogPrinter(Services services) {
        this.services = services;
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

    private void body(HashMap<Interaction, List<Interaction>> tree,
                      Interaction interaction) {

        newline();
        //TODO out.write(interaction.getProofScriptRepresentation(services));

        List<Interaction> children = tree.get(interaction);
        if (children != null) {
            switch (children.size()) {
                case 1:
                    body(tree, children.get(0));
                    break;
                default:
                    newline();
                    out.write("cases {");
                    indent++;

                    for (Interaction c : children) {
                        newline();
                        out.write("case \"");
                        //TODO out.write(matchExpr.apply(c.getNode()));
                        out.write("\" {");
                        indent++;
                        body(tree, c);
                        indent--;
                        newline();
                        out.write("}");
                    }
                    indent--;
                    newline();
                    out.write("}");
                    break;
            }
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
