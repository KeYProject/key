// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof.join;

import java.util.Comparator;
import java.util.Iterator;
import java.util.TreeSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.parser.KeYLexerF;
import de.uka.ilkd.key.parser.KeYParserF;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

/**
 * Responsible for estimating decision predicates for a join.
 *
 * @author Benjamin Niedermann
 */
public interface PredicateEstimator {
    public static final PredicateEstimator STD_ESTIMATOR = new StdPredicateEstimator();

    /**
     * @param partner
     *            Structure comprising the partners of a join.
     * @param proof
     *            The underlying proof.
     * @return A decision predicate for the two nodes in partner. The predicate
     *         should be true in the sequent of the first node and false in the
     *         sequent of the second node.
     */
    public Result estimate(ProspectivePartner partner, Proof proof);

    /**
     * Encapsulates a decision predicate for the delayed cut mechanism and the
     * common parent node at which to prune, i.e. apply the delayed cut.
     */
    public interface Result {
        Term getPredicate();

        Node getCommonParent();
    }
}

/**
 * Tries to determine the decision predicate. The information about the
 * predicate is extracted from the labels of branches in the proof.
 *
 * @author Benjamin Niedermann
 */
class StdPredicateEstimator implements PredicateEstimator {

    private static final String FALSE_LABEL = "FALSE";
    private static final String TRUE_LABEL = "TRUE";
    private static final String CUT_LABEL = "CUT:";

    @Override
    public Result estimate(ProspectivePartner partner, final Proof proof) {
        final Node node = getFirstDifferentNode(partner);
        String branchLabel = node.getNodeInfo().getBranchLabel();
        if (branchLabel != null
                && (branchLabel.endsWith(TRUE_LABEL) || branchLabel
                        .endsWith(FALSE_LABEL))) {
            final boolean positive = branchLabel.endsWith(TRUE_LABEL);
            String suffix = positive ? TRUE_LABEL : FALSE_LABEL;
            int index = branchLabel.lastIndexOf(suffix);
            branchLabel = branchLabel.substring(0, index);

            if (branchLabel.startsWith(CUT_LABEL)) {
                branchLabel = branchLabel.substring(CUT_LABEL.length());
            }

            final Term term = translate(branchLabel, proof.getServices());

            if (term != null) {
                return new Result() {

                    @Override
                    public Term getPredicate() {
                        if (!positive) {
                            return proof.getServices().getTermBuilder()
                                    .not(term);
                        }
                        return term;
                    }

                    @Override
                    public Node getCommonParent() {
                        return node.parent();
                    }
                };

            }

        }

        return new Result() {

            @Override
            public Term getPredicate() {
                // The decision predicate has to be specified by the user.
                return null;
            }

            @Override
            public Node getCommonParent() {
                return node.parent();
            }

        };
    }
    
    /**
     * Goes up to the common node of partner.getNode(0) and partner.getNode(1)
     * and returns the next node on the path to partner.getNode(0).
     *
     * @param partner The prospective partner object.
     * @return The next node on the path to partner.getNode(0).
     */
    private Node getFirstDifferentNode(ProspectivePartner partner) {
        TreeSet<Node> set = new TreeSet<Node>(new Comparator<Node>() {

            @Override
            public int compare(Node o1, Node o2) {

                return o1.serialNr() - o2.serialNr();
            }
        });

        Node node = partner.getNode(0);
        while (!node.root()) {
            set.add(node);
            node = node.parent();
        }
        if (node.root()) {
            set.add(node);
        }

        node = partner.getNode(1);
        while (node.parent() != null && !set.contains(node)) {
            node = node.parent();
        }

        if (set.contains(node)) {
            Iterator<Node> it = node.childrenIterator();
            while (it.hasNext()) {
                Node child = it.next();
                if (set.contains(child)) {
                    return child;
                }
            }
        }

        return null;
    }

    /**
     * Translates a branch label (without common prefixes such as "CUT:" etc.)
     * to a term.
     *
     * @param estimation
     *            The branch label without prefix.
     * @param services
     *            The services object.
     * @return A term corresponding to the branch label.
     */
    private Term translate(String estimation, Services services) {
        try {
            KeYParserF parser = new KeYParserF(ParserMode.TERM, new KeYLexerF(
                    estimation, ""), services, // should not be needed
                    services.getNamespaces());
            return parser.term();
        }
        catch (Throwable e) {

            return null;
        }
    }

}