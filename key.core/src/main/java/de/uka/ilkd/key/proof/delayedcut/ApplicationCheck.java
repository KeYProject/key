/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.delayedcut;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;

/**
 * Determines conflicts relevant for a delayed cut application.
 *
 * @author Benjamin Niedermann
 */
public interface ApplicationCheck {

    /**
     * @param cutNode The node at which to apply the delayed cut.
     * @param cutFormula The cut formula.
     * @return A String representation of a possible conflict affecting a delayed cut application
     *         for the given node and cut formula or null if there is no conflict.
     */
    String check(Node cutNode, Term cutFormula);

    /**
     * Implementation of an ApplicationCheck which examines if there are new symbols introduced
     * below the cut node. The existence of such symbols prohibits the replay procedure: This
     * restriction ensures that symbols introduced within the respective subtrees are actually new
     * symbols, as required by the corresponding rule definitions.
     *
     * @author Benjamin Niedermann
     */
    class NoNewSymbolsCheck implements ApplicationCheck {
        private Node node;
        private final Set<String> names = new TreeSet<>();

        private static final String INFORMATION1 =
            "The formula contains a symbol that has been introduced below Node ";
        private static final String INFORMATION2 =
            "The formula contains symbols that have been introduced below Node ";
        private static final String ADD_INFORMATION =
            "The formula that you specify at this point will be introduced at the inner node %i\n"
                + "of the proof tree by using a cut. Afterwards, the sub-trees of that node will be replayed.\n"
                + "In order to sustain the correctness of the proof, the formula must therefore not contain symbols\n"
                + "that have been introduced in the sub-trees of Node %i. In particular this restriction ensures\n"
                + "that symbols that are introduced within the subtrees of Node %i are actually new symbols\n"
                + "as required by the corresponding rule definitions.";

        @Override
        public String check(Node cutNode, Term cutFormula) {
            if (cutNode == null) {
                throw new IllegalArgumentException("cutNode is null");
            }
            if (node != cutNode) {
                node = cutNode;
                clearCaches();
                buildCaches(node);
            }

            return checkFormula(cutFormula);
        }

        private void clearCaches() {
            names.clear();
            node.clearNameCache();
        }

        private void buildCaches(Node cutNode) {
            LinkedList<Node> queue = new LinkedList<>();
            queue.add(cutNode);
            while (!queue.isEmpty()) {
                Node next = queue.pollFirst();
                if (next.getNameRecorder() != null) {
                    for (Name name : next.getNameRecorder().getProposals()) {
                        names.add(name.toString());
                    }
                }

                for (Iterator<Node> it = next.childrenIterator(); it.hasNext();) {
                    queue.add(it.next());
                }
            }
        }

        private String checkFormula(Term formula) {
            final List<String> newSymbols = new LinkedList<>();
            formula.execPreOrder(new DefaultVisitor() {
                @Override
                public void visit(Term visited) {
                    String name = visited.op().name().toString();
                    if (names.contains(name)) {
                        newSymbols.add(name);
                    }
                }
            });

            if (newSymbols.isEmpty()) {
                return null;
            }

            StringBuilder buf =
                new StringBuilder(newSymbols.size() == 1 ? INFORMATION1 : INFORMATION2);
            buf.append(node.serialNr()).append(": ");
            for (String name : newSymbols) {
                buf.append(name);
                buf.append(", ");
            }
            buf.replace(buf.length() - 2, buf.length(),
                ". (For more information click on this message)");
            buf.append("#");

            buf.append(ADD_INFORMATION.replaceAll("%i", Integer.toString(node.serialNr())));

            return buf.toString();
        }

        @Override
        public String toString() {
            return "NoNewSymbolsCheck [node=" + node.serialNr() + ", names=" + names + "]";
        }
    }
}
