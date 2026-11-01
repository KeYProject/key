/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof;

import java.io.Serializable;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

@NullMarked
public class ProofNodeDescription implements Serializable {
    /**
     * Collects the information from the tree to which branch the current node belongs:
     * <ul>
     * <li>Invariant Initially Valid</li>
     * <li>Body Preserves Invariant</li>
     * <li>Use Case</li>
     * <li>...</li>
     * </ul>
     *
     * @param node the current node
     * @return a String containing the path information to display
     *         <p>
     *         The branch label of a node is present whenever the node carries one; the dereferences
     *         of
     *         the (nullable) label are suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:dereference.of.nullable")
    public static String collectPathInformation(@Nullable Node node) {
        while (node != null) {
            if (node.getNodeInfo() != null && node.getNodeInfo().getBranchLabel() != null) {
                String label = node.getNodeInfo().getBranchLabel();
                /*
                 * Are there other interesting labels? Please feel free to add them here.
                 */
                if (label.equals("Invariant Initially Valid")
                        || label.equals("Invariant Preserved and Used") // for loop scope invariant
                        || label.equals("Body Preserves Invariant") || label.equals("Use Case")
                        || label.equals("Show Axiom Satisfiability") || label.startsWith("Pre (")
                        || label.startsWith("Exceptional Post (") // exceptional postcondition
                        || label.startsWith("Post (") // postcondition of a method
                        || label.contains("Normal Execution") || label.contains("Null Reference")
                        || label.contains("Index Out of Bounds") || label.contains("Validity")
                        || label.contains("Precondition") || label.contains("Usage")) {
                    return label;
                }
            }
            node = node.parent();
        }
        // if no label was found we have to prove the postcondition
        return "Show Postcondition/Modifiable";
    }
}
