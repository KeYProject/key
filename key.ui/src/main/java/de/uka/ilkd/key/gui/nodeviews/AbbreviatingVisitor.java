/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.nodeviews;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.pp.AbbrevException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.rule.AbstractLoopInvariantRule;

import static de.uka.ilkd.key.logic.label.ParameterlessTermLabel.ANON_HEAP_LABEL;

/**
 * Visitor that will automatically abbreviate any anon heaps associated with loops.
 *
 * @author Arne Keller
 */
public class AbbreviatingVisitor implements Visitor {
    /**
     * The anon function from the heap LDT.
     */
    private final Function anon;
    /**
     * Abbreviation map of the visited proof.
     */
    private final AbbrevMap abbrevMap;

    /**
     * Construct new abbreviating visitor.
     *
     * @param services services of a proof
     */
    public AbbreviatingVisitor(Services services) {
        anon = services.getTypeConverter().getHeapLDT().getAnon();
        abbrevMap = services.getProof().abbreviations();
    }

    @Override
    public boolean visitSubtree(Term visited) {
        return true;
    }

    @Override
    public void visit(Term visited) {
        if (visited.op() == anon && visited.subs().size() == 3) {
            TermLabel label = visited.sub(2).getLabel(ANON_HEAP_LABEL.name());
            if (label == null) {
                return;
            }
            var parts = visited.sub(2).op().name().toString().split("_");
            if (parts.length >= 2 && parts[parts.length - 2]
                    .equals(AbstractLoopInvariantRule.ANON_HEAP_NAME_SUFFIX)) {
                int number = Integer.parseInt(parts[parts.length - 1]);
                String key = "heap_loop_" + number;
                if (!abbrevMap.containsAbbreviation(key) && !abbrevMap.containsTerm(visited)) {
                    try {
                        abbrevMap.put(visited, key, true);
                    } catch (AbbrevException e) {
                        // unreachable, as we just checked this above
                        throw new IllegalStateException("AbbrevMap concurrently modified!");
                    }
                }
            }
        }
    }

    @Override
    public void subtreeEntered(Term subtreeRoot) {

    }

    @Override
    public void subtreeLeft(Term subtreeRoot) {

    }
}
