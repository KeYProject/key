/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.rusty.rule.MatchConditions;

public interface RustyProgramElement extends SyntaxElement {
    default MatchConditions match(SourceData sourceData, MatchConditions mc) {
        final var src = sourceData.getSource();

        if (src == null)
            return null;

        if (src.getClass() != this.getClass()) {
            return null;
        }

        final SourceData newSource = new SourceData(src, 0, sourceData.getServices());

        mc = matchChildren(newSource, mc, 0);

        if (mc == null) {
            return null;
        }

        sourceData.next();
        return mc;
    }

    /**
     * matches successively all children of this current node. Thereby the <tt>offset</tt>-th child
     * is matched against <code>source.getSource()</code>. The call <tt>source.next</tt> has to be
     * done in the @link ProgramElement#match method of the currently matched child in case of a
     * successful match. This is <em>not</em> done here (rationale: schemavariables matching on
     * lists can be implemented easy).
     *
     *
     * @param source the SourceData with the children to be matched
     * @param matchCond the MatchConditions found so far
     * @param offset the int denoting the index of the child to start with
     * @return the resulting match conditions or <tt>null</tt> if matching failed
     */
    default MatchConditions matchChildren(SourceData source, MatchConditions matchCond,
            int offset) {

        for (int i = offset, sz = getChildCount(); i < sz; i++) {
            var child = (RustyProgramElement) getChild(i);
            matchCond = child.match(source, matchCond);
            if (matchCond == null) {
                return null;
            }
        }

        final var src = source.getElement();

        if (!compatibleBlockSize(source.getChildPos(), src.getChildCount())) {
            return null;
        }

        return matchCond;
    }

    /**
     * used by @link matchChildren to decide if a found match is valid or if there are remaining
     * source elements that have not been matched (in which case the match failed)
     */
    default boolean compatibleBlockSize(int pos, int max) {
        return pos >= max;
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    void visit(Visitor v);
}
