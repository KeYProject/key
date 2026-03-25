/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast;


import com.github.javaparser.ast.jml.clauses.JmlContract;
import de.uka.ilkd.key.rule.MatchConditions;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.Nullable;

/**
 * A part of the program syntax that carries semantics in the model. taken from COMPOST and changed
 * to achieve an immutable structure
 */
public interface ProgramElement extends SourceElement, ModelElement {


    /**
     * Get comments.
     *
     * @return the comments.
     */
    Comment[] getComments();

    ///
    default ImmutableList<JmlContract> getAttachedJml() {
        return ImmutableSLList.nil();
    }


    /**
     * matches the source "text" (@link SourceData#getSource()) against the pattern represented by
     * this object. In case of a successful match the resulting {@link MatchConditions} with the
     * found instantiations of the schemavariables. If the match failed, <tt>null</tt> is returned
     * instead.
     *
     * @param source the SourceData with the program element to match
     * @param matchCond the MatchConditions found up to this point
     * @return the resulting match conditions or <tt>null</tt> if the match failed
     */
    @Nullable
    MatchConditions match(SourceData source, MatchConditions matchCond);
}
