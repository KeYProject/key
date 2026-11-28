/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast.statement;

import java.util.List;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.pattern.Pattern;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * A {@code case} label group whose labels are patterns, optionally guarded with {@code when}
 * (JLS 14.11.1), e.g. {@code case Integer i when i > 0:}.
 */
@NullMarked
public class PatternCase extends BranchImp {

    private final ImmutableList<Pattern> patterns;
    private final @Nullable Expression guard;
    private final ImmutableList<Statement> body;

    /**
     * Creates a pattern case without source information.
     *
     * @param patterns the patterns of the label group
     * @param guard the optional {@code when} guard
     * @param body the statements of the arm
     */
    public PatternCase(ImmutableList<Pattern> patterns, @Nullable Expression guard,
            ImmutableList<Statement> body) {
        this(PositionInfo.UNDEFINED, List.of(), patterns, guard, body);
    }

    /**
     * Creates a pattern case.
     *
     * @param pi the position information
     * @param comments the comments attached to this branch
     * @param patterns the patterns of the label group
     * @param guard the optional {@code when} guard
     * @param body the statements of the arm
     */
    public PatternCase(PositionInfo pi, List<Comment> comments,
            ImmutableList<Pattern> patterns, @Nullable Expression guard,
            ImmutableList<Statement> body) {
        super(pi, comments);
        this.patterns = patterns;
        this.guard = guard;
        this.body = body;
    }

    /**
     * @return the patterns of this label group
     */
    public ImmutableList<Pattern> getPatterns() {
        return patterns;
    }

    /**
     * @return the {@code when} guard, or {@code null} if there is none
     */
    public @Nullable Expression getGuard() {
        return guard;
    }

    /**
     * @return the statements of this arm
     */
    public ImmutableList<Statement> getBody() {
        return body;
    }

    @Override
    public int getChildCount() {
        return patterns.size() + (guard != null ? 1 : 0) + body.size();
    }

    @Override
    public ProgramElement getChildAt(int index) {
        if (index < patterns.size()) {
            return patterns.get(index);
        }
        index -= patterns.size();
        if (guard != null) {
            if (index == 0) {
                return guard;
            }
            index--;
        }
        if (index < body.size()) {
            return body.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    @Override
    public int getStatementCount() {
        return body.size();
    }

    @Override
    public Statement getStatementAt(int index) {
        return body.get(index);
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnPatternCase(this);
    }
}
