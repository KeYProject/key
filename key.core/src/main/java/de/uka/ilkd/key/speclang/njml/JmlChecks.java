/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.njml;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.speclang.PositionedString;

import org.antlr.v4.runtime.ParserRuleContext;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * Facade for implementing syntactical JML syntax checks.
 * <p>
 * This facades holds a list of all known jmlChecks. Add yours to {@code jmlChecks} to used in
 * {@link JmlIO}.
 *
 * @author Alexander Weigl
 * @version 1 (6/8/21)
 * @see JmlIO
 */
public final class JmlChecks {
    private static final List<JmlCheck> jmlChecks = new ArrayList<>();

    private JmlChecks() {}

    static {
        jmlChecks.add(new JmlWarnDifferentRequiresSemantics());
    }

    /**
     * Returns a list of currently registered JML checks.
     */
    public static @NonNull List<JmlCheck> getJmlChecks() {
        // secure internal copy
        return new ArrayList<>(jmlChecks);
    }
}


class AbstractCheck extends JmlParserBaseVisitor<Void> implements JmlCheck {
    private final List<PositionedString> warnings = new LinkedList<>();

    @Override
    public @NonNull List<PositionedString> check(@NonNull ParserRuleContext ctx) {
        warnings.clear();
        ctx.accept(this);
        return warnings;
    }

    protected void addWarning(@NonNull ParserRuleContext ctx, @NonNull String text) {
        PositionedString ps = new PositionedString(text, Location.fromToken(ctx.start));
        warnings.add(ps);
    }
}


/**
 * This check tests warns if a {@code requires} clause follows a non-{@code requires} clause. Such a
 * constellation has different semantics in KeY than in the JML ref manual. KeY does not recognize
 * {@code requires} as contract initiators.
 */
class JmlWarnDifferentRequiresSemantics extends AbstractCheck implements JmlCheck {
    @Override
    public @Nullable Void visitSpec_body(JmlParser.@NonNull Spec_bodyContext ctx) {
        checkRequires(ctx.a);
        checkRequires(ctx.inner);
        return null;
    }

    private void checkRequires(@NonNull List<JmlParser.ClauseContext> clauses) {
        boolean otherClause = false;
        for (JmlParser.ClauseContext clause : clauses) {
            if (!isRequiresClause(clause)) {
                otherClause = true;
            }

            if (isRequiresClause(clause) && otherClause) {
                addWarning(clause,
                    "Diverging Semantics from JML Reference: Requires does not initiate a new contract. "
                        + "See https://keyproject.github.io/key-docs/user/JMLGrammar/#TODO");
            }
        }
    }


    private boolean isRequiresClause(JmlParser.@NonNull ClauseContext clause) {
        return clause.requires_clause() != null;
    }
}
