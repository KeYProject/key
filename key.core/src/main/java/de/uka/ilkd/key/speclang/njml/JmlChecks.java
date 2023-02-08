package de.uka.ilkd.key.speclang.njml;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.speclang.PositionedString;
import org.antlr.v4.runtime.ParserRuleContext;

import javax.annotation.Nonnull;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

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
    public static List<JmlCheck> getJmlChecks() {
        // secure internal copy
        return new ArrayList<>(jmlChecks);
    }
}


class AbstractCheck extends JmlParserBaseVisitor<Void> implements JmlCheck {
    private final List<PositionedString> warnings = new LinkedList<>();

    @Override
    public @Nonnull List<PositionedString> check(@Nonnull ParserRuleContext ctx) {
        warnings.clear();
        ctx.accept(this);
        return warnings;
    }

    protected void addWarning(ParserRuleContext ctx, String text) {
        PositionedString ps = new PositionedString(text, ctx.start.getTokenSource().getSourceName(),
            new Position(ctx.start.getLine(), ctx.start.getCharPositionInLine()));
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
    public Void visitSpec_body(JmlParser.Spec_bodyContext ctx) {
        checkRequires(ctx.a);
        checkRequires(ctx.inner);
        return null;
    }

    private void checkRequires(List<JmlParser.ClauseContext> clauses) {
        boolean otherClause = false;
        for (JmlParser.ClauseContext clause : clauses) {
            if (!isRequiresClause(clause)) {
                otherClause = true;
            }

            if (isRequiresClause(clause) && otherClause) {
                addWarning(clause,
                    "Diverging Semantics form JML Reference: Requires does not initiate a new contract. "
                        + "See https://www.key-project.org/docs/user/JMLGrammar/#TODO");
            }
        }
    }


    private boolean isRequiresClause(JmlParser.ClauseContext clause) {
        return clause.requires_clause() != null;
    }
}
