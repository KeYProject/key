package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.util.Position;
import org.antlr.v4.runtime.RuleContext;
import org.antlr.v4.runtime.tree.ParseTree;
import org.jspecify.annotations.Nullable;

import java.util.Stack;

/**
 *
 * @author Alexander Weigl
 * @version 1 (20.08.26)
 */
public class AstBuilder extends JavaKeYParserBaseVisitor<AstNode> {
    /**
     * Helper function for avoiding cast.
     */
    public <U> @Nullable U accept(@Nullable RuleContext ctx) {
        if (ctx == null) {
            return null;
        }
        return (U) ctx.accept(this);
    }

    @Override
    protected T aggregateResult(T aggregate, T nextResult) {
        if (nextResult != null) {
            return nextResult;
        }
        return aggregate;
    }

    protected <U> @Nullable U accept(@Nullable RuleContext ctx, Object... args) {
        if (parameters == null) {
            parameters = new Stack<>();
        }
        int stackSize = parameters.size();
        push(args);
        U t = accept(ctx);
        // Stack hygiene
        while (parameters.size() > stackSize) {
            parameters.pop();
        }
        return t;
    }

    KeYFile file;

    @Override
    public AstNode visitFile(JavaKeYParser.FileContext ctx) {
        file = new KeYFile();
        file.setPosition(ctx);
        file.setProfile(accept(ctx.profile()));
        file.setPreferences(accept(ctx.preferences()));
        file.setDecls(map(ctx.decls()));
        file.setProblem(accept(ctx.profile()));
        return file;
    }

    @Override
    public AstNode visitProfile(JavaKeYParser.ProfileContext ctx) {
        return accept(ctx.name.STRING_LITERAL());
    }

    @Override
    public AstNode visitPreferences(JavaKeYParser.PreferencesContext ctx) {
        return super.visitPreferences(ctx);
    }

    @Override
    public AstNode visitDecls(JavaKeYParser.DeclsContext ctx) {

    }

    @Override
    public AstNode visitBootClassPath(JavaKeYParser.BootClassPathContext ctx) {
        file.setBootClassPath(accept(ctx.id));
        return null;
    }

    @Override
    public AstNode visitClassPaths(JavaKeYParser.ClassPathsContext ctx) {
        for (var value : ctx.string_value()) {
            file.addClassPath(accept(value));
        }
        return null;
    }

    @Override
    public AstNode visitOneProgramSource(JavaKeYParser.OneProgramSourceContext ctx) {
        for (var value : ctx.string_value()) {
            file.addProgramSource(accept(value));
        }
        return null;
    }

    @Override
    public AstNode visitProofScriptEntry(JavaKeYParser.ProofScriptEntryContext ctx) {
        return super.visitProofScriptEntry(ctx);
    }


    @Override
    public AstNode visitOne_include_statement(JavaKeYParser.One_include_statementContext ctx) {
        for (var value : ctx.one_include()) {
            file.addInclude(accept(value));
        }
        return null;
    }

    @Override
    public AstNode visitOptions_choice(JavaKeYParser.Options_choiceContext ctx) {
        return super.visitOptions_choice(ctx);
    }

    @Override
    public AstNode visitOption_decls(JavaKeYParser.Option_declsContext ctx) {
        return super.visitOption_decls(ctx);
    }


    @Override
    public AstNode visitSort_decls(JavaKeYParser.Sort_declsContext ctx) {
        return super.visitSort_decls(ctx);
    }


    @Override
    public AstNode visitProg_var_decls(JavaKeYParser.Prog_var_declsContext ctx) {
        return super.visitProg_var_decls(ctx);
    }

    private class AstNode {
        Position position;
        public void setPosition(ParseTree position) {
            this.position = Position.make(position);
        }

        public Position getPosition() {
            return position;
        }
    }
    private class KeYFile extends AstNode { }
    private class SimpleName extends AstNode {}
}
