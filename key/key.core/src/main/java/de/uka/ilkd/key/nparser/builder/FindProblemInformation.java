package de.uka.ilkd.key.nparser.builder;

import de.uka.ilkd.key.nparser.KeYParser;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.nparser.ProblemInformation;
import javax.annotation.Nonnull;

import java.util.List;
import java.util.Objects;

import static de.uka.ilkd.key.nparser.builder.BuilderHelpers.trim;

/**
 * The visitor for extracting the {@link ProblemInformation}.
 *
 * @author weigl
 * @see #getProblemInformation()
 */
public class FindProblemInformation extends AbstractBuilder<Object> {
    private final @Nonnull ProblemInformation information = new ProblemInformation();

    @Override
    public Object visitFile(KeYParser.FileContext ctx) {
        each(ctx.decls(), ctx.problem());
        return null;
    }

    @Override
    public Object visitDecls(KeYParser.DeclsContext ctx) {
        information.setProfile(acceptFirst(ctx.profile()));
        information.setPreferences(acceptFirst(ctx.preferences()));
        information.setBootClassPath(acceptFirst(ctx.bootClassPath()));
        ctx.classPaths().forEach(it ->
                information.getClasspath().addAll(Objects.requireNonNull(accept(it))));
        information.setJavaSource(acceptFirst(ctx.javaSource()));
        return null;
    }

    @Override
    public Object visitProblem(KeYParser.ProblemContext ctx) {
        if (ctx.CHOOSECONTRACT() != null) {
            if (ctx.chooseContract != null)
                information.setChooseContract(accept(ctx.chooseContract));
            else
                information.setChooseContract("");
        }
        if (ctx.PROOFOBLIGATION() != null) {
            if (ctx.proofObligation != null)
                information.setProofObligation(accept(ctx.proofObligation));
            else
                information.setProofObligation("");
        }
        information.setHasProblemTerm(ctx.PROBLEM() != null);
        return null;
    }


    @Override
    public String visitBootClassPath(KeYParser.BootClassPathContext ctx) {
        return accept(ctx.string_value());
    }

    @Override
    public List<String> visitClassPaths(KeYParser.ClassPathsContext ctx) {
        return mapOf(ctx.string_value());
    }

    @Override
    public String visitString_value(KeYParser.String_valueContext ctx) {
        return ParsingFacade.getValue(ctx);
    }


    @Override
    public String visitJavaSource(KeYParser.JavaSourceContext ctx) {
        return ctx.oneJavaSource() != null ? (String) accept(ctx.oneJavaSource()) : null;
    }

    @Override
    public String visitOneJavaSource(KeYParser.OneJavaSourceContext ctx) {
        return trim(ctx.getText(), '"');
    }

    @Override
    public Object visitProfile(KeYParser.ProfileContext ctx) {
        return accept(ctx.name);
    }

    @Override
    public String visitPreferences(KeYParser.PreferencesContext ctx) {
        return ctx.s != null ? (String) accept(ctx.s) : null;
    }

    /**
     * The found problem information.
     */
    public @Nonnull ProblemInformation getProblemInformation() {
        return information;
    }
}
