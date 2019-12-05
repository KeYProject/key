package de.uka.ilkd.key.nparser;

import com.google.common.base.CharMatcher;

import java.util.List;

public class FindProblemInformation extends AbstractBuilder<Object> {
    private ProblemInformation information = new ProblemInformation();

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
        information.setClasspath(acceptFirst(ctx.classPaths()));
        information.setJavaSource(acceptFirst(ctx.javaSource()));
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
    public String visitJavaSource(KeYParser.JavaSourceContext ctx) {
        return ctx.oneJavaSource() != null ? (String) accept(ctx.oneJavaSource()) : null;
    }

    @Override
    public String visitOneJavaSource(KeYParser.OneJavaSourceContext ctx) {
        return trim(ctx.getText(), '"');
    }

    private String trim(String text, char c) {
        return CharMatcher.is(c).trimFrom(text);
    }

    @Override
    public Object visitProfile(KeYParser.ProfileContext ctx) {
        return accept(ctx.name);
    }

    @Override
    public String visitPreferences(KeYParser.PreferencesContext ctx) {
        return ctx.s != null ? (String) accept(ctx.s) : null;
    }

    public ProblemInformation getProblemInformation() {
        return information;
    }
}
