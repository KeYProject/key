/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser.builder;

import java.util.List;
import java.util.Objects;
import javax.annotation.Nonnull;

import de.uka.ilkd.key.nparser.KeYParser;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.nparser.ProblemInformation;

import org.key_project.util.java.StringUtil;

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
        if (ctx.profile() != null) {
            information.setProfile(accept(ctx.profile()));
        }
        if (ctx.preferences() != null) {
            information.setPreferences(accept(ctx.preferences()));
        }
        each(ctx.decls(), ctx.problem());
        return null;
    }

    @Override
    public Object visitDecls(KeYParser.DeclsContext ctx) {
        information.setBootClassPath(acceptFirst(ctx.bootClassPath()));
        ctx.classPaths().forEach(
            it -> information.getClasspath().addAll(Objects.requireNonNull(accept(it))));
        information.setJavaSource(acceptFirst(ctx.javaSource()));
        return null;
    }

    @Override
    public Object visitProblem(KeYParser.ProblemContext ctx) {
        if (ctx.CHOOSECONTRACT() != null) {
            if (ctx.chooseContract != null) {
                information.setChooseContract(accept(ctx.chooseContract));
            } else {
                information.setChooseContract("");
            }
        }
        if (ctx.PROOFOBLIGATION() != null) {
            if (ctx.proofObligation != null) {
                information.setProofObligation(accept(ctx.proofObligation));
            } else {
                information.setProofObligation("");
            }
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
        return ParsingFacade.getValueDocumentation(ctx);
    }


    @Override
    public String visitJavaSource(KeYParser.JavaSourceContext ctx) {
        return ctx.oneJavaSource() != null ? (String) accept(ctx.oneJavaSource()) : null;
    }

    @Override
    public String visitOneJavaSource(KeYParser.OneJavaSourceContext ctx) {
        return StringUtil.trim(ctx.getText(), '"');
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
