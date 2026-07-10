/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser.builder;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.nparser.JavaKeYParser;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.nparser.ProblemInformation;

import org.key_project.util.java.StringUtil;
import org.key_project.util.parsing.Location;

import org.jspecify.annotations.NonNull;

/**
 * The visitor for extracting the {@link ProblemInformation}.
 *
 * @author weigl
 * @see #getProblemInformation()
 */
public class FindProblemInformation extends AbstractBuilder<Object> {
    private final @NonNull ProblemInformation information = new ProblemInformation();

    @Override
    public Object visitFile(JavaKeYParser.FileContext ctx) {
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
    public Object visitDecls(JavaKeYParser.DeclsContext ctx) {
        information.setBootClassPath(acceptFirst(ctx.bootClassPath()));
        ctx.classPaths().forEach(
            it -> information.getClasspath().addAll(Objects.requireNonNull(accept(it))));
        information.setJavaSource(acceptFirst(ctx.programSource()));
        return null;
    }

    @Override
    public Object visitProblem(JavaKeYParser.ProblemContext ctx) {
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
    public String visitBootClassPath(JavaKeYParser.BootClassPathContext ctx) {
        String value = accept(ctx.string_value());
        if (value != null) {
            information.putPathLocation(value, Location.fromToken(ctx.string_value().getStart()));
        }
        return value;
    }

    @Override
    public List<String> visitClassPaths(JavaKeYParser.ClassPathsContext ctx) {
        List<String> result = new ArrayList<>(ctx.string_value().size());
        for (var sv : ctx.string_value()) {
            String value = accept(sv);
            result.add(value);
            if (value != null) {
                information.putPathLocation(value, Location.fromToken(sv.getStart()));
            }
        }
        return result;
    }

    @Override
    public String visitString_value(JavaKeYParser.String_valueContext ctx) {
        return ParsingFacade.getValueDocumentation(ctx);
    }

    @Override
    public String visitProgramSource(JavaKeYParser.ProgramSourceContext ctx) {
        return ctx.oneProgramSource() != null ? (String) accept(ctx.oneProgramSource()) : null;
    }

    @Override
    public String visitOneProgramSource(JavaKeYParser.OneProgramSourceContext ctx) {
        return StringUtil.trim(ctx.getText(), '"');
    }

    @Override
    public Object visitProfile(JavaKeYParser.ProfileContext ctx) {
        return accept(ctx.name);
    }

    @Override
    public String visitPreferences(JavaKeYParser.PreferencesContext ctx) {
        return ctx.s != null ? (String) accept(ctx.s) : null;
    }

    /**
     * The found problem information.
     */
    public @NonNull ProblemInformation getProblemInformation() {
        return information;
    }
}
