/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
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
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * The visitor for extracting the {@link ProblemInformation}.
 *
 * @author weigl
 * @see #getProblemInformation()
 */
@NullMarked
public class FindProblemInformation extends AbstractBuilder<Object> {
    private final @NonNull ProblemInformation information = new ProblemInformation();

    /**
     * The overridden declaration requires a non-null return type, but this implementation may
     * legitimately return {@code null}; the difference is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:override.return.invalid")
    @Override
    public @Nullable Object visitFile(JavaKeYParser.FileContext ctx) {
        if (ctx.profile() != null) {
            information.setProfile(accept(ctx.profile()));
        }
        if (ctx.preferences() != null) {
            information.setPreferences(accept(ctx.preferences()));
        }
        each(ctx.decls(), ctx.problem());
        return null;
    }

    /**
     * The overridden declaration requires a non-null return type, but this implementation may
     * legitimately return {@code null}; the difference is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:override.return.invalid")
    @Override
    public @Nullable Object visitDecls(JavaKeYParser.DeclsContext ctx) {
        information.setBootClassPath(acceptFirst(ctx.bootClassPath()));
        ctx.classPaths().forEach(
            it -> information.getClasspath().addAll(Objects.requireNonNull(accept(it))));
        information.setJavaSource(acceptFirst(ctx.programSource()));
        return null;
    }

    /**
     * The overridden declaration requires a non-null return type, but this implementation may
     * legitimately return {@code null}; the difference is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:override.return.invalid")
    @Override
    public @Nullable Object visitProblem(JavaKeYParser.ProblemContext ctx) {
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


    /**
     * The overridden declaration requires a non-null return type, but this implementation may
     * legitimately return {@code null}; the difference is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:override.return.invalid")
    @Override
    public @Nullable String visitBootClassPath(JavaKeYParser.BootClassPathContext ctx) {
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
            if (value != null) {
                result.add(value);
                information.putPathLocation(value, Location.fromToken(sv.getStart()));
            }
        }
        return result;
    }

    @Override
    public String visitString_value(JavaKeYParser.String_valueContext ctx) {
        return ParsingFacade.getValueDocumentation(ctx);
    }

    /**
     * The overridden declaration requires a non-null return type, but this implementation may
     * legitimately return {@code null}; the difference is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:override.return.invalid")
    @Override
    public @Nullable String visitProgramSource(JavaKeYParser.ProgramSourceContext ctx) {
        return ctx.oneProgramSource() != null ? (String) accept(ctx.oneProgramSource()) : null;
    }

    @Override
    public String visitOneProgramSource(JavaKeYParser.OneProgramSourceContext ctx) {
        return StringUtil.trim(ctx.getText(), '"');
    }

    /**
     * The overridden declaration requires a non-null return type, but this implementation may
     * legitimately return {@code null}; the difference is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:override.return.invalid")
    @Override
    public @Nullable Object visitProfile(JavaKeYParser.ProfileContext ctx) {
        return accept(ctx.name);
    }

    /**
     * The overridden declaration requires a non-null return type, but this implementation may
     * legitimately return {@code null}; the difference is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:override.return.invalid")
    @Override
    public @Nullable String visitPreferences(JavaKeYParser.PreferencesContext ctx) {
        return ctx.s != null ? (String) accept(ctx.s) : null;
    }

    /**
     * The found problem information.
     */
    public @NonNull ProblemInformation getProblemInformation() {
        return information;
    }
}
