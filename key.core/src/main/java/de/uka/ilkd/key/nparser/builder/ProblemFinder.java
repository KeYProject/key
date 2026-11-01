/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.nparser.builder;

import java.io.IOException;
import java.io.StringReader;
import java.util.Properties;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.nparser.JavaKeYParser;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.util.parsing.BuildingException;

import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * This visitor finds the problem information (problemTerm, choosedContract, and proofObligation) of
 * a {@link de.uka.ilkd.key.nparser.KeyAst.File}.
 *
 * @author weigl
 */
@NullMarked
public class ProblemFinder extends ExpressionBuilder {
    private @Nullable Sequent problem;
    private @Nullable String chooseContract;
    private @Nullable Configuration proofObligation;

    public ProblemFinder(Services services, NamespaceSet nss) {
        super(services, nss);
    }

    /**
     * The overridden declaration requires a non-null return type, but this implementation may
     * legitimately return {@code null}; the difference is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:override.return.invalid")
    @Override
    public @Nullable Object visitFile(JavaKeYParser.FileContext ctx) {
        each(ctx.problem());
        return null;
    }

    /**
     * The overridden declaration requires a non-null return type, but this implementation may
     * legitimately return {@code null}; the difference is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:override.return.invalid")
    @Override
    public @Nullable KeYJavaType visitArrayopid(JavaKeYParser.ArrayopidContext ctx) {
        return accept(ctx.typemapping());
    }

    /**
     * Try to find a problem defined in the {@link de.uka.ilkd.key.proof.init.KeYUserProblemFile}
     * located in the
     * given AST.
     * <p>
     * After this method is called, you can retrieve the chosen contract via
     * {@link #getChooseContract()} or the
     * proof obligation information via {@link #getProofObligation()}.
     *
     * @param ctx
     *        the parse tree
     * @return a term if {@code \problem} entry exists.
     * @throws BuildingException
     *         if the proof-obligation property file cannot be loaded.
     *         <p>
     *         The overridden declaration requires a non-null return type, but this implementation
     *         may legitimately return {@code null}; the checker additionally infers a
     *         {@code @KeyForBottom} annotation on the {@code Properties.forEach} lambda
     *         parameters, which is not a legal location for that annotation. Both differences are
     *         suppressed with scoped keys.
     */
    @SuppressWarnings({ "nullness:override.return.invalid",
        "nullness:type.invalid.annotations.on.location" })
    @Override
    public @Nullable JTerm visitProblem(JavaKeYParser.ProblemContext ctx) {
        if (ctx.CHOOSECONTRACT() != null) {
            if (ctx.chooseContract != null) {
                chooseContract = ParsingFacade.getValueDocumentation(ctx.chooseContract);
            }
            // .replace("\\\\:", ":");
            else {
                chooseContract = "";
            }
        }
        if (ctx.PROOFOBLIGATION() != null) {
            var obl = ctx.proofObligation;
            if (obl instanceof JavaKeYParser.CstringContext stringContext) {
                try {
                    Properties p = new Properties();
                    var value = stringContext.STRING_LITERAL().getText();
                    value = value.substring(1, value.length() - 1).replace("\\\\", "\\");
                    p.load(new StringReader(value));
                    Configuration po = proofObligation = new Configuration();
                    p.forEach((k, v) -> po.set(k.toString(), v.toString()));
                } catch (IOException e) {
                    throw new BuildingException(ctx,
                        "Could not load the proof obligation given " +
                            "as a property file due to an error in the properties format",
                        e);
                }
            } else if (obl instanceof JavaKeYParser.TableContext tbl) {
                proofObligation = ParsingFacade.getConfiguration(tbl);
            } else {
                throw new BuildingException(ctx,
                    "Found a proof obligation entry, but the value is not a string or a JSON object");
            }
        }
        if (ctx.PROBLEM() != null) {
            problem = accept(ctx.termorseq());
        }
        return null;
    }

    /**
     * The overridden declaration requires a non-null return type, but this implementation may
     * legitimately return {@code null}; the difference is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:override.return.invalid")
    @Override
    public @Nullable Sequent visitTermorseq(JavaKeYParser.TermorseqContext ctx) {
        var obj = super.visitTermorseq(ctx);
        if (obj instanceof Sequent s)
            return s;
        if (obj instanceof JTerm t)
            return JavaDLSequentKit
                    .createSuccSequent(ImmutableList.singleton(new SequentFormula(t)));
        return null;
    }

    public @Nullable String getChooseContract() {
        return chooseContract;
    }

    public @Nullable Configuration getProofObligation() {
        return proofObligation;
    }

    public @Nullable Sequent getProblem() {
        return problem;
    }
}
