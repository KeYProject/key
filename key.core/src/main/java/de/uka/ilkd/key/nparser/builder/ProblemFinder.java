/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser.builder;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.nparser.KeYParser;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.settings.Configuration;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

import java.io.IOException;
import java.io.StringReader;
import java.util.Properties;

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

    @Override
    public @Nullable Object visitFile(KeYParser.FileContext ctx) {
        each(ctx.problem());
        return null;
    }

    @Override
    public @Nullable KeYJavaType visitArrayopid(KeYParser.ArrayopidContext ctx) {
        return accept(ctx.keyjavatype());
    }

    @Override
    public @Nullable Term visitProblem(KeYParser.ProblemContext ctx) {
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
            if (ctx.oldProofObligation != null) {
                try {
                    Properties p = new Properties();
                    p.load(new StringReader((String) ctx.oldProofObligation.accept(this)));
                    proofObligation = new Configuration();
                    p.forEach((k, v) -> proofObligation.set(k.toString(), v.toString()));
                } catch (IOException e) {
                    throw new RuntimeException("Could not load the proof obligation given as a property file @ "
                            + BuilderHelpers.getPosition(ctx.oldProofObligation), e);
                }
            } else if (ctx.proofObligation != null) {
                proofObligation =
                        ParsingFacade.getConfiguration((KeYParser.TableContext) ctx.proofObligation);
            } else {
                proofObligation = null;
            }
        }
        if (ctx.PROBLEM() != null) {
            problem = accept(ctx.termorseq());
        }
        return null;
    }

    @Override
    public @Nullable Sequent visitTermorseq(KeYParser.TermorseqContext ctx) {
        var obj = super.visitTermorseq(ctx);
        if (obj instanceof Sequent s)
            return s;
        if (obj instanceof Term t)
            return Sequent.createSuccSequent(new Semisequent(new SequentFormula(t)));
        return null;
    }

    @Nullable
    public String getChooseContract() {
        return chooseContract;
    }

    @Nullable
    public Configuration getProofObligation() {
        return proofObligation;
    }

    @Nullable
    public Sequent getProblem() {
        return problem;
    }

}
