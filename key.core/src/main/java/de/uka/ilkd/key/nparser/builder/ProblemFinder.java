/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser.builder;

import javax.annotation.Nullable;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.nparser.KeYParser;
import de.uka.ilkd.key.nparser.ParsingFacade;

/**
 * This visitor finds the problem information (problemTerm, choosedContract, and proofObligation) of
 * a {@link de.uka.ilkd.key.nparser.KeyAst.File}.
 *
 * @author weigl
 */
public class ProblemFinder extends ExpressionBuilder {
    private @Nullable Term problemTerm;
    private @Nullable String chooseContract;
    private @Nullable String proofObligation;

    public ProblemFinder(Services services, NamespaceSet nss) {
        super(services, nss);
    }

    @Override
    public Object visitFile(KeYParser.FileContext ctx) {
        each(ctx.problem());
        return null;
    }

    @Override
    public KeYJavaType visitArrayopid(KeYParser.ArrayopidContext ctx) {
        return accept(ctx.keyjavatype());
    }

    @Override
    public Term visitProblem(KeYParser.ProblemContext ctx) {
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
            if (ctx.proofObligation != null) {
                proofObligation = ParsingFacade.getValueDocumentation(ctx.proofObligation);
            }
            // .replace("\\\\:", ":");
            else {
                proofObligation = "";
            }
        }
        if (ctx.PROBLEM() != null) {
            problemTerm = accept(ctx.term());
        }
        return null;
    }

    @Nullable
    public String getChooseContract() {
        return chooseContract;
    }

    @Nullable
    public String getProofObligation() {
        return proofObligation;
    }

    @Nullable
    public Term getProblemTerm() {
        return problemTerm;
    }
}
