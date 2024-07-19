/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.nparser.KeYParser;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.nparser.builder.ExpressionBuilder;
import de.uka.ilkd.key.util.parsing.BuildingIssue;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.ParserRuleContext;
import org.jspecify.annotations.NullMarked;
import org.key_project.logic.Name;
import org.key_project.logic.PosInTerm;
import org.key_project.logic.sort.AbstractSort;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.rules.instantiation.AssumesFormulaInstantiation;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.List;

@NullMarked
public class SequentWithHoles {


    private final List<TermWithHoles> antecedent;
    private final List<TermWithHoles> succedent;

    private SequentWithHoles(List<TermWithHoles> antecedent, List<TermWithHoles> succedent) {
        this.antecedent = antecedent;
        this.succedent = succedent;
    }

    private static final Logger LOGGER = LoggerFactory.getLogger(SequentWithHoles.class);

    public static SequentWithHoles fromString(EngineState engineState, String str) {
        KeyAst.Seq seq = ParsingFacade.parseSequent(CharStreams.fromString(str));
        return fromParserContext(engineState, seq.ctx);
    }

    public static SequentWithHoles fromParserContext(EngineState state, ParserRuleContext ctx) {

        if(ctx instanceof KeYParser.ProofScriptExpressionContext psctx) {
            ctx = psctx.seq();
        }

        if(ctx instanceof KeYParser.SeqContext seqCtx) {
            List<TermWithHoles> antecedent = new java.util.ArrayList<>();
            KeYParser.SemisequentContext semseq = seqCtx.ant;
            while(semseq != null && semseq.term() != null) {
                antecedent.add(TermWithHoles.fromParserContext(state, semseq.term()));
                semseq = semseq.semisequent();
            }

            List<TermWithHoles> succedent = new java.util.ArrayList<>();
            semseq = seqCtx.suc;
            while(semseq != null && semseq.term() != null) {
                succedent.add(TermWithHoles.fromParserContext(state, semseq.term()));
                semseq = semseq.semisequent();
            }
            return new SequentWithHoles(antecedent, succedent);
        }

        throw new IllegalArgumentException("Not a sequent: " + ctx.getText());
    }

    // TODO currently this does not check if the instantiation is on the correct side ...
    public boolean matches(ImmutableList<AssumesFormulaInstantiation> ifFormulaInstantiations) {

        for (AssumesFormulaInstantiation assF : ifFormulaInstantiations) {
            var form = assF.getSequentFormula();
            if (antecedent.stream().noneMatch(f -> f.matchesToplevel(form)) &&
                    succedent.stream().noneMatch(f -> f.matchesToplevel(form))) {
                return false;
            }
        }

        return true;
    }
}