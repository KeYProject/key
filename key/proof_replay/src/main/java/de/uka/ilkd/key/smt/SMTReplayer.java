package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.smt.SMTProofParser.*;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;

public class SMTReplayer {
    private final String smtOutput;
    private final Goal goal;
    private final Proof proof;
    private final Services services;
    private final TermBuilder tb;

    private final Map<Symbol, ProofsexprContext> symbolTable = new LinkedHashMap<>();
    private final Map<String, Sort> sorts = new HashMap<>();

    public SMTReplayer(SMTProblem problem) {
        if (problem.getSolvers().size() != 1) {
            throw new IllegalStateException("Proof can only be replayed from single solver!");
        }
        SMTSolver solver = problem.getSolvers().iterator().next();
        smtOutput = solver.getSolverOutput();
        goal = problem.getGoal();
        proof = problem.getGoal().proof();
        services = proof.getServices();
        tb = services.getTermBuilder();
    }

    public void replay() {
        SmtoutputContext smtoutputContext = SMTProofParsing.parse(smtOutput);
        ReplayVisitor visitor = new ReplayVisitor();
        smtoutputContext.accept(visitor);
        System.out.println();
    }

    private class ReplayVisitor extends SMTProofBaseVisitor<Void> {
        @Override
        public Void visitSmtoutput(SmtoutputContext ctx) {
            // does nothing currently
            return super.visitSmtoutput(ctx);
            //return null;
        }

        @Override
        public Void visitProof(ProofContext ctx) {
            // does nothing currently
            return super.visitProof(ctx);
        }

        @Override
        public Void visitProofsexpr(ProofsexprContext ctx) {
            /*
            String rulename = ctx.rulename.getText();
            if (rulename.equals("")) {

            } else if (rulename.equals("let")) {

            } else if (rulename.equals("lambda")) {

            } else {

            }*/
            return super.visitProofsexpr(ctx);
        }

        @Override
        public Void visitFunction_def(Function_defContext ctx) {
            return super.visitFunction_def(ctx);
        }

        @Override
        public Void visitCommand(CommandContext ctx) {
            /*
            String cmdName = ctx.cmdName.getText();
            switch (cmdName) {
                case "assert":
                    List<? extends Term> children = new ArrayList<>();
                    //children.add(visitTerm(ctx.term()));
                    return new Command(new Operator("assert", 1), children);
                case "check-sat": break;
                case "declare-const": break;
                case "declare-fun": break;
                case "define-fun": break;
                case "exit": break;
                case "get-proof": break;
                case "set-logic": break;
                default: break;
            }
            */
            return super.visitCommand(ctx);
        }

        @Override
        public Void visitSpec_constant(Spec_constantContext ctx) {
            return super.visitSpec_constant(ctx);
        }

        @Override
        public Void visitS_expr(S_exprContext ctx) {
            return super.visitS_expr(ctx);
        }

        @Override
        public Void visitIdentifier(IdentifierContext ctx) {
            return super.visitIdentifier(ctx);
        }

        @Override
        public Void visitSort(SortContext ctx) {
            return super.visitSort(ctx);
        }

        @Override
        public Void visitAttribute_value(Attribute_valueContext ctx) {
            return super.visitAttribute_value(ctx);
        }

        @Override
        public Void visitAttribute(AttributeContext ctx) {
            return super.visitAttribute(ctx);
        }

        @Override
        public Void visitQual_identifier(Qual_identifierContext ctx) {
            String id = ctx.identifier().getText();
            de.uka.ilkd.key.logic.Term term;
            if (id.equals("false")) {
                term = tb.ff();
            }
            return super.visitQual_identifier(ctx);
        }

        @Override
        public Void visitVar_binding(Var_bindingContext ctx) {

            Symbol s = new Symbol(ctx.SYMBOL().getSymbol().getText());
            //Term def = visitProofsexpr(ctx.proofsexpr());
            ProofsexprContext def = ctx.proofsexpr();


            symbolTable.put(s, def);
            return super.visitVar_binding(ctx);
        }

        @Override
        public Void visitSorted_var(Sorted_varContext ctx) {
            String sortName = ctx.sort().getText();
            // cut ModularSMTLib2Translator.SORT_PREFIX from sortName
            // lookup sort by name in services

            return super.visitSorted_var(ctx);
        }

        @Override
        public Void visitPattern(PatternContext ctx) {
            return super.visitPattern(ctx);
        }

        @Override
        public Void visitMatch_case(Match_caseContext ctx) {
            return super.visitMatch_case(ctx);
        }

        @Override
        public Void visitTerm(TermContext ctx) {
            return super.visitTerm(ctx);
        }
    }
}
