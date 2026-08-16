package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLMethodDecl;
import de.uka.ilkd.key.speclang.njml.JmlParser;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.tree.ParseTree;
import org.key_project.logic.op.Function;
import org.key_project.prover.engine.ProverTaskListener;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class LemmaAndModelMethodScriptMacro  extends AbstractProofMacro {

    private static final String ID = "[A-Za-z_$0-9.]+";
    private static final Pattern NAME_PATTERN =
            Pattern.compile(ID+ "\\[(" + ID + "::" + ID + ")\\(.*\\)\\].JML model_behavior operation contract.\\d+");

    public LemmaAndModelMethodScriptMacro() { }

    @Override
    public String getName() {
        return "lemma-script-auto-macro";
    }

    @Override
    public String getCategory() {
        return null;
    }

    @Override
    public String getDescription() {
        return "Apply scripts in lemmas and model methods";
    }

    @Override
    public boolean canApplyTo(Proof proof, ImmutableList<Goal> goals, PosInOccurrence posInOcc) {
        // only applicable on the root of the proof
        // todo change this to allow for subproofs of lemmas and model methods
        if(!goals.stream().allMatch(g -> g.node() == proof.root()))
            return false;

        String name = proof.name().toString();
        Matcher m = NAME_PATTERN.matcher(name);
        return m.matches();
    }

    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic, Proof proof, ImmutableList<Goal> goals, PosInOccurrence posInOcc, ProverTaskListener listener) throws Exception {
        String name = proof.name().toString();
        Matcher m = NAME_PATTERN.matcher(name);
        if (!m.matches())
            throw new RuntimeException("This macro was not applicable");

        Services services = proof.getServices();
        String lemmaName = m.group(1);
        Function function = services.getNamespaces().functions().lookup(lemmaName);
        if(function instanceof ProgramMethod pm && pm.isModel()) {
            if(pm.isLemma()) {
                return applyToLemma(uic, goals.head(), pm);
            } else {
                return applyToModel(uic, goals.head(), pm);
            }
        } else {
            return new ProofMacroFinishedInfo(this, goals);
        }
    }

    private ProofMacroFinishedInfo applyToLemma(UserInterfaceControl uic, Goal root, ProgramMethod pm) {
        return new ProofMacroFinishedInfo(this, ImmutableList.of(root));
    }

    private ProofMacroFinishedInfo applyToModel(UserInterfaceControl uic, Goal root, ProgramMethod pm) {
        TextualJMLMethodDecl methodDecl = (TextualJMLMethodDecl) pm.getMethodDeclaration().getAttachedJml().stream().
                filter(TextualJMLMethodDecl.class::isInstance).findAny().get();
        JmlParser.Method_declarationContext ctx =
                (JmlParser.Method_declarationContext) methodDecl.getMethodDefinition();

        CutTree cutTree = extractCutTree(ctx.method_body);

        // replicate cutTree and apply proofs on the leaves.

        return new ProofMacroFinishedInfo(this, ImmutableList.of(root));
    }

    private CutTree extractCutTree(ParserRuleContext ctx) {
        JmlParser.Mbody_statementContext stmCtx;
        List<ParseTree> localHistory;

        switch(ctx) {
            case JmlParser.Mbody_blockContext block -> {
                localHistory = block.children.stream().
                        filter(x -> x instanceof JmlParser.Mbody_varContext
                                || x instanceof JmlParser.Assert_statementContext).
                        toList();
                stmCtx = block.mbody_statement();
            }
            case JmlParser.Mbody_statementContext stm -> {
                localHistory = List.of();
                stmCtx = stm;
            }
            default -> throw new IllegalStateException("Unexpected value: " + ctx);
        }

        if(stmCtx instanceof JmlParser.Mbody_ifContext ifCtx) {
            var cond = ifCtx.getChild(ParserRuleContext.class, 0);
            var thenBr = ifCtx.getChild(ParserRuleContext.class, 1);
            var elseBr = ifCtx.getChild(ParserRuleContext.class, 2);

            CutTree thenTree = extractCutTree(thenBr);
            CutTree elseTree = extractCutTree(elseBr);

            if (thenTree.hasAssertions() || elseTree.hasAssertions()) {
                return new CutTree(localHistory, cond, thenTree, elseTree);
            }
        }
        return new CutTree(localHistory);
    }

    record CutTree(List<ParseTree> localHistory, ParserRuleContext cond, CutTree thenTree, CutTree elseTree) {

        public CutTree(List<ParseTree> localHistory) {
            this(localHistory, null, null, null);
        }

        public boolean hasAssertions() {
            return thenTree != null && thenTree.hasAssertions() || elseTree != null && elseTree.hasAssertions() ||
                    localHistory.stream().anyMatch(x -> x instanceof JmlParser.Assert_statementContext);
        }
    }
}
