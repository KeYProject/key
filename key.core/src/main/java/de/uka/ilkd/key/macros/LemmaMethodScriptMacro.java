package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.SourceElement;
import de.uka.ilkd.key.java.ast.statement.JmlAssert;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.impl.DefaultTaskStartedInfo;
import de.uka.ilkd.key.rule.JmlAssertBuiltInRuleApp;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.scripts.ProofScriptEngine;
import de.uka.ilkd.key.scripts.ScriptCommandAst;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLLemmaDecl;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLMethodDecl;
import de.uka.ilkd.key.speclang.njml.JmlIO;
import de.uka.ilkd.key.speclang.njml.JmlParser;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.tree.ParseTree;
import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Modality;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.engine.ProverTaskListener;
import org.key_project.prover.engine.TaskStartedInfo;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.Pair;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

public class LemmaMethodScriptMacro extends AbstractProofMacro {

    private static final Logger LOGGER = LoggerFactory.getLogger(LemmaMethodScriptMacro.class);

    public static final String ID = "[A-Za-z_$0-9.]+";
    public static final Pattern NAME_PATTERN =
            Pattern.compile(ID + "\\[(" + ID + "::" + ID + ")\\(.*\\)\\].JML model_behavior operation contract.\\d+");

    public LemmaMethodScriptMacro() {
    }

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

    public boolean canApplyTo(Proof proof, ImmutableList<Goal> goals, PosInOccurrence posInOcc) {
        return ModelMethodScriptMacro.canApplyTo(proof, goals, posInOcc, true);
    }

    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic, Proof proof, ImmutableList<Goal> goals, PosInOccurrence posInOcc, ProverTaskListener listener) throws Exception {
        ProgramMethod pm = ModelMethodScriptMacro.extractModelMethod(proof);
        assert pm != null : "If canApplyTo gives true, this cannot happen";

        Goal goal = goals.head();

        // Currently treat lemmas the same way: if an attached JML assert script is present
        // at the current goal, execute it using the shared support.
        TextualJMLLemmaDecl methodDecl =
                (TextualJMLLemmaDecl) pm.getMethodDeclaration().getAttachedJml().stream().filter(TextualJMLLemmaDecl.class::isInstance).findAny().get();
        JmlParser.Lemma_declarationContext ctx =
                (JmlParser.Lemma_declarationContext) methodDecl.getMethodDefinition();

        JmlIO io = JmlProofScriptSupport.prepareJmlIO(proof.getServices(), pm);
        KeyAst.JMLProofScript proofScript = new KeyAst.JMLProofScript(ctx.assertionProof());
        Map<ParserRuleContext, JTerm> termMap = JmlProofScriptSupport.createTermMap(null, proofScript, List.of(), pm, io, proof.getServices());

        // We heavily rely on that variables have been computed before, otherwise this will
        // raise an NPE.
        Map<LocationVariable, JFunction> obtainMap =
                JmlProofScriptSupport.makeObtainVarMap(proofScript.getObtainedProgramVars(null));
        OpReplacer updateReplacer = JmlProofScriptSupport.getUpdateReplacer(goal);
        List<ScriptCommandAst> renderedProof =
                JmlProofScriptSupport.renderProof(proofScript, termMap, updateReplacer, proof.getServices());
        ProofScriptEngine pse = JmlProofScriptSupport.prepareEngine(proof, goal, obtainMap);
        LOGGER.debug("---- Script");
        LOGGER.debug(renderedProof.stream()
                .map(ScriptCommandAst::asCommandLine)
                .collect(Collectors.joining("\n")));
        LOGGER.debug("---- End Script");

        pse.execute((AbstractUserInterfaceControl) uic, renderedProof);

        return new ProofMacroFinishedInfo(this, proof);

    }
}