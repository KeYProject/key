/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros;

import java.util.*;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.statement.JmlAssert;
import de.uka.ilkd.key.java.ast.statement.MethodFrame;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.scripts.ProofScriptEngine;
import de.uka.ilkd.key.scripts.ScriptCommandAst;
import de.uka.ilkd.key.scripts.ScriptException;
import de.uka.ilkd.key.scripts.TermWithHoles;
import de.uka.ilkd.key.speclang.njml.JmlIO;
import de.uka.ilkd.key.speclang.njml.JmlLexer;
import de.uka.ilkd.key.speclang.njml.JmlParser;
import de.uka.ilkd.key.speclang.njml.JmlParser.ProofArgContext;
import de.uka.ilkd.key.speclang.njml.JmlParser.ProofCmdCaseContext;
import de.uka.ilkd.key.speclang.njml.JmlParser.ProofCmdContext;
import de.uka.ilkd.key.speclang.njml.SpecMathMode;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Term;
import org.key_project.prover.rules.RuleApp;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.java.StringUtil;
import org.key_project.util.lookup.Property;
import org.key_project.util.parsing.Location;

import org.antlr.v4.runtime.ParserRuleContext;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * Utilities for rendering and executing JML proof scripts across different macros.
 * This class centralizes common functionality so macros like ApplyScriptsMacro and
 * LemmaAndModelMethodScriptMacro can share logic without duplication.
 */
public final class JmlProofScriptSupport {

    private JmlProofScriptSupport() {
        // utility
    }

    public static final Property<Map<LocationVariable, JFunction>> USER_DATA_JML_OBTAIN_VAR_MAP =
        new Property<>("jml.obtainVarMap");

    /**
     * Wrapper around a JTerm that defers resolution of obtain variables until use.
     */
    public record ObtainAwareTerm(JTerm term) {
        JTerm resolve(Map<LocationVariable, JFunction> obtainMap, Services services) {
            OpReplacer pvr = new OpReplacer(obtainMap, services.getTermFactory());
            JTerm result = pvr.replace(term);
            assertNoObtainVarsLeft(result, obtainMap);
            return result;
        }

        private void assertNoObtainVarsLeft(JTerm term,
                Map<LocationVariable, JFunction> obtainMap) {
            var v = new DefaultVisitor() {
                @Override
                public void visit(Term visited) {
                    if (obtainMap.containsKey(term.op())) {
                        throw new RuntimeException(
                            "Use of obtain variable before it being obtained: " + term.op());
                    }
                }
            };
            term.execPreOrder(v);
        }
    }

    /**
     * Create an obtain variable map with all provided variables initialized to null.
     */
    public static Map<LocationVariable, JFunction> makeObtainVarMap(
            ImmutableList<LocationVariable> locationVariables) {
        HashMap<LocationVariable, JFunction> result = new LinkedHashMap<>();
        for (LocationVariable lv : locationVariables) {
            result.put(lv, null);
        }
        return result;
    }

    /**
     * Creates an OpReplacer that applies the update found on the goal's applied rule app, if any.
     */
    public static OpReplacer getUpdateReplacer(Goal goal) {
        Node parent = goal.node().parent();
        if(parent == null) {
            // we can also operate on the root ...
            return null;
        }
        RuleApp ruleApp = parent.getAppliedRuleApp();
        org.key_project.logic.Term appliedOn = ruleApp.posInOccurrence().subTerm();
        if (appliedOn.op() instanceof UpdateApplication) {
            var update = UpdateApplication.getUpdate((JTerm) appliedOn);
            Map<JTerm, JTerm> updates = new LinkedHashMap<>();
            Services services = goal.proof().getServices();
            collectUpdates(update, updates, services);
            return new OpReplacer(updates, services.getTermFactory());
        }
        return null;
    }

    private static void collectUpdates(JTerm update, Map<JTerm, JTerm> updates, Services services) {
        switch (update.op()) {
            case ElementaryUpdate eu ->
                updates.put(services.getTermBuilder().var((ProgramVariable) eu.lhs()),
                    update.sub(0));

            case UpdateJunctor uj -> {
                collectUpdates(update.sub(0), updates, services);
                collectUpdates(update.sub(1), updates, services);
            }

            default ->
                throw new IllegalStateException(
                    "Unexpected update operation: " + update.op().getClass());
        }
    }

    /**
     * Render a JML proof script into a list of script command ASTs.
     */
    public static List<ScriptCommandAst> renderProof(KeyAst.JMLProofScript script,
            Map<ParserRuleContext, JTerm> termMap, @Nullable OpReplacer update, Services services)
            throws ScriptException {
        List<ScriptCommandAst> result = new ArrayList<>();
        // Push current settings onto the settings stack
        result.add(new ScriptCommandAst("set", Map.of("stack", "push"), List.of()));
        // Prepare by resolving the update
        result.add(new ScriptCommandAst("oss", Map.of("recentOnly", true), List.of()));
        for (ProofCmdContext proofCmdContext : script.ctx.proofCmd()) {
            result.addAll(renderProofCmd(proofCmdContext, termMap, update, services));
        }
        // Pop settings stack to restore old settings
        result.add(new ScriptCommandAst("set", Map.of("stack", "pop"), List.of()));
        return result;
    }

    private static List<ScriptCommandAst> renderProofCmd(ProofCmdContext ctx,
            Map<ParserRuleContext, JTerm> termMap,
            @Nullable OpReplacer update, Services services) throws ScriptException {
        List<ScriptCommandAst> result = new ArrayList<>();

        // Push the current branch context
        result.add(new ScriptCommandAst("branches", Map.of(), List.of("push")));

        // Compose the command itself
        if (ctx.obtain != null) {
            ScriptCommandAst command = renderObtainCommand(ctx, termMap, update, services);
            result.add(command);
        } else {
            ScriptCommandAst command = renderRegularCommand(ctx, termMap, update, services);
            result.add(command);
        }

        // handle followup proofCmd if present
        JmlParser.ProofCmdSuffixContext suffix = ctx.proofCmdSuffix();
        if (suffix != null) {
            if (!suffix.proofCmd().isEmpty()) {
                result.add(new ScriptCommandAst("branches", Map.of(), List.of("single")));
                for (ProofCmdContext proofCmdContext : suffix.proofCmd()) {
                    result.addAll(renderProofCmd(proofCmdContext, termMap, update, services));
                }
            }

            // handle proofCmdCases if present
            for (ProofCmdCaseContext pcase : suffix.proofCmdCase()) {
                String label = StringUtil.stripQuotes(pcase.label.getText());
                result.add(new ScriptCommandAst("branches", Map.of("branch", label),
                    List.of("select")));
                for (ProofCmdContext proofCmdContext : pcase.proofCmd()) {
                    result.addAll(renderProofCmd(proofCmdContext, termMap, update, services));
                }
            }
        }

        // Pop the branch stack
        result.add(new ScriptCommandAst("branches", Map.of(), List.of("pop")));

        return result;
    }

    private static ScriptCommandAst renderObtainCommand(ProofCmdContext ctx,
            Map<ParserRuleContext, JTerm> termMap,
            @Nullable OpReplacer update, Services services) throws ScriptException {
        Map<String, Object> named = new HashMap<>();

        String argName = switch (ctx.obtKind.getType()) {
            case JmlLexer.SUCH_THAT -> "such_that";
            case JmlLexer.EQUAL_SINGLE -> "equals";
            case JmlLexer.FROM_GOAL -> "from_goal";
            default -> throw new ScriptException("Unknown obtain kind: " + ctx.obtKind.getText());
        };

        named.put("var", ctx.var.getText());

        if (ctx.expression() == null) {
            named.put(argName, true);
        } else {
            JmlParser.ExpressionContext exp = ctx.expression();
            Object value;
            if (isStringLiteral(exp)) {
                value = StringUtil.stripQuotes(exp.getText());
            } else {
                value = termMap.get(exp);
                if (update != null) {
                    // Wrap in update application if an update is present
                    value = update.replace((JTerm) value);
                }
            }
            if (value instanceof JTerm term) {
                value = new ObtainAwareTerm(term);
            }
            named.put(argName, value);
        }

        return new ScriptCommandAst("__obtain", named, List.of(), Location.fromToken(ctx.start));
    }

    private static @NonNull ScriptCommandAst renderRegularCommand(ProofCmdContext ctx,
            Map<ParserRuleContext, JTerm> termMap, @Nullable OpReplacer update, Services services) {
        Map<String, Object> named = new HashMap<>();
        List<Object> positional = new ArrayList<>();
        for (ProofArgContext argContext : ctx.proofArg()) {
            Object value;
            JmlParser.ExpressionContext exp = argContext.expression();
            if (isStringLiteral(exp)) {
                value = StringUtil.stripQuotes(exp.getText());
            } else {
                value = termMap.get(exp);
                if (update != null) {
                    // Wrap in update application if an update is present
                    value = update.replace((JTerm) value);
                }
            }
            if (value instanceof JTerm term) {
                value = new ObtainAwareTerm(term);
            }
            if (argContext.argLabel != null) {
                named.put(argContext.argLabel.getText(), value);
            } else {
                positional.add(value);
            }
        }
        return new ScriptCommandAst(ctx.cmd.getText(), named, positional,
            Location.fromToken(ctx.start));
    }

    private static boolean isStringLiteral(JmlParser.ExpressionContext ctx) {
        return ctx.start == ctx.stop && ctx.start.getType() == JmlParser.STRING_LITERAL;
    }

    /**
     * Build a map from JML expression contexts to corresponding JTerms for a JML assert.
     */
    public static Map<ParserRuleContext, JTerm> getTermMapForAssert(JmlAssert jmlAssert,
            JavaBlock javaBlock, Services services) {
        SpecificationRepository.@org.jspecify.annotations.Nullable JmlStatementSpec jmlspec =
            services.getSpecificationRepository().getStatementSpec(jmlAssert);
        if (jmlspec == null) {
            throw new IllegalStateException(
                "No specification found for JML assert statement at " + jmlAssert);
        }
        ImmutableList<JTerm> terms = ImmutableList.of();
        for (int i = jmlspec.terms().size() - 1; i >= 1; i--) {
            terms = terms.prepend(correctSelfVar(i, javaBlock, jmlspec, services));
        }
        ImmutableList<JmlParser.ExpressionContext> jmlExprs = jmlAssert.collectTerms().tail();
        Map<ParserRuleContext, JTerm> result = new IdentityHashMap<>();
        assert terms.size() == jmlExprs.size();
        for (int i = 0; i < terms.size(); i++) {
            result.put(jmlExprs.get(i), terms.get(i));
        }
        return result;
    }

    private static JTerm correctSelfVar(int index, JavaBlock javaBlock,
            SpecificationRepository.JmlStatementSpec spec, Services services) {
        final MethodFrame frame = JavaTools.getInnermostMethodFrame(javaBlock, services);
        final JTerm self = MiscTools.getSelfTerm(frame, services);
        return spec.getTerm(services, self, index);
    }

    /**
     * Prepare a ProofScriptEngine with the standard obtain-variable converters and initial state.
     */
    public static ProofScriptEngine prepareEngine(Proof proof, Goal initiallySelected,
            Map<LocationVariable, JFunction> obtainMap) {
        ProofScriptEngine pse = new ProofScriptEngine(proof);
        pse.setInitiallySelectedGoal(initiallySelected);
        pse.getStateMap().getUserData().set(USER_DATA_JML_OBTAIN_VAR_MAP, obtainMap);
        pse.getStateMap().getValueInjector().addConverter(JTerm.class, ObtainAwareTerm.class,
            oat -> oat.resolve(obtainMap, initiallySelected.proof().getServices()));
        // TODO: Perhaps have holes also in JML?
        pse.getStateMap().getValueInjector().addConverter(TermWithHoles.class,
            ObtainAwareTerm.class,
            oat -> new TermWithHoles(
                oat.resolve(obtainMap, initiallySelected.proof().getServices())));
        pse.getStateMap().getValueInjector().addConverter(boolean.class, ObtainAwareTerm.class,
            oat -> Boolean.parseBoolean(oat.term.toString()));
        return pse;
    }


    public static JmlIO prepareJmlIO(Services services, ProgramMethod pm) {
        JmlIO io = new JmlIO(services);
        if(!pm.isStatic()) {
            io.selfVar((LocationVariable) services.getNamespaces().programVariables().lookup("self"));
        }
        io.classType(pm.getContainerType());
        // FIXME: Make this respect the right math mode (but this is not soundess-critical)
        io.specMathMode(SpecMathMode.BIGINT);
        // check if this lookup is necessary at all ...
        ImmutableList<LocationVariable> instParams = pm.collectParameters().map(param -> (LocationVariable)services.getNamespaces().programVariables().lookup(param.name()));
        io.parameters(instParams);
        return io;
    }

    public static Map<ParserRuleContext, JTerm> createTermMap(
            JmlParser.@Nullable ExpressionContext assertedCond,
            KeyAst.JMLProofScript script,
            List assignments,
            ProgramMethod pm,
            JmlIO io,
            Services services) {
        ImmutableList<LocationVariable> obtainedVars = script.getObtainedProgramVars(io);
        io.parameters(io.getParamVars().prepend(obtainedVars));
        ImmutableList<JmlParser.ExpressionContext> collectedTerms = script.collectTerms();
        if(assertedCond != null) {
            collectedTerms = collectedTerms.prepend(assertedCond);
        }
        Map<ParserRuleContext, JTerm> termMap = new IdentityHashMap<>();
        for (JmlParser.ExpressionContext ectx : collectedTerms) {
            JTerm term = io.translateTerm(ectx);
            termMap.put(ectx, term);
        }
        return termMap;
    }

}
