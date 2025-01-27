/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.metaconstruct;

import java.util.*;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.rusty.RustTools;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.ast.expr.FunctionFrame;
import org.key_project.rusty.ast.expr.LoopExpression;
import org.key_project.rusty.ast.visitor.RustyASTVisitor;
import org.key_project.rusty.logic.TermBuilder;
import org.key_project.rusty.logic.op.AbstractTermTransformer;
import org.key_project.rusty.logic.op.Modality;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.rule.inst.SVInstantiations;
import org.key_project.rusty.speclang.LoopSpecImpl;
import org.key_project.rusty.speclang.LoopSpecification;
import org.key_project.rusty.util.MiscTools;
import org.key_project.util.collection.ImmutableList;

/**
 * Transformer that introduces concrete prestate variables
 */
public class IntroAtPreDefs extends AbstractTermTransformer {
    public IntroAtPreDefs() {
        super(new Name("introAtPreDefs"), 1);
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst, Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final Term target = term.sub(0);

        final var pe = ((Modality) target.op()).program().program();

        final var fnFrame = RustTools.getInnermostFunctionFrame(pe, services);

        final var updater = new PrestateVariablesUpdater(fnFrame, services, tb);
        updater.start();

        return tb.apply(updater.atPreUpdate, target);
    }

    private class PrestateVariablesUpdater extends RustyASTVisitor {
        /**
         * A TermBuilder
         */
        private final TermBuilder tb;

        private final FunctionFrame frame;

        /**
         * function name for which prestate variables get introduced.
         */
        private final String functionName;

        /**
         * renamings Term form.
         */
        private final Map<ProgramVariable, Term> atPres = new LinkedHashMap<>();

        /**
         * renamings ProgramVariable form.
         */
        private final Map<ProgramVariable, ProgramVariable> atPreVars = new LinkedHashMap<>();

        /**
         * update Term for the prestate variables. Will get completed as the visitor runs.
         */
        private Term atPreUpdate;

        public PrestateVariablesUpdater(final FunctionFrame frame, final Services services,
                final TermBuilder tb) {
            super(frame, services);
            this.frame = frame;
            this.tb = tb;
            atPreUpdate = tb.skip();
            functionName = frame.getFunction().name().toString();
        }


        @Override
        protected void doDefaultAction(RustyProgramElement node) {

        }

        @Override
        public void performActionOnLoopInvariant(final LoopSpecification spec) {
            addNeededVariables(spec.getInternalAtPres().keySet());
            final Term newVariant = spec.getVariant(atPres, services);
            final Term newInvariant = spec.getInvariant(atPres, services);
            LoopExpression loop = spec.getLoop();
            final ImmutableList<Term> newLocalIns = tb.var(MiscTools.getLocalIns(loop, services));
            final ImmutableList<Term> newLocalOuts = tb.var(MiscTools.getLocalOuts(loop, services));
            final var newSpec =
                new LoopSpecImpl(loop, newInvariant, newVariant, newLocalIns, newLocalOuts, atPres);
            services.getSpecificationRepository().addLoopSpec(newSpec);
        }

        public void addNeededVariables(Collection<ProgramVariable> variables) {
            List<ProgramVariable> vars = new ArrayList<>(variables);

            for (ProgramVariable var : vars) {
                if (atPres.containsKey(var)) {
                    continue;
                }
                final ProgramVariable l = tb.progVar(var.name() + "Before_" + functionName,
                    var.getKeYRustyType(), true);
                services.getNamespaces().programVariables().addSafely(l);

                final Term u = tb.elementary(l, tb.var(var));
                atPreUpdate = tb.parallel(atPreUpdate, u);

                atPres.put(var, tb.var(l));
                atPreVars.put(var, l);
            }
        }
    }
}
