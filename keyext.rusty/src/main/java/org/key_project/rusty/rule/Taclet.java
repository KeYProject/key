/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;


import org.key_project.logic.Name;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.TacletApplPart;
import org.key_project.rusty.logic.BoundVarsVisitor;
import org.key_project.rusty.logic.Sequent;
import org.key_project.rusty.rule.match.VMTacletMatcher;
import org.key_project.rusty.rule.tacletbuilder.TacletGoalTemplate;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSet;


public abstract class Taclet extends
        org.key_project.prover.rules.Taclet implements Rule {
    /**
     * creates a Taclet (originally known as Schematic Theory Specific Rules)
     *
     * @param name the name of the Taclet
     * @param applPart contains the application part of a Taclet that is the if-sequence, the
     *        variable conditions
     * @param goalTemplates a list of goal descriptions.
     * @param attrs attributes for the Taclet; these are boolean values indicating a noninteractive
     *        or recursive use of the Taclet.
     */
    protected Taclet(Name name, org.key_project.prover.rules.TacletApplPart applPart,
            ImmutableList<? extends org.key_project.prover.rules.tacletbuilder.TacletGoalTemplate> goalTemplates,
            org.key_project.prover.rules.TacletAttributes attrs,
            ImmutableMap<SchemaVariable, org.key_project.prover.rules.TacletPrefix> prefixMap,
            boolean surviveSmbExec,
            ImmutableSet<org.key_project.prover.rules.TacletAnnotation> tacletAnnotations) {
        super(name, applPart, goalTemplates, attrs, prefixMap, surviveSmbExec, tacletAnnotations);
    }

    public final TacletMatcher getMatcher() {
        return (TacletMatcher) super.getMatcher();
    }

    /**
     * creates a Schematic Theory Specific Rule (Taclet) with the given parameters.
     *
     * @param name the name of the Taclet
     * @param applPart contains the application part of a Taclet that is the if-sequence, the
     *        variable conditions
     * @param goalTemplates a list of goal descriptions.
     * @param attrs attributes for the Taclet; these are boolean values indicating a noninteractive
     *        or recursive use of the Taclet.
     */
    protected Taclet(Name name, TacletApplPart applPart,
            ImmutableList<? extends TacletGoalTemplate> goalTemplates,
            org.key_project.prover.rules.TacletAttributes attrs,
            ImmutableMap<SchemaVariable, org.key_project.prover.rules.TacletPrefix> prefixMap,
            ImmutableSet<org.key_project.prover.rules.TacletAnnotation> tacletAnnotations) {
        this(name, applPart, goalTemplates, attrs, prefixMap, false,
            tacletAnnotations);
    }

    /**
     * creates and initializes the taclet matching and execution engines has to be called at the end
     * of initialization
     */
    protected void createTacletServices() {
        createAndInitializeMatcher();
        createAndInitializeExecutor();
    }

    protected void createAndInitializeMatcher() {
        this.matcher = new VMTacletMatcher(this);
    }

    protected abstract void createAndInitializeExecutor();

    /**
     * computes and returns all variables that occur bound in the taclet including the taclets
     * defined in <tt>addrules</tt> sections. The result is cached and therefore only computed once.
     *
     * @return all variables occuring bound in the taclet
     */
    public ImmutableSet<QuantifiableVariable> getBoundVariables() {
        if (boundVariables == null) {
            ImmutableSet<QuantifiableVariable> result =
                DefaultImmutableSet.nil();

            for (final var tgt : goalTemplates()) {
                result = result.union(tgt.getBoundVariables());
            }

            final BoundVarsVisitor bvv = new BoundVarsVisitor();
            bvv.visit((Sequent) assumesSequent());
            result = result.union(bvv.getBoundVariables()).union(getBoundVariablesHelper());

            boundVariables = result;
        }

        return boundVariables;
    }

    /**
     * collects bound variables in taclet entities others than goal templates
     *
     * @return set of variables that occur bound in taclet entities others than goal templates
     */
    protected abstract ImmutableSet<QuantifiableVariable> getBoundVariablesHelper();

    /**
     * returns the set of schemavariables of the taclet's if-part
     *
     * @return Set of schemavariables of the if part
     */
    protected ImmutableSet<org.key_project.logic.op.sv.SchemaVariable> getAssumesVariables() {
        // should be synchronized
        if (assumesVariables == null) {
            TacletSchemaVariableCollector svc = new TacletSchemaVariableCollector();
            svc.visit((Sequent) assumesSequent());

            assumesVariables = DefaultImmutableSet.nil();
            for (final SchemaVariable sv : svc.vars()) {
                assumesVariables = assumesVariables.add(sv);
            }
        }

        return assumesVariables;
    }

    /**
     * returns the computed prefix for the given schemavariable. The prefix of a schemavariable is
     * used to determine if an instantiation is correct, in more detail: it mainly contains all
     * variables that can appear free in an instantiation of the schemvariable sv (rewrite taclets
     * have some special handling, see paper of M. Giese and comment of method isContextInPrefix).
     *
     * @param sv the Schemavariable
     * @return prefix of schema variable sv
     */
    public TacletPrefix getPrefix(SchemaVariable sv) {
        return (TacletPrefix) prefixMap.get(sv);
    }

    public TacletExecutor<?> getExecutor() {
        return (TacletExecutor<? extends Taclet>) executor;
    }

    @Override
    public abstract Taclet setName(String s);
}
