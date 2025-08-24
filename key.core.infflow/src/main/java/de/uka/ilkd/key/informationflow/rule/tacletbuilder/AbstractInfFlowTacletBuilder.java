/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.rule.tacletbuilder;

import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilderSchemaVarCollector;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Name;
import org.key_project.logic.Visitor;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.NonNull;


/**
 * Builds the rule which inserts information flow contract applications.
 * <p/>
 *
 * @author christoph
 */
abstract class AbstractInfFlowTacletBuilder extends TermBuilder {

    /**
     * Constant name for eqAtLocs function.
     */
    private static final Name EQUAL_LOCS = new Name("__EQUALS__LOCS__");

    /**
     * Constant name for eqAtLocsPost function.
     */
    private static final Name EQUAL_LOCS_POST = new Name("__EQUALS__LOCS__POST__");

    protected AbstractInfFlowTacletBuilder(final Services services) {
        super(services.getTermFactory(), services);
    }


    ImmutableList<JTerm> createTermSV(ImmutableList<JTerm> ts, String schemaPrefix,
            Services services) {
        ImmutableList<JTerm> result = ImmutableSLList.nil();
        for (JTerm t : ts) {
            result = result.append(createTermSV(t, schemaPrefix, services));
        }
        return result;
    }


    JTerm createTermSV(JTerm t, String schemaPrefix, Services services) {
        if (t == null) {
            return null;
        }
        t = unlabel(t);
        String svName = MiscTools.toValidVariableName(schemaPrefix + t.toString()).toString();
        Sort sort = t.sort();
        Name name = services.getVariableNamer().getTemporaryNameProposal(svName);
        return var(SchemaVariableFactory.createTermSV(name, sort));
    }


    VariableSV createVariableSV(QuantifiableVariable v, String schemaPrefix,
            Services services) {
        if (v == null) {
            return null;
        }
        String svName = MiscTools.toValidVariableName(schemaPrefix + v.name()).toString();
        Sort sort = v.sort();
        Name name = services.getVariableNamer().getTemporaryNameProposal(svName);
        return SchemaVariableFactory.createVariableSV(name, sort);

    }


    void addVarconds(RewriteTacletBuilder<? extends RewriteTaclet> tacletBuilder,
            Iterable<? extends SchemaVariable> quantifiableSVs) throws IllegalArgumentException {
        RewriteTacletBuilderSchemaVarCollector svCollector =
            new RewriteTacletBuilderSchemaVarCollector(tacletBuilder);
        Set<SchemaVariable> schemaVars = svCollector.collectSchemaVariables();
        for (SchemaVariable sv : schemaVars) {
            if (sv instanceof TermSV) {
                for (SchemaVariable qv : quantifiableSVs) {
                    tacletBuilder.addVarsNotFreeIn(qv, sv);
                }
            }
        }
    }


    Map<QuantifiableVariable, VariableSV> collectQuantifiableVariables(JTerm replaceWithTerm,
            Services services) {
        QuantifiableVariableVisitor qvVisitor = new QuantifiableVariableVisitor();
        replaceWithTerm.execPreOrder(qvVisitor);
        LinkedList<QuantifiableVariable> quantifiableVariables = qvVisitor.getResult();
        final Map<QuantifiableVariable, VariableSV> quantifiableVarsToSchemaVars =
            new LinkedHashMap<>();
        for (QuantifiableVariable qv : quantifiableVariables) {
            quantifiableVarsToSchemaVars.put(qv, createVariableSV(qv, "", services));
        }
        return quantifiableVarsToSchemaVars;
    }

    // -------------------------------------------------------------------------
    // information flow operators
    // -------------------------------------------------------------------------

    /**
     * Get eqAtLocs function as a term.
     *
     * @param services the Services object.
     * @param heap1 the first heap term.
     * @param locset1 the first location set term.
     * @param heap2 the first heap term.
     * @param locset2 the first location set term.
     * @return The eqAtLocs function term.
     */
    public JTerm eqAtLocs(Services services, JTerm heap1, JTerm locset1, JTerm heap2,
            JTerm locset2) {
        return (locset1.equals(empty()) && locset2.equals(empty())) ? tt()
                : func(services.getNamespaces().functions().lookup(EQUAL_LOCS), heap1,
                    locset1, heap2, locset2);
    }

    /**
     * Get eqAtLocsPost function as a term.
     *
     * @param services the Services object.
     * @param heap1Pre the first pre-heap term.
     * @param heap1Post the first post-heap term.
     * @param locset1 the first location set term.
     * @param heap2Pre the second pre-heap term.
     * @param heap2Post the second post-heap term.
     * @param locset2 the second location set term.
     * @return The eqAtLocsPost function term.
     */
    public JTerm eqAtLocsPost(Services services, JTerm heap1Pre, JTerm heap1Post, JTerm locset1,
            JTerm heap2Pre, JTerm heap2Post, JTerm locset2) {
        return (locset1.equals(empty()) && locset2.equals(empty())) ? tt()
                : func(services.getNamespaces().functions().lookup(EQUAL_LOCS_POST),
                    heap1Pre, heap1Post, locset1, heap2Pre, heap2Post, locset2);
    }

    static class QuantifiableVariableVisitor implements Visitor<@NonNull JTerm> {

        private final LinkedList<QuantifiableVariable> vars = new LinkedList<>();

        @Override
        public boolean visitSubtree(JTerm visited) {
            return true;
        }

        @Override
        public void visit(JTerm visited) {
            for (var boundVar : visited.boundVars()) {
                vars.add(boundVar);
            }
        }


        @Override
        public void subtreeEntered(JTerm subtreeRoot) {
            // nothing to do
        }


        @Override
        public void subtreeLeft(JTerm subtreeRoot) {
            // nothing to do
        }


        public LinkedList<QuantifiableVariable> getResult() {
            return vars;
        }
    }
}
