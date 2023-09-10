/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.rule.tacletbuilder;

import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilderSchemaVarCollector;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;


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

    public AbstractInfFlowTacletBuilder(final Services services) {
        super(services.getTermFactory(), services);
    }


    ImmutableList<Term> createTermSV(ImmutableList<Term> ts, String schemaPrefix,
            Services services) {
        ImmutableList<Term> result = ImmutableSLList.nil();
        for (Term t : ts) {
            result = result.append(createTermSV(t, schemaPrefix, services));
        }
        return result;
    }


    Term createTermSV(Term t, String schemaPrefix, Services services) {
        if (t == null) {
            return null;
        }
        t = unlabel(t);
        String svName = MiscTools.toValidVariableName(schemaPrefix + t.toString()).toString();
        Sort sort = t.sort();
        Name name = services.getVariableNamer().getTemporaryNameProposal(svName);
        return var(SchemaVariableFactory.createTermSV(name, sort));
    }


    SchemaVariable createVariableSV(QuantifiableVariable v, String schemaPrefix,
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
            Iterable<SchemaVariable> quantifiableSVs) throws IllegalArgumentException {
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


    Map<QuantifiableVariable, SchemaVariable> collectQuantifiableVariables(Term replaceWithTerm,
            Services services) {
        QuantifiableVariableVisitor qvVisitor = new QuantifiableVariableVisitor();
        replaceWithTerm.execPreOrder(qvVisitor);
        LinkedList<QuantifiableVariable> quantifiableVariables = qvVisitor.getResult();
        final Map<QuantifiableVariable, SchemaVariable> quantifiableVarsToSchemaVars =
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
    public Term eqAtLocs(Services services, Term heap1, Term locset1, Term heap2, Term locset2) {
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
    public Term eqAtLocsPost(Services services, Term heap1Pre, Term heap1Post, Term locset1,
            Term heap2Pre, Term heap2Post, Term locset2) {
        return (locset1.equals(empty()) && locset2.equals(empty())) ? tt()
                : func(services.getNamespaces().functions().lookup(EQUAL_LOCS_POST),
                    heap1Pre, heap1Post, locset1, heap2Pre, heap2Post, locset2);
    }

    static class QuantifiableVariableVisitor implements Visitor {

        private final LinkedList<QuantifiableVariable> vars =
            new LinkedList<>();

        @Override
        public boolean visitSubtree(Term visited) {
            return true;
        }

        @Override
        public void visit(Term visited) {
            final ImmutableArray<QuantifiableVariable> boundVars = visited.boundVars();
            for (QuantifiableVariable var : boundVars) {
                vars.add(var);
            }
        }


        @Override
        public void subtreeEntered(Term subtreeRoot) {
            // nothing to do
        }


        @Override
        public void subtreeLeft(Term subtreeRoot) {
            // nothing to do
        }


        public LinkedList<QuantifiableVariable> getResult() {
            return vars;
        }
    }
}
