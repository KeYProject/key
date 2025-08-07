/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.expression.operator.LessThan;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.IGuard;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.JModality;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.speclang.LoopSpecification;

import org.key_project.logic.Term;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * The built in rule app for the loop invariant rule.
 */
@NullMarked
public class LoopInvariantBuiltInRuleApp<T extends BuiltInRule>
        extends AbstractBuiltInRuleApp<T> {

    private final While loop;

    private LoopSpecification spec;
    private final List<LocationVariable> heapContext;
    private ExecutionContext executionContext;
    private JTerm guard;

    private final TermServices services;

    public LoopInvariantBuiltInRuleApp(T rule, PosInOccurrence pos, TermServices services) {
        this(rule, pos, null, null, null, services);
    }

    protected LoopInvariantBuiltInRuleApp(T rule, PosInOccurrence pio,
            @Nullable ImmutableList<PosInOccurrence> ifInsts,
            @Nullable LoopSpecification inv,
            @Nullable List<LocationVariable> heapContext, TermServices services) {
        super(rule, pio, ifInsts);
        assert pio != null;
        this.loop = (While) JavaTools.getActiveStatement(programTerm().javaBlock());
        assert loop != null;
        this.spec = instantiateIndexValues(inv, services);
        this.heapContext = heapContext;
        this.services = services;
    }

    /**
     * Replaces the function symbols "index" and "values" by actual program entities. The index
     * function symbol is a placeholder which stems from translating the <code>\index</code> keyword
     * from JML. The values function symbol is a placeholder which stems from translating the
     * <code>\values</code> keyword from JML. Both are used to refer to a runtime-generated
     * variable. If the loop guard has the form <code>i < x</code>, index is instantiated with
     * <code>i</code>, if the second statement in the loop body has the form <code>v = xxx</code>,
     * where <code>v</code> is a ghost variable of type sequence, values is instantiated with
     * <code>v</code>, otherwise <code>rawInv</code> is returned.
     *
     * @param services TODO
     */
    private @Nullable LoopSpecification instantiateIndexValues(LoopSpecification rawInv,
            TermServices services) {
        if (rawInv == null) {
            return null;
        }
        Map<LocationVariable, JTerm> invs = rawInv.getInternalInvariants();
        Map<LocationVariable, JTerm> freeInvs = rawInv.getInternalFreeInvariants();
        JTerm var = rawInv.getInternalVariant();
        final TermBuilder tb = services.getTermBuilder();
        boolean skipIndex = false;
        boolean skipValues = false;


        // try to retrieve a loop index variable
        IGuard guard = loop.getGuard();
        // the guard is expected to be of the form "i < x" and we want to retrieve "i".
        assert guard.getChildCount() == 1 : "child count: " + guard.getChildCount();
        ProgramElement guardStatement = guard.getChildAt(0);
        skipIndex = !(guardStatement instanceof LessThan);
        Expression loopIndex =
            skipIndex ? null : (Expression) ((LessThan) guard.getChildAt(0)).getChildAt(0);
        skipIndex = skipIndex || !(loopIndex instanceof ProgramVariable);
        final JTerm loopIdxVar = skipIndex ? null : tb.var((ProgramVariable) loopIndex);

        // try to retrieve a sequence of values
        Statement body = loop.getBody();
        skipValues = !(body instanceof StatementBlock);
        StatementBlock block = skipValues ? null : ((StatementBlock) body);
        // get the second statement if possible
        Statement last =
            (skipValues || block.getStatementCount() < 2) ? null : block.getStatementAt(1);
        skipValues = skipValues || !(last instanceof CopyAssignment);
        CopyAssignment assignment = skipValues ? null : ((CopyAssignment) last);
        ProgramElement lhs = skipValues ? null : assignment.getChildAt(0);
        skipValues = skipValues || !(lhs instanceof ProgramVariable);
        final JTerm valuesVar = skipValues ? null : tb.var((ProgramVariable) lhs);

        // set up replacement visitors
        final class IndexTermReplacementVisitor implements DefaultVisitor {

            private JTerm result;

            @Override
            public void visit(Term visited) {
                // TODO: Remove cast when/if term builder is moved
                result = replace((JTerm) visited);
            }

            public JTerm getResult() {
                return result;
            }

            private @Nullable JTerm replace(JTerm visited) {
                ImmutableArray<JTerm> subs = visited.subs();
                if (subs.isEmpty()) {
                    if (visited.op().name().toString().equals("index")) {
                        return loopIdxVar;
                    } else {
                        return visited;
                    }
                } else {
                    JTerm[] newSubs = new JTerm[subs.size()];
                    for (int i = 0; i < subs.size(); i++) {
                        newSubs[i] = replace(subs.get(i));
                    }
                    return tb.tf().createTerm(visited.op(), new ImmutableArray<>(newSubs),
                        visited.boundVars(), visited.getLabels());
                }
            }
        }
        final class ValuesTermReplacementVisitor implements DefaultVisitor {

            private JTerm result;

            @Override
            public void visit(Term visited) {
                result = replace((JTerm) visited);
            }

            public JTerm getResult() {
                return result;
            }

            private @Nullable JTerm replace(JTerm visited) {
                ImmutableArray<JTerm> subs = visited.subs();
                if (subs.isEmpty()) {
                    if (visited.op().name().toString().equals("values")) {
                        return valuesVar;
                    } else {
                        return visited;
                    }
                } else {
                    JTerm[] newSubs = new JTerm[subs.size()];
                    for (int i = 0; i < subs.size(); i++) {
                        newSubs[i] = replace(subs.get(i));
                    }
                    return tb.tf().createTerm(visited.op(), new ImmutableArray<>(newSubs),
                        visited.boundVars(), visited.getLabels());
                }
            }
        }

        // replace index
        Map<LocationVariable, JTerm> newInvs = new LinkedHashMap<>(invs);
        if (!skipIndex) {
            IndexTermReplacementVisitor v = new IndexTermReplacementVisitor();
            for (LocationVariable heap : invs.keySet()) {
                JTerm inv = invs.get(heap);
                if (inv != null) {
                    v.visit(inv);
                    inv = v.getResult();
                    newInvs.put(heap, inv);
                }
            }
            if (var != null) {
                v.visit(var);
                var = v.getResult();
            }
        }

        Map<LocationVariable, JTerm> newFreeInvs =
            new LinkedHashMap<>(freeInvs);
        if (!skipIndex) {
            IndexTermReplacementVisitor v = new IndexTermReplacementVisitor();
            for (LocationVariable heap : freeInvs.keySet()) {
                JTerm inv = freeInvs.get(heap);
                if (inv != null) {
                    v.visit(inv);
                    inv = v.getResult();
                    newFreeInvs.put(heap, inv);
                }
            }
            if (var != null) {
                v.visit(var);
                var = v.getResult();
            }
        }

        // replace values
        if (!skipValues) {
            ValuesTermReplacementVisitor v = new ValuesTermReplacementVisitor();
            for (LocationVariable heap : invs.keySet()) {
                JTerm inv = invs.get(heap);
                if (inv != null) {
                    v.visit(inv);
                    inv = v.getResult();
                    newInvs.put(heap, inv);
                }
            }
            if (var != null) {
                v.visit(var);
                var = v.getResult();
            }
        }
        return rawInv.instantiate(newInvs, newFreeInvs, var);
    }

    protected LoopInvariantBuiltInRuleApp(T rule, PosInOccurrence pio,
            LoopSpecification inv, TermServices services) {
        this(rule, pio, null, inv, null, services);
    }

    public boolean complete() {
        return spec != null && loop != null && invariantAvailable()
                && (!variantRequired() || variantAvailable());
    }

    public LoopSpecification getSpec() {
        return spec;
    }

    public While getLoopStatement() {
        return loop;
    }

    public boolean invariantAvailable() {
        boolean result = spec != null && spec.getInternalInvariants() != null;
        if (result) {
            Map<LocationVariable, JTerm> invs = spec.getInternalInvariants();
            Map<LocationVariable, JTerm> freeInvs = spec.getInternalFreeInvariants();
            result = false;
            for (LocationVariable heap : heapContext) {
                if (invs.get(heap) != null || freeInvs.get(heap) != null) {
                    result = true;
                    break;
                }
            }
        }
        return result;
    }

    public boolean isSufficientlyComplete() {
        return pio != null && loop != null;
    }

    public JTerm programTerm() {
        if (posInOccurrence() != null) {
            return TermBuilder.goBelowUpdates((JTerm) posInOccurrence().subTerm());
        }
        return null;
    }

    @Override
    public LoopInvariantBuiltInRuleApp replacePos(PosInOccurrence newPos) {
        return new LoopInvariantBuiltInRuleApp(builtInRule, newPos, ifInsts, spec, heapContext,
            services);
    }

    public LoopSpecification retrieveLoopInvariantFromSpecification(Services services) {
        return services.getSpecificationRepository().getLoopSpec(loop);
    }

    @Override
    public LoopInvariantBuiltInRuleApp setAssumesInsts(
            ImmutableList<PosInOccurrence> ifInsts) {
        setMutable(ifInsts);
        return this;

    }

    public LoopInvariantBuiltInRuleApp setLoopInvariant(LoopSpecification inv) {
        assert inv != null;
        if (this.loop == inv.getLoop()) {
            this.spec = inv;
        }
        return new LoopInvariantBuiltInRuleApp(builtInRule, pio, ifInsts, inv, heapContext,
            services);
    }


    public void setGuard(JTerm guard) {
        this.guard = guard;
    }

    public void setExecutionContext(ExecutionContext context) {
        this.executionContext = context;
    }

    @Override
    public LoopInvariantBuiltInRuleApp tryToInstantiate(Goal goal) {
        if (spec != null) {
            return this;
        }
        final Services services = goal.proof().getServices();
        LoopSpecification inv = retrieveLoopInvariantFromSpecification(services);
        var m = ((JModality) programTerm().op()).<JModality.JavaModalityKind>kind();
        return new LoopInvariantBuiltInRuleApp(builtInRule, pio, ifInsts, inv,
            HeapContext.getModifiableHeaps(services, m.transaction()), services);
    }

    public boolean variantAvailable() {
        return spec != null && spec.getInternalVariant() != null;
    }

    public boolean variantRequired() {
        return ((JModality) programTerm().op()).<JModality.JavaModalityKind>kind()
                .terminationSensitive();
    }

    @Override
    public List<LocationVariable> getHeapContext() {
        return heapContext;
    }


    public JTerm getGuard() {
        return guard;
    }

    public ExecutionContext getExecutionContext() {
        return executionContext;
    }
}
