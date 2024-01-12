/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import java.util.ArrayList;
import java.util.List;
import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.Private;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;


/**
 * A class axiom that connects an observer symbol representing a Java method (i.e., an object of
 * type IProgramMethod), with the corresponding method body.
 */
public final class QueryAxiom extends ClassAxiom {

    /**
     * The unique internal name of the query axiom.
     */
    private final String name;
    /**
     * The axiomatised query function symbol.
     */
    private final IProgramMethod target;
    /**
     * The KeYJavaType representing the function to which the query belongs.
     */
    private final KeYJavaType kjt;

    public QueryAxiom(String name, IProgramMethod target, KeYJavaType kjt) {
        assert name != null;
        assert target != null;
        assert target.getReturnType() != null;
        assert kjt != null;
        this.name = name;
        this.target = target;
        this.kjt = kjt;
    }

    @Override
    public QueryAxiom map(UnaryOperator<Term> op, Services services) {
        return this;
    }


    @Override
    public boolean equals(Object o) {
        if (o == null || o.getClass() != getClass()) {
            return false;
        }
        final QueryAxiom other = (QueryAxiom) o;
        return name.equals(other.name) && target.equals(other.target) && kjt.equals(other.kjt);
    }

    @Override
    public int hashCode() {
        return name.hashCode() * 7 + target.hashCode() * 49 + kjt.hashCode() * 17;
    }


    @Override
    public String getName() {
        return name;
    }


    @Override
    public IObserverFunction getTarget() {
        return target;
    }


    @Override
    public KeYJavaType getKJT() {
        return kjt;
    }


    @Override
    public VisibilityModifier getVisibility() {
        return new Private();
    }


    @Override
    public ImmutableSet<Taclet> getTaclets(ImmutableSet<Pair<Sort, IObserverFunction>> toLimit,
            Services services) {
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final TermBuilder tb = services.getTermBuilder();

        // create schema variables
        final List<SchemaVariable> heapSVs = new ArrayList<>();
        for (int i = 0; i < target.getHeapCount(services); i++) {
            heapSVs.add(SchemaVariableFactory.createTermSV(new Name("h" + i), heapLDT.targetSort(),
                false, false));
        }
        final SchemaVariable selfSV = target.isStatic() ? null
                : SchemaVariableFactory.createTermSV(new Name("self"), kjt.getSort(), false, false);
        final SchemaVariable[] paramSVs = new SchemaVariable[target.getNumParams()];
        for (int i = 0; i < paramSVs.length; i++) {
            paramSVs[i] = SchemaVariableFactory.createTermSV(new Name("p" + i),
                target.getParamType(i).getSort(), false, false);
        }
        final SchemaVariable skolemSV = SchemaVariableFactory
                .createSkolemTermSV(new Name(target.getName() + "_sk"), target.sort());

        // create schema variables for program variables
        final ProgramSV selfProgSV = target.isStatic() ? null
                : SchemaVariableFactory.createProgramSV(new ProgramElementName("#self"),
                    ProgramSVSort.VARIABLE, false);
        final ProgramSV[] paramProgSVs = new ProgramSV[target.getNumParams()];
        for (int i = 0; i < paramProgSVs.length; i++) {
            paramProgSVs[i] = SchemaVariableFactory.createProgramSV(
                new ProgramElementName("#p" + i), ProgramSVSort.VARIABLE, false);
        }
        final ProgramSV resultProgSV = SchemaVariableFactory
                .createProgramSV(new ProgramElementName("#res"), ProgramSVSort.VARIABLE, false);

        // create update and postcondition linking schema variables and
        // program variables
        Term update = null;
        int hc = 0;
        for (LocationVariable heap : HeapContext.getModHeaps(services, false)) {
            if (hc >= target.getHeapCount(services)) {
                break;
            }
            Term u = tb.elementary(heap, tb.var(heapSVs.get(hc++)));
            if (update == null) {
                update = u;
            } else {
                update = tb.parallel(update, u);
            }
        }
        update = target.isStatic() ? update
                : tb.parallel(update, tb.elementary(selfProgSV, tb.var(selfSV)));
        for (int i = 0; i < paramSVs.length; i++) {
            update = tb.parallel(update, tb.elementary(paramProgSVs[i], tb.var(paramSVs[i])));
        }
        final Term post = tb.imp(tb.reachableValue(tb.var(resultProgSV), target.getReturnType()),
            tb.equals(tb.var(skolemSV), tb.var(resultProgSV)));

        // create java block
        final ImmutableList<KeYJavaType> sig = ImmutableSLList.<KeYJavaType>nil()
                .append(target.getParamTypes().toArray(new KeYJavaType[target.getNumParams()]));
        final IProgramMethod targetImpl =
            services.getJavaInfo().getProgramMethod(kjt, target.getName(), sig, kjt);
        final MethodBodyStatement mbs = new MethodBodyStatement(targetImpl, selfProgSV,
            resultProgSV, new ImmutableArray<>(paramProgSVs));
        final StatementBlock sb = new StatementBlock(mbs);
        final JavaBlock jb = JavaBlock.createJavaBlock(sb);

        // create if sequent
        final Sequent ifSeq;
        if (target.isStatic()) {
            ifSeq = null;
        } else {
            final Term ifFormula = tb.exactInstance(kjt.getSort(), tb.var(selfSV));
            final SequentFormula ifCf = new SequentFormula(ifFormula);
            final Semisequent ifSemiSeq =
                Semisequent.EMPTY_SEMISEQUENT.insertFirst(ifCf).semisequent();
            ifSeq = Sequent.createAnteSequent(ifSemiSeq);
        }

        // create find
        final Term[] subs = new Term[target.arity()];
        int offset = 0;
        for (SchemaVariable heapSV : heapSVs) {
            subs[offset] = tb.var(heapSV);
            offset++;
        }
        if (!target.isStatic()) {
            subs[offset] = tb.var(selfSV);
            offset++;
        }
        for (SchemaVariable paramSV : paramSVs) {
            subs[offset] = tb.var(paramSV);
            offset++;
        }
        final Term find = tb.func(target, subs);

        // create replacewith
        final Term replacewith = tb.var(skolemSV);

        // create added sequent
        final Term addedFormula = tb.apply(update, tb.prog(Modality.BOX, jb, post), null);
        final SequentFormula addedCf = new SequentFormula(addedFormula);
        final Semisequent addedSemiSeq =
            Semisequent.EMPTY_SEMISEQUENT.insertFirst(addedCf).semisequent();
        final Sequent addedSeq = Sequent.createAnteSequent(addedSemiSeq);

        // build taclet
        final RewriteTacletBuilder<RewriteTaclet> tacletBuilder =
            new RewriteTacletBuilder<>();
        tacletBuilder.setFind(find);
        for (SchemaVariable heapSV : heapSVs) {
            tacletBuilder.addVarsNewDependingOn(skolemSV, heapSV);
        }
        if (!target.isStatic()) {
            tacletBuilder.addVarsNewDependingOn(skolemSV, selfSV);
            tacletBuilder.setIfSequent(ifSeq);
            tacletBuilder.addVarsNew(selfProgSV, kjt);
        }
        for (int i = 0; i < paramSVs.length; i++) {
            tacletBuilder.addVarsNewDependingOn(skolemSV, paramSVs[i]);
            tacletBuilder.addVarsNew(paramProgSVs[i], target.getParamType(i));
        }
        tacletBuilder.addVarsNew(resultProgSV, target.getReturnType());
        tacletBuilder.setApplicationRestriction(RewriteTaclet.SAME_UPDATE_LEVEL);
        tacletBuilder.addTacletGoalTemplate(
            new RewriteTacletGoalTemplate(addedSeq, ImmutableSLList.nil(), replacewith));
        tacletBuilder.setName(MiscTools.toValidTacletName(name));
        tacletBuilder.addRuleSet(new RuleSet(new Name("query_axiom")));
        // Originally used to be "simplify"

        return DefaultImmutableSet.<Taclet>nil().add(tacletBuilder.getTaclet());
        // return DefaultImmutableSet.<Taclet>nil();
    }


    @Override
    public ImmutableSet<Pair<Sort, IObserverFunction>> getUsedObservers(Services services) {
        return DefaultImmutableSet.nil();
    }


    @Override
    public String toString() {
        return "query axiom for " + target;
    }
}
