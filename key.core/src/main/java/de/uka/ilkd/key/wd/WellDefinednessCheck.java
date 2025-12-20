/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.wd;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.init.WellDefinednessPO;
import de.uka.ilkd.key.proof.init.WellDefinednessPO.Variables;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.jml.JMLInfoExtractor;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;
import org.key_project.prover.rules.RuleSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.Pair;

import static de.uka.ilkd.key.logic.equality.IrrelevantTermLabelsProperty.IRRELEVANT_TERM_LABELS_PROPERTY;

/**
 * A contract for checking the well-definedness of a jml specification element (i.e. a class
 * invariant, a method contract, a model field or any jml statement), consisting of precondition,
 * modifiable-clause, postcondition, accessible-clause, measured-by-clause and represents-clause.
 *
 * @author Michael Kirsten
 */
public abstract class WellDefinednessCheck implements Contract {

    private static final String OPTION = "wdChecks";
    public static final String INV_TACLET = "wd_Invariant";
    public static final String OP_TACLET = "wd_Operation";
    public static final String OP_EXC_TACLET = "wd_Exc_Operation";

    enum Type {
        CLASS_INVARIANT, OPERATION_CONTRACT, LOOP_INVARIANT, BLOCK_CONTRACT
    }

    private final String name;
    private final int id;
    private final Type type;
    private final IObserverFunction target;
    private final LocationVariable heap;
    private final OriginalVariables origVars;

    private Condition requires;
    private JTerm modifiable;
    private Condition ensures;
    private JTerm accessible;
    private JTerm mby;
    private JTerm represents;

    final TermBuilder TB;

    WellDefinednessCheck(String name, int id, IObserverFunction target, OriginalVariables origVars,
            Type type, Services services) {
        this.id = id;
        this.name = name + " WD." + id;
        this.type = type;
        this.target = target;
        this.heap = services.getTypeConverter().getHeapLDT().getHeap();
        this.origVars = origVars;
        this.TB = services.getTermBuilder();
    }

    WellDefinednessCheck(String name, int id, Type type, IObserverFunction target,
            LocationVariable heap, OriginalVariables origVars, Condition requires, JTerm modifiable,
            JTerm accessible, Condition ensures, JTerm mby, JTerm represents, TermBuilder tb) {
        this.name = name;
        this.id = id;
        this.type = type;
        this.target = target;
        this.heap = heap;
        this.origVars = origVars;
        this.requires = requires;
        this.modifiable = modifiable;
        this.accessible = accessible;
        this.ensures = ensures;
        this.mby = mby;
        this.represents = represents;
        this.TB = tb;
    }

    // -------------------------------------------------------------------------
    // Internal Methods
    // -------------------------------------------------------------------------

    /**
     * Splits and sorts a (specification) term in such a way that implicit parts are in the first
     * and explicit parts in the second list.
     *
     * @param spec specification term
     * @return two lists for implicit and explicit specification parts
     */
    private Pair<ImmutableList<JTerm>, ImmutableList<JTerm>> sort(JTerm spec) {
        assert spec != null;
        ImmutableList<JTerm> implicit = ImmutableSLList.nil();
        ImmutableList<JTerm> explicit = ImmutableSLList.nil();
        if (spec.arity() > 0 && spec.op().equals(Junctor.AND)) { // Conjunctions
            assert spec.arity() == 2;
            if (spec.hasLabels()
                    && spec.containsLabel(ParameterlessTermLabel.SHORTCUT_EVALUATION_LABEL)) {
                // Specification conjuncted with short-circuit operator
                for (JTerm sub : spec.subs()) {
                    if (sub.hasLabels() // Found implicit subterms
                            && sub.containsLabel(
                                ParameterlessTermLabel.IMPLICIT_SPECIFICATION_LABEL)) {
                        final Pair<ImmutableList<JTerm>, ImmutableList<JTerm>> p = sort(sub);
                        implicit = implicit.append(p.first).append(p.second);
                    } else { // Subterm not labeled as implicit
                        final Pair<ImmutableList<JTerm>, ImmutableList<JTerm>> p = sort(sub);
                        implicit = implicit.append(p.first);
                        explicit = explicit.append(p.second);
                    }
                }
            } else { // Specification conjuncted with symmetric operator
                final Condition c1 = split(spec.sub(0));
                final Condition c2 = split(spec.sub(1));
                final JTerm a1 = TB.andSC(c1.implicit, c1.explicit);
                final JTerm a2 = TB.andSC(c2.implicit, c2.explicit);
                final JTerm a;
                if (a2.hasLabels()
                        && a2.containsLabel(ParameterlessTermLabel.IMPLICIT_SPECIFICATION_LABEL)) {
                    // Implicit term first
                    a = TB.and(a2, a1);
                } else {
                    a = TB.and(a1, a2);
                }
                if (spec.hasLabels() && spec
                        .containsLabel(ParameterlessTermLabel.IMPLICIT_SPECIFICATION_LABEL)) {
                    // Handled specification is already implicit
                    implicit = implicit.append(a);
                } else {
                    explicit = explicit.append(a);
                }
            }
        } else if (spec.arity() > 0 && spec.op().equals(Junctor.IMP)) { // Implications
            assert spec.arity() == 2;
            final Condition c1 = split(spec.sub(0));
            final Condition c2 = split(spec.sub(1));
            final JTerm i1 = TB.andSC(c1.implicit, c1.explicit);
            final JTerm i2 = TB.andSC(c2.implicit, c2.explicit);
            if (spec.hasLabels()
                    && spec.containsLabel(ParameterlessTermLabel.IMPLICIT_SPECIFICATION_LABEL)) {
                // Handled specification is already implicit
                implicit = implicit.append(TB.imp(i1, i2));
            } else {
                explicit = explicit.append(TB.imp(i1, i2));
            }
        } else { // Other operator
            if (spec.hasLabels()
                    && spec.containsLabel(ParameterlessTermLabel.IMPLICIT_SPECIFICATION_LABEL)) {
                // Handled specification is already implicit
                implicit = implicit.append(spec);
            } else {
                explicit = explicit.append(spec);
            }
        }
        return new Pair<>(implicit, explicit);
    }

    private JTerm replaceSV(JTerm t, JOperatorSV self, ImmutableList<JOperatorSV> params) {
        return replaceSV(t, self, null, null, null, params, getOrigVars(), getHeaps());
    }

    private JTerm replaceSV(JTerm t, JOperatorSV selfVar, JOperatorSV resultVar,
            JOperatorSV excVar, Map<LocationVariable, JOperatorSV> atPreVars,
            ImmutableList<JOperatorSV> paramVars, OriginalVariables origVars,
            ImmutableList<LocationVariable> heaps) {
        var map = getSchemaMap(selfVar, resultVar, excVar, atPreVars, paramVars, origVars, heaps);
        final OpReplacer or = new OpReplacer(map, TB.tf());
        return or.replace(t);
    }

    private JTerm replace(JTerm t, LocationVariable selfVar, LocationVariable resultVar,
            LocationVariable excVar, Map<LocationVariable, LocationVariable> atPreVars,
            ImmutableList<LocationVariable> paramVars, OriginalVariables origVars,
            ImmutableList<LocationVariable> heaps) {
        Map<LocationVariable, LocationVariable> map =
            getReplaceMap(selfVar, resultVar, excVar, atPreVars, paramVars, origVars, heaps);
        final OpReplacer or = new OpReplacer(map, TB.tf());
        return or.replace(t);
    }

    private static Map<LocationVariable, JOperatorSV> getSchemaMap(JOperatorSV selfVar,
            JOperatorSV resultVar, JOperatorSV excVar,
            Map<LocationVariable, JOperatorSV> atPreVars,
            ImmutableList<JOperatorSV> paramVars, OriginalVariables vars,
            ImmutableList<LocationVariable> heaps) {
        final Map<LocationVariable, JOperatorSV> result =
            new LinkedHashMap<>();
        // self
        if (selfVar != null && vars.self != null) {
            assert selfVar.sort().extendsTrans(vars.self.sort());
            result.put(vars.self, selfVar);
        }
        // parameters
        if (paramVars != null && vars.params != null && !paramVars.isEmpty()
                && !vars.params.isEmpty()) {
            assert vars.params.size() == paramVars.size();
            final Iterator<LocationVariable> it1 = vars.params.iterator();
            final Iterator<JOperatorSV> it2 = paramVars.iterator();
            while (it1.hasNext()) {
                var originalParamVar = it1.next();
                var paramVar = it2.next();
                assert originalParamVar.sort().equals(paramVar.sort());
                result.put(originalParamVar, paramVar);
            }
        }
        // result
        if (resultVar != null && vars.result != null) {
            assert vars.result.sort().equals(resultVar.sort());
            result.put(vars.result, resultVar);
        }
        // exception
        if (excVar != null && vars.exception != null) {
            assert vars.exception.sort().equals(excVar.sort());
            result.put(vars.exception, excVar);
        }
        if (atPreVars != null && vars.atPres != null && !atPreVars.isEmpty()
                && !vars.atPres.isEmpty()) {
            for (LocationVariable h : heaps) {
                if (atPreVars.get(h) != null && vars.atPres.get(h) != null) {
                    assert vars.atPres.get(h).sort().equals(atPreVars.get(h).sort());
                    result.put(vars.atPres.get(h), atPreVars.get(h));
                }
            }
        }
        return result;
    }

    private static Map<LocationVariable, LocationVariable> getReplaceMap(LocationVariable selfVar,
            LocationVariable resultVar, LocationVariable excVar,
            Map<LocationVariable, LocationVariable> atPreVars,
            ImmutableList<LocationVariable> paramVars, OriginalVariables vars,
            ImmutableList<LocationVariable> heaps) {
        final Map<LocationVariable, LocationVariable> result =
            new LinkedHashMap<>();
        // self
        if (selfVar != null && vars.self != null) {
            assert vars.self.sort().extendsTrans(selfVar.sort())
                    || selfVar.sort().extendsTrans(vars.self.sort());
            result.put(vars.self, selfVar);
        }
        // parameters
        if (paramVars != null && vars.params != null && !paramVars.isEmpty()
                && !vars.params.isEmpty()) {
            assert vars.params.size() == paramVars.size();
            final Iterator<LocationVariable> it1 = vars.params.iterator();
            final Iterator<LocationVariable> it2 = paramVars.iterator();
            while (it1.hasNext()) {
                LocationVariable originalParamVar = it1.next();
                LocationVariable paramVar = it2.next();
                assert originalParamVar.sort().equals(paramVar.sort());
                result.put(originalParamVar, paramVar);
            }
        }
        // result
        if (resultVar != null && vars.result != null) {
            assert vars.result.sort().equals(resultVar.sort());
            result.put(vars.result, resultVar);
        }
        // exception
        if (excVar != null && vars.exception != null) {
            assert vars.exception.sort().equals(excVar.sort());
            result.put(vars.exception, excVar);
        }
        if (atPreVars != null && vars.atPres != null && !atPreVars.isEmpty()
                && !vars.atPres.isEmpty()) {
            for (LocationVariable h : heaps) {
                if (atPreVars.get(h) != null && vars.atPres.get(h) != null) {
                    assert vars.atPres.get(h).sort().equals(atPreVars.get(h).sort());
                    result.put(vars.atPres.get(h), atPreVars.get(h));
                }
            }
        }
        return result;
    }

    /**
     * Splits a (specification) term into implicit and explicit parts (i.e. as written in the
     * specification) and reforms the conjunction in a sorted way, where implicit parts appear
     * first, and also labeled with the short-circuit term label.
     *
     * @param spec specification term
     * @return sorted and short-circuit conjuncted specification term
     */
    private Condition split(JTerm spec) {
        Pair<ImmutableList<JTerm>, ImmutableList<JTerm>> p = sort(spec);
        ImmutableList<JTerm> implicit = p.first;
        ImmutableList<JTerm> explicit = p.second;
        return new Condition(TB.andSC(implicit), TB.andSC(explicit));
    }

    private Condition replace(Condition pre, OriginalVariables newVars) {
        final JTerm implicit = replace(pre.implicit, newVars);
        final JTerm explicit = replace(pre.explicit, newVars);
        return new Condition(implicit, explicit);
    }

    private Condition replace(Condition pre, Variables vars) {
        final JTerm implicit = replace(pre.implicit, vars);
        final JTerm explicit = replace(pre.explicit, vars);
        return new Condition(implicit, explicit);
    }

    private ImmutableList<JTerm> replace(Iterable<JTerm> l, Variables vars) {
        ImmutableList<JTerm> res = ImmutableSLList.nil();
        for (JTerm t : l) {
            res = res.append(replace(t, vars));
        }
        return res;
    }

    private ImmutableList<LocationVariable> getHeaps() {
        ImmutableList<LocationVariable> result = ImmutableSLList.nil();
        return result.append(getHeap());
    }

    private String typeString() {
        return type().toString().toLowerCase().replace("_", " ");
    }

    /**
     * Return String to display contract in proof management dialog
     *
     * @param includeHtmlMarkup
     * @param services
     * @return String to display
     */
    private String getText(boolean includeHtmlMarkup, Services services) {
        final StringBuilder sig = new StringBuilder();
        OriginalVariables origVars = getOrigVars();
        if (origVars.result != null) {
            sig.append(origVars.result);
            sig.append(" = ");
        } else if (isConstructor()) {
            sig.append(origVars.self);
            sig.append(" = new ");
        }
        if (!target.isStatic() && !isConstructor()) {
            sig.append(origVars.self);
            sig.append(".");
        }
        sig.append(target instanceof IProgramMethod ? ((IProgramMethod) target).getName() : "");
        sig.append("(");
        for (ProgramVariable pv : origVars.params) {
            sig.append(pv.name()).append(", ");
        }
        if (!origVars.params.isEmpty()) {
            sig.setLength(sig.length() - 2);
        }
        sig.append(")");
        if (!modelField() && !(type().equals(Type.OPERATION_CONTRACT)
                && ((MethodWellDefinedness) this).isModel())) {
            sig.append(" catch(");
            sig.append(origVars.exception);
            sig.append(")");
        }
        final String printMby = hasMby() ? LogicPrinter.quickPrintTerm(this.mby, services) : null;
        String mby = "";
        if (printMby != null) {
            mby = mby + (includeHtmlMarkup ? "<br><b>" : "\n") + "measured-by"
                + (includeHtmlMarkup ? "</b> " : ": ")
                + (includeHtmlMarkup ? LogicPrinter.escapeHTML(printMby, false) : printMby.trim());
        }
        String modifiables = "";
        final boolean isInv = type().equals(Type.CLASS_INVARIANT);
        final boolean isLoop = type().equals(Type.LOOP_INVARIANT);
        final boolean showSig = !isInv && !modelField();
        if (getModifiable() != null && showSig) {
            String printModifiables = LogicPrinter.quickPrintTerm(
                getModifiable(null).equalsModProperty(TB.strictlyNothing(),
                    IRRELEVANT_TERM_LABELS_PROPERTY) ? TB.empty()
                            : this.getModifiable(null),
                services);
            modifiables += (includeHtmlMarkup ? "<br><b>" : "\n") + "modifiable"
                + (includeHtmlMarkup ? "</b> " : ": ")
                + (includeHtmlMarkup ? LogicPrinter.escapeHTML(printModifiables, false)
                        : printModifiables.trim());
        }
        if (getModifiable() != null && getModifiable().equals(TB.strictlyNothing()) && showSig) {
            modifiables +=
                (includeHtmlMarkup ? "<b>" : "") + ", creates no new objects"
                    + (includeHtmlMarkup ? "</b>" : "");
        }
        String globalUpdates = "";
        if (getGlobalDefs() != null) {
            final String printUpdates = LogicPrinter.quickPrintTerm(getGlobalDefs(), services);
            globalUpdates = (includeHtmlMarkup ? "<br><b>" : "\n") + "defs"
                + (includeHtmlMarkup ? "</b> " : ": ")
                + (includeHtmlMarkup ? LogicPrinter.escapeHTML(printUpdates, false)
                        : printUpdates);
        }
        String pres = "";
        if (getRequires(null) != null) {
            String printPres = LogicPrinter.quickPrintTerm(getRequires(null), services);
            pres += (includeHtmlMarkup ? "<br><b>" : "\n")
                    + ((!isInv && !isLoop) ? "pre" : "inv") + (includeHtmlMarkup ? "</b> " : ": ")
                    + (includeHtmlMarkup ? LogicPrinter.escapeHTML(printPres, false)
                            : printPres);
        }
        String deps = "";
        if (getAccessible() != null) {
            String printDeps = LogicPrinter.quickPrintTerm(getAccessible(), services);
            deps += (includeHtmlMarkup ? "<br><b>" : "\n") + "dep"
                + (includeHtmlMarkup ? "</b> " : ": ")
                + (includeHtmlMarkup ? LogicPrinter.escapeHTML(printDeps, false)
                        : printDeps);
        }
        String reps = "";
        if (getRepresents() != null) {
            String printReps = LogicPrinter.quickPrintTerm(getRepresents(), services);
            reps += (includeHtmlMarkup ? "<br><b>" : "\n") + "rep"
                + (includeHtmlMarkup ? "</b> " : ": ")
                + (includeHtmlMarkup ? LogicPrinter.escapeHTML(printReps, false)
                        : printReps);
        }
        String posts = "";
        if (getEnsures(null) != null && showSig && !isLoop) {
            String printPosts = LogicPrinter.quickPrintTerm(getEnsures(null), services);
            posts += (includeHtmlMarkup ? "<br><b>" : "\n") + "post"
                + (includeHtmlMarkup ? "</b> " : ": ")
                + (includeHtmlMarkup ? LogicPrinter.escapeHTML(printPosts, false)
                        : printPosts);
        }
        String axioms = "";
        if (getAxiom() != null) {
            String printAxioms = LogicPrinter.quickPrintTerm(getAxiom(), services);
            axioms += (includeHtmlMarkup ? "<br><b>" : "\n") + "axiom"
                + (includeHtmlMarkup ? "</b> " : ": ")
                + (includeHtmlMarkup ? LogicPrinter.escapeHTML(printAxioms, false)
                        : printAxioms);
        }
        String transactionApplicable = "";
        if (transactionApplicableContract()) {
            transactionApplicable = (includeHtmlMarkup ? "<br><b>" : "\n")
                + "transaction applicable" + (includeHtmlMarkup ? "</b> " : ":");
        }
        if (includeHtmlMarkup) {
            return "<html>"
                + (showSig ? ("<i>" + LogicPrinter.escapeHTML(sig.toString(), false) + "</i>") : "")
                + globalUpdates + pres + deps + reps + posts + axioms + modifiables + mby
                + transactionApplicable + "</html>";
        } else {
            return (showSig ? sig.toString() : "") + globalUpdates + pres + deps + reps + posts
                    + axioms + modifiables + mby + transactionApplicable;
        }
    }

    /**
     * Non-helper constructor methods cannot assume the free precondition, but establish it.
     *
     * @param pre specified precondition
     * @param self self variable
     * @param heap heap variable
     * @param services
     * @return specified precondition appended with free precondition
     */
    private JTerm appendFreePre(JTerm pre, ProgramVariable self, ProgramVariable heap,
            TermServices services) {
        final IObserverFunction target = getTarget();
        final KeYJavaType selfKJT = target.getContainerType();
        final JTerm notNull =
            target.isStatic() ? TB.tt() : TB.not(TB.equals(TB.var(self), TB.NULL()));
        final JTerm created = TB.created(TB.var(heap), TB.var(self));
        final JTerm selfExactType = TB.exactInstance(selfKJT.getSort(), TB.var(self));
        return TB.andSC(pre, notNull, created, selfExactType);
    }

    /**
     * Generates the general assumption that self is not null.
     *
     * @param selfVar The self variable.
     * @return The term representing the general assumption.
     */
    private JTerm generateSelfNotNull(JAbstractSortedOperator selfVar) {
        return selfVar == null || isConstructor() ? TB.tt()
                : TB.not(TB.equals(TB.tf().createTerm(selfVar), TB.NULL()));
    }

    /**
     * Generates the general assumption that self is created.
     *
     * @param selfVar The self variable.
     * @return The term representing the general assumption.
     */
    private JTerm generateSelfCreated(JAbstractSortedOperator selfVar,
            JAbstractSortedOperator heap) {
        if (selfVar == null || isConstructor()) {
            return TB.tt();
        } else {
            return TB.created(TB.tf().createTerm(heap), TB.tf().createTerm(selfVar));
        }
    }


    /**
     * Generates the general assumption which defines the type of self.
     *
     * @param selfVar The self variable.
     * @return The term representing the general assumption.
     */
    private JTerm generateSelfExactType(JAbstractSortedOperator selfVar) {
        return selfVar == null || isConstructor() ? TB.tt()
                : TB.exactInstance(getKJT().getSort(), TB.tf().createTerm(selfVar));
    }

    /**
     * Generates the general assumption that all parameter arguments are valid.
     *
     * @param paramVars The parameters {@link LocationVariable}s.
     * @return The term representing the general assumption.
     */
    private JTerm generateParamsOK(ImmutableList<? extends JAbstractSortedOperator> paramVars) {
        JTerm paramsOK = TB.tt();
        if (paramVars.size() == getOrigVars().params.size()) {
            final Iterator<LocationVariable> origParams = getOrigVars().params.iterator();
            for (JAbstractSortedOperator paramVar : paramVars) {
                assert origParams.hasNext();
                paramsOK = TB.and(paramsOK,
                    TB.reachableValue(TB.tf().createTerm(paramVar),
                        origParams.next().getKeYJavaType()));
            }
        } else {
            throw new RuntimeException("Unequal number of params!");
            /*
             * for (AbstractSortedOperator paramVar : paramVars) {
             * paramsOK =
             * TB.and(paramsOK,
             * TB.reachableValue(TB.var(paramVar), paramVar.getKeYJavaType()));
             * }
             */
        }
        return paramsOK;
    }

    /**
     * Builds the "general assumption"
     *
     * @param implicitPre the implicit precondition
     * @param self self variable
     * @param heap heap variable
     * @param params list of parameter variables
     * @param services
     * @return The {@link JTerm} containing the general assumptions.
     */
    private TermListAndFunc buildFreePre(JTerm implicitPre, LocationVariable self,
            LocationVariable heap, ImmutableList<LocationVariable> params,
            Services services) {
        ImmutableList<JTerm> resList = ImmutableSLList.nil();

        // "self != null"
        final JTerm selfNotNull = generateSelfNotNull(self);

        // "self.<created> = TRUE"
        final JTerm selfCreated = generateSelfCreated(self, heap);

        // "MyClass::exactInstance(self) = TRUE"
        final JTerm selfExactType = generateSelfExactType(self);

        // conjunction of...
        // - "p_i = null | p_i.<created> = TRUE" for object parameters, and
        // - "inBounds(p_i)" for integer parameters
        final JTerm paramsOK = generateParamsOK(params);

        // initial value of measured_by clause
        final Function mbyAtPreFunc = generateMbyAtPreFunc(services);
        final JTerm mbyAtPreDef;
        if (type().equals(Type.OPERATION_CONTRACT)) {
            MethodWellDefinedness mwd = (MethodWellDefinedness) this;
            mbyAtPreDef = mwd.generateMbyAtPreDef(self, params, mbyAtPreFunc, services);
        } else {
            mbyAtPreDef = TB.tt();
        }

        final JTerm wellFormed = TB.wellFormed(TB.var(heap));

        final JTerm invTerm = self != null && this instanceof ClassWellDefinedness
                ? TB.inv(new JTerm[] { TB.var(heap) }, TB.var(self))
                : TB.tt();

        final JTerm[] result =
            { wellFormed, selfNotNull, selfCreated, selfExactType, invTerm,
                paramsOK, implicitPre, mbyAtPreDef };

        for (JTerm t : result) {
            resList = resList.append(t);
        }
        return new TermListAndFunc(resList, mbyAtPreFunc);
    }

    /**
     * Builds the "general assumption"
     *
     * @param implicitPre the implicit precondition
     * @param self self variable
     * @param heap heap variable
     * @param params list of parameter variables
     * @param services
     * @return The {@link JTerm} containing the general assumptions.
     */
    private TermListAndFunc buildFreePreForTaclet(JTerm implicitPre, TermSV self,
            TermSV heap, ImmutableList<JOperatorSV> params,
            Services services) {
        ImmutableList<JTerm> resList = ImmutableSLList.nil();

        // "self != null"
        final JTerm selfNotNull = generateSelfNotNull(self);

        // "self.<created> = TRUE"
        final JTerm selfCreated = generateSelfCreated(self, heap);

        // "MyClass::exactInstance(self) = TRUE"
        final JTerm selfExactType = generateSelfExactType(self);

        // conjunction of...
        // - "p_i = null | p_i.<created> = TRUE" for object parameters, and
        // - "inBounds(p_i)" for integer parameters
        final JTerm paramsOK = generateParamsOK(params);

        // initial value of measured_by clause
        final Function mbyAtPreFunc = generateMbyAtPreFunc(services);

        final JTerm wellFormed = TB.wellFormed(TB.var(heap));

        final JTerm[] result;
        result = new JTerm[] { wellFormed, paramsOK, implicitPre };

        for (JTerm t : result) {
            resList = resList.append(t);
        }
        return new TermListAndFunc(resList, mbyAtPreFunc);
    }

    /**
     * Conjoins two well-definedness taclets for pure method invocations
     *
     * @param name taclet name
     * @param find1 first find term
     * @param find2 second find term
     * @param goal1 first precondition
     * @param goal2 second precondition
     * @param services
     * @return conjoined taclet
     */
    static RewriteTaclet createTaclet(String name, JTerm find1, JTerm find2, JTerm goal1,
            JTerm goal2, TermServices services) {
        assert find1.op().name().equals(TermBuilder.WD_ANY.name());
        assert find2.op().name().equals(TermBuilder.WD_ANY.name());
        assert find1.sub(0).op().name().equals(find2.sub(0).op().name());
        assert find1.sub(0).arity() == find2.sub(0).arity();

        Map<Operator, Operator> map = new LinkedHashMap<>();
        int i = 0;
        for (JTerm sub : find1.sub(0).subs()) {
            map.put(find2.sub(0).sub(i).op(), sub.op());
            i++;
        }
        final OpReplacer or = new OpReplacer(map, services.getTermFactory());
        final JTerm goal = services.getTermBuilder().orSC(goal1, or.replace(goal2));
        final RewriteTacletBuilder<RewriteTaclet> tb = new RewriteTacletBuilder<>();
        tb.setFind(find1);
        tb.setName(MiscTools.toValidTacletName(name));
        tb.addRuleSet(new RuleSet(new Name("simplify")));
        tb.addGoalTerm(goal);
        return tb.getTaclet();
    }

    /**
     * Creates new well-definedness taclet for either an invariant reference or a pure method
     * invocation.
     *
     * @param name taclet name
     * @param callee the receiver variable as a term
     * @param callTerm the whole invocation term
     * @param pre the method's or invariant's precondition
     * @param isStatic a boolean to tell if the method is static
     * @param services
     * @return created taclet
     */
    static RewriteTaclet createTaclet(String name, JTerm callee, JTerm callTerm, JTerm pre,
            boolean isStatic, TermServices services) {
        final TermBuilder TB = services.getTermBuilder();
        final RewriteTacletBuilder<RewriteTaclet> tb = new RewriteTacletBuilder<>();
        final JTerm notNull = isStatic ? TB.tt() : TB.not(TB.equals(callee, TB.NULL()));
        final JTerm created = isStatic ? TB.tt() : TB.created(callee);
        tb.setFind(TB.wd(callTerm));
        tb.setName(MiscTools.toValidTacletName(name));
        tb.addRuleSet(new RuleSet(new Name("simplify")));
        tb.addGoalTerm(TB.andSC(notNull, created, pre));
        return tb.getTaclet();
    }

    /**
     * Creates new well-definedness taclet for a pure method invocation, which can potentially throw
     * an exception.
     *
     * @param name taclet name
     * @param callTerm the whole invocation term
     * @param services
     * @return created taclet with false as replacewith term
     */
    static RewriteTaclet createExcTaclet(String name, JTerm callTerm, TermServices services) {
        final TermBuilder TB = services.getTermBuilder();
        final RewriteTacletBuilder<RewriteTaclet> tb = new RewriteTacletBuilder<>();
        tb.setFind(TB.wd(callTerm));
        tb.setName(MiscTools.toValidTacletName(name));
        tb.addRuleSet(new RuleSet(new Name("simplify")));
        tb.addGoalTerm(TB.ff());
        return tb.getTaclet();
    }

    abstract Function generateMbyAtPreFunc(Services services);

    final JTerm replace(JTerm t, OriginalVariables newVars) {
        return replace(t, newVars.self, newVars.result, newVars.exception, newVars.atPres,
            newVars.params, getOrigVars(), getHeaps());
    }

    final Condition replaceSV(Condition pre, JOperatorSV self,
            ImmutableList<JOperatorSV> params) {
        final JTerm implicit = replaceSV(pre.implicit, self, params);
        final JTerm explicit = replaceSV(pre.explicit, self, params);
        return new Condition(implicit, explicit);
    }

    final void setMby(JTerm mby) {
        this.mby = mby;
    }

    final void addRequires(Condition req) {
        final Condition oldRequires = getRequires();
        this.requires = new Condition(TB.andSC(req.implicit, oldRequires.implicit),
            TB.andSC(req.explicit, oldRequires.explicit));
    }

    final void addRequires(JTerm req) {
        Condition requires = split(req);
        addRequires(requires);
    }

    final void setRequires(JTerm req) {
        this.requires = split(req);
    }

    final void setModifiable(JTerm modifiables, TermServices services) {
        this.modifiable = modifiables;
        if (modifiables == null
                || TB.strictlyNothing().equalsModProperty(
                    modifiables, IRRELEVANT_TERM_LABELS_PROPERTY)
                || TB.FALSE().equalsModProperty(
                    modifiables, IRRELEVANT_TERM_LABELS_PROPERTY)) {
            this.modifiable = TB.strictlyNothing();
        } else if (TB.tt().equalsModProperty(
            modifiables, IRRELEVANT_TERM_LABELS_PROPERTY)
                || TB.TRUE().equalsModProperty(
                    modifiables, IRRELEVANT_TERM_LABELS_PROPERTY)) {
            this.modifiable = TB.allLocs();
        }
    }

    final void combineModifiable(JTerm modifiables1, JTerm modifiables2,
            TermServices services) {
        if (modifiables1 == null || TB.strictlyNothing().equalsModProperty(
            modifiables1, IRRELEVANT_TERM_LABELS_PROPERTY)) {
            setModifiable(modifiables2, services);
        } else if (modifiables2 == null || TB.strictlyNothing().equalsModProperty(
            modifiables2, IRRELEVANT_TERM_LABELS_PROPERTY)) {
            setModifiable(modifiables1, services);
        } else {
            setModifiable(TB.union(modifiables1, modifiables2), services);
        }
    }

    final void setAccessible(JTerm acc) {
        this.accessible = acc;
    }

    final void combineAccessible(JTerm acc, JTerm accPre, TermServices services) {
        if (acc == null && accPre == null) {
            setAccessible(null);
        } else if (accPre == null || accPre.equals(acc)) {
            setAccessible(acc);
        } else if (acc == null) {
            setAccessible(accPre);
        } else if (acc.equals(TB.allLocs()) || accPre.equals(TB.allLocs())) {
            // This case is necessary since KeY defaults most method contracts with allLocs
            final JTerm allLocs = TB.allLocs();
            if (acc.equals(allLocs)) {
                setAccessible(accPre);
            } else if (accPre.equals(allLocs)) {
                setAccessible(acc);
            }
        } else {
            setAccessible(TB.union(acc, accPre));
        }
    }

    final void addEnsures(Condition ens) {
        final Condition oldEnsures = getEnsures();
        this.ensures = new Condition(TB.andSC(ens.implicit, oldEnsures.implicit),
            TB.andSC(ens.explicit, oldEnsures.explicit));
    }

    final void addEnsures(JTerm ens) {
        Condition ensures = split(ens);
        addEnsures(ensures);
    }

    final void setEnsures(JTerm ens) {
        this.ensures = split(ens);
    }

    final Type type() {
        return this.type;
    }

    /**
     * Collects all remaining (implicitly or explicitly) specified clauses (except for
     * pre-condition, post-condition and modifiable-clause).
     *
     * @return a list of all remaining clauses
     */
    ImmutableList<JTerm> getRest() {
        ImmutableList<JTerm> rest = ImmutableSLList.nil();
        final JTerm accessible = this.accessible;
        if (accessible != null) {
            rest = rest.append(accessible);
        }
        final JTerm mby = this.mby;
        if (mby != null) {
            rest = rest.append(mby);
        }
        final JTerm represents = this.represents;
        if (represents != null) {
            rest = rest.append(represents);
        }
        return rest;
    }

    // -------------------------------------------------------------------------
    // Public Interface
    // -------------------------------------------------------------------------

    @Override
    public abstract WellDefinednessCheck map(UnaryOperator<JTerm> op, Services services);

    /**
     * Detects the specification element's behaviour
     *
     * @return behaviour string
     */
    public abstract String getBehaviour();

    /**
     * Detects if the specification element is a true (i.e. not an invariant) model field
     *
     * @return true for model fields
     */
    public abstract boolean modelField();

    /**
     * Only for contracts with model_behaviour, the result is different from null.
     *
     * @return the return value of a model method (null otherwise)
     */
    public abstract JTerm getAxiom();

    /**
     * Combines two well-definedness checks having the same name, id, target, type, behaviour and
     * are either both model fields or both not a model field.
     *
     * @param wdc the well-definedness check to be combined with the current one
     * @param services
     * @return the combined well-definedness contract
     */
    public WellDefinednessCheck combine(WellDefinednessCheck wdc, TermServices services) {
        assert this.getName().equals(wdc.getName());
        assert this.id() == wdc.id();
        assert this.getTarget().equals(wdc.getTarget());
        assert this.type().equals(wdc.type());
        assert this.modelField() == wdc.modelField();
        assert this.getBehaviour().equals(wdc.getBehaviour());

        if (this.getAccessible() != null && wdc.getAccessible() != null) {
            final JTerm acc = wdc.replace(wdc.getAccessible(), this.getOrigVars());
            combineAccessible(acc, this.getAccessible(), services);
        } else if (wdc.getAccessible() != null) {
            final JTerm acc = wdc.replace(wdc.getAccessible(), this.getOrigVars());
            setAccessible(acc);
        }
        if (this.getModifiable() != null && wdc.getModifiable() != null) {
            final JTerm ass = wdc.replace(wdc.getModifiable(), this.getOrigVars());
            combineModifiable(ass, this.getModifiable(), services);
        } else if (wdc.getModifiable() != null) {
            final JTerm ass = wdc.replace(wdc.getModifiable(), this.getOrigVars());
            setModifiable(ass, services);
        }
        final Condition ens = wdc.replace(wdc.getEnsures(), this.getOrigVars());
        addEnsures(ens);
        final Condition req = wdc.replace(wdc.getRequires(), this.getOrigVars());
        addRequires(req);
        if (this.getRepresents() != null && wdc.getRepresents() != null) {
            final JTerm rep = wdc.replace(wdc.getRepresents(), this.getOrigVars());
            this.represents = TB.andSC(rep, getRepresents());
        } else if (wdc.getRepresents() != null) {
            final JTerm rep = wdc.replace(wdc.getRepresents(), this.getOrigVars());
            this.represents = rep;
        }
        if (this.hasMby() && wdc.hasMby()) {
            final JTerm mby = wdc.replace(wdc.getMby(), this.getOrigVars());
            setMby(TB.pair(mby, this.getMby()));
        } else if (wdc.hasMby()) {
            final JTerm mby = wdc.replace(wdc.getMby(), this.getOrigVars());
            setMby(mby);
        }
        return this;
    }

    /**
     * This method checks, if well-definedness checks are generally turned on or off.
     *
     * @return true if on and false if off
     */
    public static boolean isOn() {
        final String setting =
            ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().getDefaultChoices().get(OPTION);
        if (setting == null) {
            return false;
        }
        if (setting.equals(OPTION + ":on")) {
            return true;
        } else if (setting.equals(OPTION + ":off")) {
            return false;
        } else {
            throw new RuntimeException(
                "The setting for the wdProofs-option is not valid: " + setting);
        }
    }

    /**
     * collects terms for precondition, modifiable clause and other specification elements, and
     * postcondition and signals-clause
     */
    public final POTerms createPOTerms() {
        final Condition pre = this.getRequires();
        final JTerm modifiable = this.getModifiable();
        final ImmutableList<JTerm> rest = this.getRest();
        final Condition post = this.getEnsures();
        return new POTerms(pre, modifiable, rest, post);
    }

    public final WellDefinednessCheck addRepresents(JTerm rep) {
        assert rep != null;
        if (this.represents != null) {
            this.represents = TB.andSC(this.represents, rep);
        } else {
            this.represents = rep;
        }
        return this;
    }

    /**
     * Gets the full valid precondition, which holds in the element's pre-state.
     *
     * @param pre the precondition with the original variables
     * @param self the new self variable
     * @param heap the new heap variable
     * @param parameters the new parameter list
     * @param services
     * @return the full valid pre-condition assumed in the pre-state including the measured-by
     *         function
     */
    public final TermAndFunc getPre(final Condition pre, LocationVariable self,
            LocationVariable heap, ImmutableList<LocationVariable> parameters,
            Services services) {
        final IObserverFunction target = getTarget();
        final TermListAndFunc freePre =
            buildFreePre(pre.implicit, self, heap, parameters, services);
        final ImmutableList<JTerm> preTerms = freePre.terms.append(pre.explicit);
        JTerm res = TB.andSC(preTerms);
        if (target instanceof IProgramMethod && ((IProgramMethod) target).isConstructor()
                && !JMLInfoExtractor.isHelper((IProgramMethod) target)) {
            final JTerm constructorPre = appendFreePre(res, self, heap, services);
            return new TermAndFunc(constructorPre, freePre.func);
        } else {
            return new TermAndFunc(res, freePre.func);
        }
    }

    /**
     * Gets the full valid precondition, which holds in the element's pre-state.
     *
     * @param pre the precondition with the original variables
     * @param self the new self variable
     * @param heap the new heap variable
     * @param parameters the new parameter list
     * @param services
     * @return the full valid pre-condition assumed in the pre-state including the measured-by
     *         function
     */
    public final TermAndFunc getPreForTaclet(final Condition pre, TermSV self,
            TermSV heap, ImmutableList<JOperatorSV> parameters,
            Services services) {
        final TermListAndFunc freePre =
            buildFreePreForTaclet(pre.implicit, self, heap, parameters, services);
        final ImmutableList<JTerm> preTerms = freePre.terms.append(pre.explicit);

        return new TermAndFunc(TB.andSC(preTerms), freePre.func);
    }

    /**
     * Gets the full valid post-condition
     *
     * @param post post-condition with original variables
     * @param result the new result variable
     * @param services
     * @return the full valid post-condition
     */
    public final JTerm getPost(final Condition post, ProgramVariable result,
            TermServices services) {
        final JTerm reachable;
        if (result != null) {
            reachable = TB.reachableValue(TB.var(result), origVars.result.getKeYJavaType());
        } else {
            reachable = TB.tt();
        }
        return TB.andSC(reachable, post.implicit, post.explicit);
    }

    /**
     * Gets the necessary updates applicable to the post-condition
     *
     * @param modifiable the modifiable-clause
     * @param heap the current heap variable
     * @param heapAtPre the current variable for the heap of the pre-state
     * @param anonHeap the anonymous heap term
     * @param services
     * @return the applicable update term including an update for old-expressions and the
     *         anonymisation update
     */
    public final JTerm getUpdates(JTerm modifiable, LocationVariable heap,
            ProgramVariable heapAtPre,
            JTerm anonHeap, TermServices services) {
        assert modifiable != null;
        assert anonHeap != null
                || TB.strictlyNothing().equalsModProperty(modifiable,
                    IRRELEVANT_TERM_LABELS_PROPERTY);
        final JTerm havocUpd =
            TB.strictlyNothing().equalsModProperty(modifiable, IRRELEVANT_TERM_LABELS_PROPERTY)
                    ? TB.skip()
                    : TB.elementary(heap, TB.anon(TB.var(heap), modifiable, anonHeap));
        final JTerm oldUpd =
            heapAtPre != heap ? TB.elementary(TB.var(heapAtPre), TB.var(heap)) : TB.skip();
        return TB.parallel(oldUpd, havocUpd);
    }

    public final JTerm replace(JTerm t, Variables vars) {
        return replace(t, vars.self, vars.result, vars.exception, vars.atPres, vars.params,
            getOrigVars(), getHeaps());
    }

    public final POTerms replace(POTerms po, Variables vars) {
        final Condition pre = replace(po.pre, vars);
        final JTerm modifiable = replace(po.modifiable, vars);
        final ImmutableList<JTerm> rest = replace(po.rest, vars);
        final Condition post = replace(po.post, vars);
        return new POTerms(pre, modifiable, rest, post);
    }

    public final LocationVariable getHeap() {
        return this.heap;
    }

    public final Name name() {
        return new Name(getName());
    }

    public final Condition getRequires() {
        assert this.requires != null;
        return this.requires;
    }

    public final JTerm getModifiable() {
        assert this.modifiable != null;
        return this.modifiable;
    }

    public final JTerm getAccessible() {
        return this.accessible;
    }

    public final Condition getEnsures() {
        assert this.ensures != null;
        return this.ensures;
    }

    public final JTerm getEnsures(LocationVariable heap) {
        return TB.andSC(getEnsures().implicit, getEnsures().explicit);
    }

    public final JTerm getRepresents() {
        return this.represents;
    }

    public final boolean isConstructor() {
        IObserverFunction target = getTarget();
        return target instanceof IProgramMethod && ((IProgramMethod) target).isConstructor();
    }

    @Override
    public final String toString() {
        return getName();
    }

    @Override
    public final String getName() {
        return this.name;
    }

    @Override
    public final int id() {
        return id;
    }

    @Override
    public final JTerm getMby() {
        return this.mby;
    }

    @Override
    public final boolean hasMby() {
        return this.mby != null;
    }

    @Override
    public final JTerm getRequires(LocationVariable heap) {
        return TB.andSC(getRequires().implicit, getRequires().explicit);
    }

    @Override
    public final JTerm getModifiable(LocationVariable heap) {
        return getModifiable();
    }

    @Override
    public final JTerm getAccessible(LocationVariable heap) {
        return getAccessible();
    }

    @Override
    public final String getHTMLText(Services services) {
        return getText(true, services);
    }

    @Override
    public final String getPlainText(Services services) {
        return getText(false, services);
    }

    @Override
    public final String proofToString(Services services) {
        assert false;
        return null;
    }

    @Override
    public final IObserverFunction getTarget() {
        return this.target;
    }

    @Override
    public final ProofOblInput createProofObl(InitConfig initConfig, Contract contract) {
        return new WellDefinednessPO(initConfig, (WellDefinednessCheck) contract);
    }

    @Override
    public final ProofOblInput createProofObl(InitConfig initConfig, Contract contract,
            boolean addSymbolicExecutionLabel) {
        if (addSymbolicExecutionLabel) {
            throw new IllegalStateException("Symbolic Execution API is not supported.");
        } else {
            return createProofObl(initConfig, contract);
        }
    }

    @Override
    public final ContractPO createProofObl(InitConfig initConfig) {
        return (ContractPO) createProofObl(initConfig, this);
    }

    @Override
    public final ProofOblInput getProofObl(Services services) {
        return services.getSpecificationRepository().getPO(this);
    }

    @Override
    public final String getDisplayName() {
        String displayName = "Well-Definedness of JML ";
        if (modelField()) {
            displayName = displayName + "model field";
        } else {
            displayName = displayName + typeString();
        }
        if (!modelField() && !type().equals(Type.CLASS_INVARIANT)) {
            displayName = displayName + " " + id;
        }
        if (!getBehaviour().isEmpty()) {
            displayName = displayName + " (" + getBehaviour() + ")";
        }
        return displayName;
    }

    @Override
    public final boolean toBeSaved() {
        return false;
    }

    @Override
    public final boolean hasSelfVar() {
        return origVars.self != null;
    }

    @Override
    public final OriginalVariables getOrigVars() {
        return this.origVars;
    }

    @Override
    public final boolean equals(Object o) {
        if (!(o instanceof WellDefinednessCheck wd)
                || !wd.getKJT().equals(getKJT())) {
            return false;
        }
        return wd.getName().equals(this.name);
    }

    @Override
    public final int hashCode() {
        return this.name.hashCode();
    }

    @Override
    @Deprecated
    public final JTerm getPre(LocationVariable heap, LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars,
            Map<LocationVariable, LocationVariable> atPreVars, Services services)
            throws UnsupportedOperationException {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Override
    @Deprecated
    public final JTerm getPre(List<LocationVariable> heapContext, LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars,
            Map<LocationVariable, LocationVariable> atPreVars, Services services)
            throws UnsupportedOperationException {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Override
    @Deprecated
    public final JTerm getPre(LocationVariable heap, JTerm heapTerm, JTerm selfTerm,
            ImmutableList<JTerm> paramTerms, Map<LocationVariable, JTerm> atPres, Services services)
            throws UnsupportedOperationException {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Override
    @Deprecated
    public final JTerm getPre(List<LocationVariable> heapContext,
            Map<LocationVariable, JTerm> heapTerms, JTerm selfTerm, ImmutableList<JTerm> paramTerms,
            Map<LocationVariable, JTerm> atPres, Services services)
            throws UnsupportedOperationException {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Override
    @Deprecated
    public final JTerm getDep(LocationVariable heap, boolean atPre, LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars,
            Map<LocationVariable, LocationVariable> atPreVars, Services services) {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Override
    @Deprecated
    public final JTerm getDep(LocationVariable heap, boolean atPre, JTerm heapTerm, JTerm selfTerm,
            ImmutableList<JTerm> paramTerms, Map<LocationVariable, JTerm> atPres,
            Services services) {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Override
    @Deprecated
    public final JTerm getGlobalDefs(LocationVariable heap, JTerm heapTerm, JTerm selfTerm,
            ImmutableList<JTerm> paramTerms, Services services) {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Override
    @Deprecated
    public final JTerm getMby(LocationVariable selfVar, ImmutableList<LocationVariable> paramVars,
            Services services) throws UnsupportedOperationException {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Override
    @Deprecated
    public final JTerm getMby(Map<LocationVariable, JTerm> heapTerms, JTerm selfTerm,
            ImmutableList<JTerm> paramTerms, Map<LocationVariable, JTerm> atPres, Services services)
            throws UnsupportedOperationException {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    /**
     * A static data structure for passing a term list with a function.
     *
     * @author Michael Kirsten
     */
    private final static class TermListAndFunc {
        private final ImmutableList<JTerm> terms;
        private final Function func;


        private TermListAndFunc(ImmutableList<JTerm> ts, Function f) {
            this.terms = ts;
            this.func = f;
        }
    }

    /**
     * A static data structure for storing and passing two terms, denoting the implicit and the
     * explicit part of a pre- or post-condition.
     *
     * @author Michael Kirsten
     */
    public record Condition(JTerm implicit, JTerm explicit) {

        /**
         * Applies a unary operator to every term in this object.
         *
         * @param op the operator to apply.
         * @return this object with the operator applied.
         */
        Condition map(UnaryOperator<JTerm> op) {
            return new Condition(op.apply(implicit), op.apply(explicit));
        }
    }

    /**
     * A static data structure for passing a term with a function.
     *
     * @author Michael Kirsten
     */
    public record TermAndFunc(JTerm term, Function func) {
    }

    /**
     * A data structure for storing and passing all specifications of a specification element
     * including pre- and post-condition, a modifiable-clause and a list of all other clauses
     * specified.
     *
     * @author Michael Kirsten
     */
    public record POTerms(Condition pre, JTerm modifiable, ImmutableList<JTerm> rest,
            Condition post) {
    }
}
