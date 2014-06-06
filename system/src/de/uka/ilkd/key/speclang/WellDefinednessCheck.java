// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.speclang;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.init.WellDefinednessPO;
import de.uka.ilkd.key.proof.init.WellDefinednessPO.Variables;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.speclang.jml.JMLInfoExtractor;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;

/**
 * A contract for checking the well-definedness of a jml specification element
 * (i.e. a class invariant, a method contract, a model field or any jml statement),
 * consisting of precondition, assignable-clause, postcondition, accessible-clause,
 * measured-by-clause and represents-clause.
 *
 * @author Michael Kirsten
 */
public abstract class WellDefinednessCheck implements Contract {

    private static final String OPTION = "wdChecks";
    public static final String INV_TACLET = "wd_Invariant";
    public static final String OP_TACLET = "wd_Operation";
    public static final String OP_EXC_TACLET = "wd_Exc_Operation";

    static enum Type {
        CLASS_INVARIANT, OPERATION_CONTRACT, LOOP_INVARIANT, BLOCK_CONTRACT
    }

    private final String name;
    private final int id;
    private final Type type;
    private IObserverFunction target;
    private final LocationVariable heap;
    private final OriginalVariables origVars;

    private Condition requires;
    private Term assignable;
    private Condition ensures;
    private Term accessible;
    private Term mby;
    private Term represents;
    
    final TermBuilder TB;

    WellDefinednessCheck(String name, int id, IObserverFunction target,
                         OriginalVariables origVars, Type type, Services services) {
        this.id = id;
        this.name = name +" WD." + id;
        this.type = type;
        this.target = target;
        this.heap = services.getTypeConverter().getHeapLDT().getHeap();
        this.origVars = origVars;
        this.TB = services.getTermBuilder();
    }

    WellDefinednessCheck(String name, int id, Type type, IObserverFunction target,
                         LocationVariable heap, OriginalVariables origVars,
                         Condition requires, Term assignable, Term accessible,
                         Condition ensures, Term mby, Term represents, TermBuilder tb) {
        this.name = name;
        this.id = id;
        this.type = type;
        this.target = target;
        this.heap = heap;
        this.origVars = origVars;
        this.requires = requires;
        this.assignable = assignable;
        this.accessible = accessible;
        this.ensures = ensures;
        this.mby = mby;
        this.represents = represents;
        this.TB = tb;
    }

    //-------------------------------------------------------------------------
    // Internal Methods
    //-------------------------------------------------------------------------

    /**
     * Splits and sorts a (specification) term in such a way that implicit parts are in the
     * first and explicit parts in the second list.
     * @param spec specification term
     * @return two lists for implicit and explicit specification parts
     */
    private Pair<ImmutableList<Term>, ImmutableList<Term>> sort(Term spec) {
        assert spec != null;
        ImmutableList<Term> implicit = ImmutableSLList.<Term>nil();
        ImmutableList<Term> explicit = ImmutableSLList.<Term>nil();
        if (spec.arity() > 0
                && spec.op().equals(Junctor.AND)) { // Conjunctions
            assert spec.arity() == 2;
            if (spec.hasLabels()
                    && spec.containsLabel(ParameterlessTermLabel.SHORTCUT_EVALUATION_LABEL)) {
                // Specification conjuncted with short-circuit operator
                for (Term sub: spec.subs()) {
                    if(sub.hasLabels() // Found implicit subterms
                            && sub.containsLabel(
                                    ParameterlessTermLabel.IMPLICIT_SPECIFICATION_LABEL)) {
                        final Pair<ImmutableList<Term>, ImmutableList<Term>> p = sort(sub);
                        implicit = implicit.append(p.first).append(p.second);
                    } else { // Subterm not labeled as implicit
                        final Pair<ImmutableList<Term>, ImmutableList<Term>> p = sort(sub);
                        implicit = implicit.append(p.first);
                        explicit = explicit.append(p.second);
                    }
                }
            } else { // Specification conjuncted with symmetric operator
                final Condition c1 = split(spec.sub(0));
                final Condition c2 = split(spec.sub(1));
                final Term a1 = TB.andSC(c1.implicit, c1.explicit);
                final Term a2 = TB.andSC(c2.implicit, c2.explicit);
                final Term a;
                if (a2.hasLabels()
                        && a2.containsLabel(ParameterlessTermLabel.IMPLICIT_SPECIFICATION_LABEL)) {
                    // Implicit term first
                    a = TB.and(a2, a1);
                } else {
                    a = TB.and(a1, a2);
                }
                if (spec.hasLabels()
                        && spec.containsLabel(ParameterlessTermLabel.IMPLICIT_SPECIFICATION_LABEL)) {
                    // Handled specification is already implicit
                    implicit = implicit.append(a);
                } else {
                    explicit = explicit.append(a);
                }
            }
        } else if (spec.arity() > 0
                && spec.op().equals(Junctor.IMP)) { // Implications
            assert spec.arity() == 2;
            final Condition c1 = split(spec.sub(0));
            final Condition c2 = split(spec.sub(1));
            final Term i1 = TB.andSC(c1.implicit, c1.explicit);
            final Term i2 = TB.andSC(c2.implicit, c2.explicit);
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
        return new Pair<ImmutableList<Term>, ImmutableList<Term>> (implicit, explicit);
    }

    private Term replaceSV(Term t, SchemaVariable self, ImmutableList<ParsableVariable> params) {
		return replaceSV(t, self, null, null, null, params, getOrigVars(), getHeaps());
    }

    private Term replaceSV(Term t,
						   SchemaVariable selfVar,
						   SchemaVariable resultVar,
						   SchemaVariable excVar,
						   Map<LocationVariable, SchemaVariable> atPreVars,
						   ImmutableList<ParsableVariable> paramVars,
						   OriginalVariables origVars,
						   ImmutableList<LocationVariable> heaps) {
        Map<ProgramVariable, SchemaVariable> map =
                getSchemaMap(selfVar, resultVar, excVar, atPreVars,
                        paramVars, origVars, heaps);
        final OpReplacer or = new OpReplacer(map, TB.tf());
        return or.replace(t);
    }

    private Term replace(Term t,
						 ProgramVariable selfVar,
						 ProgramVariable resultVar,
						 ProgramVariable excVar,
						 Map<LocationVariable, ProgramVariable> atPreVars,
						 ImmutableList<ProgramVariable> paramVars,
						 OriginalVariables origVars,
						 ImmutableList<LocationVariable> heaps) {
        Map<ProgramVariable, ProgramVariable> map =
                getReplaceMap(selfVar, resultVar, excVar, atPreVars,
                        paramVars, origVars, heaps);
        final OpReplacer or = new OpReplacer(map, TB.tf());
        return or.replace(t);
    }

    private static Map<ProgramVariable, SchemaVariable>
                                getSchemaMap(SchemaVariable selfVar,
                                             SchemaVariable resultVar,
                                             SchemaVariable excVar,
                                             Map<LocationVariable,
                                                 SchemaVariable> atPreVars,
                                             ImmutableList<ParsableVariable> paramVars,
                                             OriginalVariables vars,
                                             ImmutableList<LocationVariable> heaps) {
        final Map<ProgramVariable, SchemaVariable> result =
                new LinkedHashMap<ProgramVariable, SchemaVariable>();
        //self
        if(selfVar != null && vars.self != null) {
            assert selfVar.sort().extendsTrans(vars.self.sort());
            result.put(vars.self, selfVar);
        }
        //parameters
        if(paramVars != null && vars.params != null
                && !paramVars.isEmpty() && !vars.params.isEmpty()) {
            assert vars.params.size() == paramVars.size();
            final Iterator<ProgramVariable> it1 = vars.params.iterator();
            final Iterator<ParsableVariable> it2 = paramVars.iterator();
            while(it1.hasNext()) {
                ProgramVariable originalParamVar = it1.next();
                ParsableVariable paramVar          = it2.next();
                assert paramVar instanceof SchemaVariable;
                SchemaVariable paramSV = (SchemaVariable)paramVar;
                assert originalParamVar.sort().equals(paramSV.sort());
                result.put(originalParamVar, paramSV);
            }
        }
        //result
        if(resultVar != null && vars.result != null) {
            assert vars.result.sort().equals(resultVar.sort());
            result.put(vars.result, resultVar);
        }
        //exception
        if(excVar != null && vars.exception != null) {
            assert vars.exception.sort().equals(excVar.sort());
            result.put(vars.exception, excVar);
        }
        if(atPreVars != null && vars.atPres != null
                && !atPreVars.isEmpty() && !vars.atPres.isEmpty()) {
            for(LocationVariable h : heaps) {
                if(atPreVars.get(h) != null && vars.atPres.get(h) != null) {
                    assert vars.atPres.get(h).sort().equals(atPreVars.get(h).sort());
                    result.put(vars.atPres.get(h), atPreVars.get(h));
                }
            }
        }
        return result;
    }

    private static Map<ProgramVariable, ProgramVariable>
                                getReplaceMap(ProgramVariable selfVar,
                                              ProgramVariable resultVar,
                                              ProgramVariable excVar,
                                              Map<LocationVariable,
                                                  ProgramVariable> atPreVars,
                                              ImmutableList<ProgramVariable> paramVars,
                                              OriginalVariables vars,
                                              ImmutableList<LocationVariable> heaps) {
        final Map<ProgramVariable, ProgramVariable> result =
                new LinkedHashMap<ProgramVariable, ProgramVariable>();
        //self
        if(selfVar != null && vars.self != null) {
            assert vars.self.sort().extendsTrans(selfVar.sort())
                || selfVar.sort().extendsTrans(vars.self.sort());
            result.put(vars.self, selfVar);
        }
        //parameters
        if(paramVars != null && vars.params != null
                && !paramVars.isEmpty() && !vars.params.isEmpty()) {
            assert vars.params.size() == paramVars.size();
            final Iterator<ProgramVariable> it1 = vars.params.iterator();
            final Iterator<ProgramVariable> it2 = paramVars.iterator();
            while(it1.hasNext()) {
                ProgramVariable originalParamVar = it1.next();
                ProgramVariable paramVar         = it2.next();
                assert originalParamVar.sort().equals(paramVar.sort());
                result.put(originalParamVar, paramVar);
            }
        }
        //result
        if(resultVar != null && vars.result != null) {
            assert vars.result.sort().equals(resultVar.sort());
            result.put(vars.result, resultVar);
        }
        //exception
        if(excVar != null && vars.exception != null) {
            assert vars.exception.sort().equals(excVar.sort());
            result.put(vars.exception, excVar);
        }
        if(atPreVars != null && vars.atPres != null
                && !atPreVars.isEmpty() && !vars.atPres.isEmpty()) {
            for(LocationVariable h : heaps) {
                if(atPreVars.get(h) != null && vars.atPres.get(h) != null) {
                    assert vars.atPres.get(h).sort().equals(atPreVars.get(h).sort());
                    result.put(vars.atPres.get(h), atPreVars.get(h));
                }
            }
        }
        return result;
    }

    /**
     * Splits a (specification) term into implicit and explicit parts (i.e. as written
     * in the specification) and reforms the conjunction in a sorted way, where implicit
     * parts appear first, and also labeled with the short-circuit term label.
     * @param spec specification term
     * @return sorted and short-circuit conjuncted specification term
     */
    private Condition split(Term spec) {
        Pair<ImmutableList<Term>, ImmutableList<Term>> p = sort(spec);
        ImmutableList<Term> implicit = p.first;
        ImmutableList<Term> explicit   = p.second;
        return new Condition(TB.andSC(implicit), TB.andSC(explicit));
    }

    private Condition replace(Condition pre, OriginalVariables newVars) {
        final Term implicit = replace(pre.implicit, newVars);
        final Term explicit = replace(pre.explicit, newVars);
        return new Condition(implicit, explicit);
    }

    private Condition replace(Condition pre, Variables vars) {
        final Term implicit = replace(pre.implicit, vars);
        final Term explicit = replace(pre.explicit, vars);
        return new Condition(implicit, explicit);
    }

    private ImmutableList<Term> replace(Iterable<Term> l, Variables vars) {
        ImmutableList<Term> res = ImmutableSLList.<Term>nil();
        for (Term t: l) {
            res = res.append(replace(t, vars));
        }
        return res;
    }

    private ImmutableList<LocationVariable> getHeaps() {
        ImmutableList<LocationVariable> result =
                ImmutableSLList.<LocationVariable>nil();
        return result.append(getHeap());
    }

    private String typeString() {
        return type().toString().toLowerCase().replace("_", " ");
    }

    /**
     * Return String to display contract in proof management dialog
     * @param includeHtmlMarkup
     * @param services
     * @return String to display
     */
    private String getText(boolean includeHtmlMarkup, Services services) {
        final StringBuffer sig = new StringBuffer();
        OriginalVariables origVars = getOrigVars();
        if (origVars.result != null) {
            sig.append(origVars.result);
            sig.append(" = ");
        }
        else if (isConstructor()) {
            sig.append(origVars.self);
            sig.append(" = new ");
        }
        if (!target.isStatic() && !isConstructor()) {
            sig.append(origVars.self);
            sig.append(".");
        }
        sig.append(target instanceof IProgramMethod ?
                ((IProgramMethod)target).getName() : "");
        sig.append("(");
        for (ProgramVariable pv : origVars.params) {
            sig.append(pv.name()).append(", ");
        }
        if (!origVars.params.isEmpty()) {
            sig.setLength(sig.length() - 2);
        }
        sig.append(")");
        if(!modelField()
                && !(type().equals(Type.OPERATION_CONTRACT)
                        && ((MethodWellDefinedness)this).isModel())) {
            sig.append(" catch(");
            sig.append(origVars.exception);
            sig.append(")");
        }
        final String printMby = hasMby() ? LogicPrinter.quickPrintTerm(this.mby, services) : null;
        String mby = "";
        if (printMby != null) {
            mby = mby
                    + (includeHtmlMarkup ? "<br><b>" : "\n")
                    + "measured-by"
                    + (includeHtmlMarkup ? "</b> " : ": ")
                    + (includeHtmlMarkup ?
                            LogicPrinter.escapeHTML(printMby, false) : printMby.trim());
        }
        String mods = "";
        final boolean isInv = type().equals(Type.CLASS_INVARIANT);
        final boolean isLoop = type().equals(Type.LOOP_INVARIANT);
        final boolean showSig = !isInv && !modelField();
        if (getAssignable() != null && showSig) {
            String printMods =
                    LogicPrinter.quickPrintTerm(getAssignable(null).equals(TB.strictlyNothing()) ?
                                                    TB.empty() :
                                                        this.getAssignable(null),
                                                services);
            mods = mods
                    + (includeHtmlMarkup ? "<br><b>" : "\n")
                    + "mod"
                    + (includeHtmlMarkup ? "</b> " : ": ")
                    + (includeHtmlMarkup ?
                            LogicPrinter.escapeHTML(printMods, false) : printMods.trim());
        }
        if (getAssignable().equals(TB.strictlyNothing()) && showSig) {
            mods = mods +
                    (includeHtmlMarkup ? "<b>" : "") +
                    ", creates no new objects" +
                    (includeHtmlMarkup ? "</b>" : "");
        }
        String globalUpdates = "";
        if (getGlobalDefs() != null){
            final String printUpdates = LogicPrinter.quickPrintTerm(getGlobalDefs(), services);
            globalUpdates = (includeHtmlMarkup? "<br><b>": "\n")
                    + "defs" + (includeHtmlMarkup? "</b> " : ": ")
                    + (includeHtmlMarkup ? LogicPrinter.escapeHTML(printUpdates,false) : printUpdates.trim());
        }
        String pres = "";
        if (getRequires(null) != null) {
            String printPres = LogicPrinter.quickPrintTerm(getRequires(null), services);
            pres = pres
                    + (includeHtmlMarkup ? "<br><b>" : "\n")
                    + ((!isInv && !isLoop) ? "pre" : "inv")
                    + (includeHtmlMarkup ? "</b> " : ": ")
                    + (includeHtmlMarkup ?
                            LogicPrinter.escapeHTML(printPres, false) : printPres.trim());
        }
        String deps = "";
        if(getAccessible() != null) {
            String printDeps = LogicPrinter.quickPrintTerm(getAccessible(), services);
            deps = deps
                    + (includeHtmlMarkup ? "<br><b>" : "\n")
                    + "dep"
                    + (includeHtmlMarkup ? "</b> " : ": ")
                    + (includeHtmlMarkup ?
                            LogicPrinter.escapeHTML(printDeps, false) : printDeps.trim());
        }
        String reps = "";
        if(getRepresents() != null) {
            String printReps = LogicPrinter.quickPrintTerm(getRepresents(), services);
            reps = reps
                    + (includeHtmlMarkup ? "<br><b>" : "\n")
                    + "rep"
                    + (includeHtmlMarkup ? "</b> " : ": ")
                    + (includeHtmlMarkup ?
                            LogicPrinter.escapeHTML(printReps, false) : printReps.trim());
        }
        String posts = "";
        if (getEnsures(null) != null && showSig && !isLoop) {
            String printPosts = LogicPrinter.quickPrintTerm(getEnsures(null), services);
            posts = posts
                    + (includeHtmlMarkup ? "<br><b>" : "\n")
                    + "post"
                    + (includeHtmlMarkup ? "</b> " : ": ")
                    + (includeHtmlMarkup ? LogicPrinter.escapeHTML(printPosts, false)
                            : printPosts.trim());
        }
        String axioms = "";
        if (getAxiom() != null) {
            String printAxioms = LogicPrinter.quickPrintTerm(getAxiom(), services);
            axioms = axioms
                    + (includeHtmlMarkup ? "<br><b>" : "\n")
                    + "axiom"
                    + (includeHtmlMarkup ? "</b> " : ": ")
                    + (includeHtmlMarkup ?
                            LogicPrinter.escapeHTML(printAxioms, false) : printAxioms.trim());
        }
        String transactionApplicable = "";
        if (transactionApplicableContract()) {
            transactionApplicable = (includeHtmlMarkup ? "<br><b>" : "\n")
                    + "transaction applicable"
                    + (includeHtmlMarkup ? "</b> " : ":");
        }
        if (includeHtmlMarkup) {
            return "<html>"
                    + (showSig ?
                            ("<i>"
                                    + LogicPrinter.escapeHTML(sig.toString(), false)
                                    + "</i>")
                             : "")
                    + globalUpdates
                    + pres
                    + deps
                    + reps
                    + posts
                    + axioms
                    + mods
                    + mby
                    + transactionApplicable
                    + "</html>";
        } else {
            return (showSig ? sig.toString() : "")
                    + globalUpdates
                    + pres
                    + deps
                    + reps
                    + posts
                    + axioms
                    + mods
                    + mby
                    + transactionApplicable;
        }
    }

    /**
     * Non-helper constructor methods cannot assume the free precondition, but
     * establish it.
     * @param pre specified precondition
     * @param self self variable
     * @param heap heap variable
     * @param services
     * @return specified precondition appended with free precondition
     */
    private Term appendFreePre(Term pre,
                               ParsableVariable self,
                               ParsableVariable heap,
                               TermServices services) {
        final IObserverFunction target = getTarget();
        final KeYJavaType selfKJT = target.getContainerType();
        final Term notNull = target.isStatic() ?
                TB.tt() : TB.not(TB.equals(TB.var(self), TB.NULL()));
        final Term created = TB.created(TB.var(heap), TB.var(self));
        final Term selfExactType =
                TB.exactInstance(selfKJT.getSort(), TB.var(self));
        return TB.andSC(pre, notNull, created, selfExactType);
    }

    /**
     * Generates the general assumption that self is not null.
     * @param pm The {@link IProgramMethod} to execute.
     * @param selfVar The self variable.
     * @return The term representing the general assumption.
     */
    private Term generateSelfNotNull(ParsableVariable selfVar) {
        return selfVar == null || isConstructor() ?
                TB.tt() : TB.not(TB.equals(TB.var(selfVar), TB.NULL()));
    }

    /**
     * Generates the general assumption that self is created.
     * @param pm The {@link IProgramMethod} to execute.
     * @param selfVar The self variable.
     * @return The term representing the general assumption.
     */
    private Term generateSelfCreated(ParsableVariable selfVar, ParsableVariable heap) {
        if(selfVar == null || isConstructor()) {
            return TB.tt();
        } else {
            return TB.created(TB.var(heap), TB.var(selfVar));
        }
    }


    /**
     * Generates the general assumption which defines the type of self.
     * @param pm The {@link IProgramMethod} to execute.
     * @param selfVar The self variable.
     * @param selfKJT The {@link KeYJavaType} of the self variable.
     * @return The term representing the general assumption.
     */
    private Term generateSelfExactType(ParsableVariable selfVar) {
        return selfVar == null || isConstructor() ? TB.tt() :
            TB.exactInstance(getKJT().getSort(), TB.var(selfVar));
    }

    /**
     * Generates the general assumption that all parameter arguments are valid.
     * @param paramVars The parameters {@link ProgramVariable}s.
     * @return The term representing the general assumption.
     */
    private Term generateParamsOK(ImmutableList<ParsableVariable> paramVars) {
        Term paramsOK = TB.tt();
        if (paramVars.size() == getOrigVars().params.size()) {
            final Iterator<ProgramVariable> origParams = getOrigVars().params.iterator();
            for (ParsableVariable paramVar : paramVars) {
                assert origParams.hasNext();
                paramsOK = TB.and(paramsOK,
                                  TB.reachableValue(TB.var(paramVar),
													origParams.next().getKeYJavaType()));
            }
        } else {
            for (ParsableVariable paramVar : paramVars) {
                assert paramVar instanceof ProgramVariable;
                ProgramVariable pv = (ProgramVariable)paramVar;
                paramsOK = TB.and(paramsOK,
                                  TB.reachableValue(TB.var(paramVar), pv.getKeYJavaType()));
            }
        }
        return paramsOK;
    }

    /**
     * Builds the "general assumption"
     * @param implicitPre the implicit precondition
     * @param self self variable
     * @param heap heap variable
     * @param params list of parameter variables
     * @param taclet boolean is true if used for a wd-taclet
     * @param services
     * @return The {@link Term} containing the general assumptions.
     */
    private TermListAndFunc buildFreePre(Term implicitPre, ParsableVariable self,
                                         ParsableVariable heap,
                                         ImmutableList<ParsableVariable> params,
                                         boolean taclet,
                                         Services services) {
        ImmutableList<Term> resList = ImmutableSLList.<Term>nil();

        // "self != null"
        final Term selfNotNull = generateSelfNotNull(self);

        // "self.<created> = TRUE"
        final Term selfCreated = generateSelfCreated(self, heap);

        // "MyClass::exactInstance(self) = TRUE"
        final Term selfExactType = generateSelfExactType(self);

        // conjunction of...
        // - "p_i = null | p_i.<created> = TRUE" for object parameters, and
        // - "inBounds(p_i)" for integer parameters
        final Term paramsOK = generateParamsOK(params);

        // initial value of measured_by clause
        final Function mbyAtPreFunc = generateMbyAtPreFunc(services);
        final Term mbyAtPreDef;
        if (!taclet && type().equals(Type.OPERATION_CONTRACT)) {
            MethodWellDefinedness mwd = (MethodWellDefinedness)this;
            mbyAtPreDef = mwd.generateMbyAtPreDef(self, params, mbyAtPreFunc, services);
        } else {
            mbyAtPreDef = TB.tt();
        }

        final Term wellFormed = TB.wellFormed(TB.var(heap));

        final Term invTerm = self != null && this instanceof ClassWellDefinedness ?
                TB.inv(new Term[] {TB.var(heap)}, TB.var(self)) : TB.tt();

        final Term[] result;
        if (!taclet) {
            result = new Term[]
                    { wellFormed, selfNotNull, selfCreated, selfExactType,
                      invTerm, paramsOK, implicitPre, mbyAtPreDef };
        } else {
            result = new Term[]
                    { wellFormed, paramsOK, implicitPre };
        }
        for (Term t: result) {
            resList = resList.append(t);
        }
        return new TermListAndFunc(resList, mbyAtPreFunc);
    }

    /**
     * Conjoins two well-definedness taclets for pure method invocations
     * @param name taclet name
     * @param find1 first find term
     * @param find2 second find term
     * @param goal1 first precondition
     * @param goal2 second precondition
     * @param services
     * @return conjoined taclet
     */
    final static RewriteTaclet createTaclet(String name,
                                            Term find1,
                                            Term find2,
                                            Term goal1,
                                            Term goal2,
                                            TermServices services) {
        assert find1.op().name().equals(TermBuilder.WD_ANY.name());
        assert find2.op().name().equals(TermBuilder.WD_ANY.name());
        assert find1.sub(0).op().name().equals(find2.sub(0).op().name());
        assert find1.sub(0).arity() == find2.sub(0).arity();

        Map<ParsableVariable, ParsableVariable> map =
                new LinkedHashMap<ParsableVariable, ParsableVariable>();
        int i = 0;
        for (Term sub: find1.sub(0).subs()) {
            map.put((ParsableVariable)find2.sub(0).sub(i).op(), (ParsableVariable)sub.op());
            i++;
        }
        final OpReplacer or = new OpReplacer(map, services.getTermFactory());
        final Term goal = services.getTermBuilder().orSC(goal1, or.replace(goal2));
        final RewriteTacletBuilder tb = new RewriteTacletBuilder();
        tb.setFind(find1);
        tb.setName(MiscTools.toValidTacletName(name));
        tb.addRuleSet(new RuleSet(new Name("simplify")));
        tb.addGoalTerm(goal);
        return (RewriteTaclet) tb.getTaclet();
    }

    /**
     * Creates new well-definedness taclet for either an invariant reference or a pure
     * method invocation.
     * @param name taclet name
     * @param callee the receiver variable as a term
     * @param callTerm the whole invocation term
     * @param pre the method's or invariant's precondition
     * @param isStatic a boolean to tell if the method is static
     * @param services
     * @return created taclet
     */
    final static RewriteTaclet createTaclet(String name,
                                            Term callee,
                                            Term callTerm,
                                            Term pre,
                                            boolean isStatic,
                                            TermServices services) {
        final TermBuilder TB = services.getTermBuilder();
        final RewriteTacletBuilder tb = new RewriteTacletBuilder();
        final Term notNull = isStatic ? TB.tt() : TB.not(TB.equals(callee, TB.NULL()));
        final Term created = isStatic ? TB.tt() : TB.created(callee);
        tb.setFind(TB.wd(callTerm));
        tb.setName(MiscTools.toValidTacletName(name));
        tb.addRuleSet(new RuleSet(new Name("simplify")));
        tb.addGoalTerm(TB.andSC(notNull, created, pre));
        return (RewriteTaclet) tb.getTaclet();
    }

    /**
     * Creates new well-definedness taclet for a pure method invocation, which can
     * potentially throw an exception.
     * @param name taclet name
     * @param callTerm the whole invocation term
     * @param services
     * @return created taclet with false as replacewith term
     */
    final static RewriteTaclet createExcTaclet(String name,
                                               Term callTerm,
                                               TermServices services) {
        final TermBuilder TB = services.getTermBuilder();
        final RewriteTacletBuilder tb = new RewriteTacletBuilder();
        tb.setFind(TB.wd(callTerm));
        tb.setName(MiscTools.toValidTacletName(name));
        tb.addRuleSet(new RuleSet(new Name("simplify")));
        tb.addGoalTerm(TB.ff());
        return (RewriteTaclet) tb.getTaclet();
    }

    abstract Function generateMbyAtPreFunc(Services services);

    final Term replace(Term t, OriginalVariables newVars) {
		return replace(t, newVars.self, newVars.result, newVars.exception, newVars.atPres,
					   newVars.params, getOrigVars(), getHeaps());
    }

    final Condition replaceSV(Condition pre, SchemaVariable self,
                              ImmutableList<ParsableVariable> params) {
        final Term implicit = replaceSV(pre.implicit, self, params);
        final Term explicit = replaceSV(pre.explicit, self, params);
        return new Condition(implicit, explicit);
    }

    final void setMby(Term mby) {
        this.mby = mby;
    }

    final void addRequires(Condition req) {
        final Condition oldRequires = getRequires();
        this.requires = new Condition(TB.andSC(req.implicit, oldRequires.implicit),
                                      TB.andSC(req.explicit, oldRequires.explicit));
    }

    final void addRequires(Term req) {
        Condition requires = split(req);
        addRequires(requires);
    }

    final void setRequires(Term req) {
        this.requires = split(req);
    }

    final void setAssignable(Term ass, TermServices services) {
        this.assignable = ass;
        if (TB.strictlyNothing().equals(ass) || TB.FALSE().equals(ass)
                || ass == null || ass.op() == BooleanLiteral.FALSE) {
            this.assignable = TB.strictlyNothing();
        } else if (TB.tt().equals(ass) || TB.TRUE().equals(ass)
                || ass.op().equals(BooleanLiteral.TRUE)) {
            this.assignable = TB.allLocs();
        }
    }

    final void combineAssignable(Term ass1, Term ass2, TermServices services) {
        if (ass1 == null || TB.strictlyNothing().equals(ass1)) {
            setAssignable(ass2, services);
        } else if(ass2 == null || TB.strictlyNothing().equals(ass2)) {
            setAssignable(ass1, services);
        } else {
            setAssignable(TB.union(ass1, ass2), services);
        }
    }

    final void setAccessible(Term acc) {
        this.accessible = acc;
    }

    final void combineAccessible(Term acc, Term accPre, TermServices services) {
        if (acc == null && accPre == null) {
            setAccessible(null);
        } else if (accPre == null || accPre.equals(acc)) {
            setAccessible(acc);
        } else if (acc == null) {
            setAccessible(accPre);
        } else if (acc.equals(TB.allLocs()) || accPre.equals(TB.allLocs())) {
            // This case is necessary since KeY defaults most method contracts with allLocs
            final Term allLocs = TB.allLocs();
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

    final void addEnsures(Term ens) {
        Condition ensures = split(ens);
        addEnsures(ensures);
    }

    final void setEnsures(Term ens) {
        this.ensures = split(ens);
    }

    final Type type() {
        return this.type;
    }

    /**
     * Collects all remaining (implicitly or explicity) specified clauses
     * (except for pre-condition, post-condition and assignable-clause).
     * @return a list of all remaining clauses
     */
    ImmutableList<Term> getRest() {
        ImmutableList<Term> rest = ImmutableSLList.<Term>nil();
        final Term accessible = this.accessible;
        if (accessible != null) {
            rest = rest.append(accessible);
        }
        final Term mby = this.mby;
        if (mby != null) {
            rest = rest.append(mby);
        }
        final Term represents = this.represents;
        if (represents != null) {
            rest = rest.append(represents);
        }
        return rest;
    }

    //-------------------------------------------------------------------------
    // Public Interface
    //-------------------------------------------------------------------------

    /**
     * Detects the specification element's behaviour
     * @return behaviour string
     */
    public abstract String getBehaviour();

    /**
     * Detects if the specification element is a true (i.e. not an invariant) model field
     * @return true for model fields
     */
    public abstract boolean modelField();

    /**
     * Only for contracts with model_behaviour, the result is different from null.
     * @return the return value of a model method (null otherwise)
     */
    public abstract Term getAxiom();

    /**
     * Combines two well-definedness checks having the same name, id, target, type,
     * behaviour and are either both model fields or both not a model field.
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
            final Term acc = wdc.replace(wdc.getAccessible(), this.getOrigVars());
            combineAccessible(acc, this.getAccessible(), services);
        } else if (wdc.getAccessible() != null) {
            final Term acc = wdc.replace(wdc.getAccessible(), this.getOrigVars());
            setAccessible(acc);
        }
        if (this.getAssignable() != null && wdc.getAssignable() != null) {
            final Term ass = wdc.replace(wdc.getAssignable(), this.getOrigVars());
            combineAssignable(ass, this.getAssignable(), services);
        } else if (wdc.getAssignable() != null) {
            final Term ass = wdc.replace(wdc.getAssignable(), this.getOrigVars());
            setAssignable(ass, services);
        }
        final Condition ens = wdc.replace(wdc.getEnsures(), this.getOrigVars());
        addEnsures(ens);
        final Condition req = wdc.replace(wdc.getRequires(), this.getOrigVars());
        addRequires(req);
        if (this.getRepresents() != null && wdc.getRepresents() != null) {
            final Term rep = wdc.replace(wdc.getRepresents(), this.getOrigVars());
            this.represents = TB.andSC(rep, getRepresents());
        } else if (wdc.getRepresents() != null) {
            final Term rep = wdc.replace(wdc.getRepresents(), this.getOrigVars());
            this.represents = rep;
        }
        if (this.hasMby() && wdc.hasMby()) {
            final Term mby = wdc.replace(wdc.getMby(), this.getOrigVars());
            setMby(TB.pair(mby, this.getMby()));
        } else if (wdc.hasMby()) {
            final Term mby = wdc.replace(wdc.getMby(), this.getOrigVars());
            setMby(mby);
        }
        return this;
    }

    /**
     * This method checks, if well-definedness checks are generally turned on or off.
     * @return true if on and false if off
     */
    public final static boolean isOn() {
        final String setting =
                ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().getDefaultChoices().get(OPTION);
        if (setting.equals(OPTION + ":on")) {
            return true;
        } else if (setting.equals(OPTION + ":off")) {
            return false;
        } else {
            throw new RuntimeException("The setting for the wdProofs-option is not valid: "
                    + setting);
        }
    }

    /** collects terms for precondition,
     * assignable clause and other specification elements,
     * and postcondition & signals-clause */
    public final POTerms createPOTerms() {
        final Condition pre = this.getRequires();
        final Term mod = this.getAssignable();
        final ImmutableList<Term> rest = this.getRest();
        final Condition post = this.getEnsures();
        return new POTerms(pre, mod, rest, post);
    }

    public final WellDefinednessCheck addRepresents(Term rep) {
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
     * @param pre the precondition with the original variables
     * @param self the new self variable
     * @param heap the new heap variable
     * @param parameters the new parameter list
     * @param taclet is true if the precondition will be used in a taclet
     * @param services
     * @return the full valid pre-condition assumed in the pre-state
     * including the measured-by function
     */
    public final TermAndFunc getPre(final Condition pre,
                                    ParsableVariable self,
                                    ParsableVariable heap,
                                    ImmutableList<? extends ParsableVariable> parameters,
                                    boolean taclet,
                                    Services services) {
        ImmutableList<ParsableVariable> params = ImmutableSLList.<ParsableVariable>nil();
        for (ParsableVariable pv: parameters) {
            params = params.append(pv);
        }
        final IObserverFunction target = getTarget();
        final TermListAndFunc freePre =
                buildFreePre(pre.implicit, self, heap, params, taclet, services);
        final ImmutableList<Term> preTerms = freePre.terms.append(pre.explicit);
        Term res = TB.andSC(preTerms);
        if (!taclet
                && target instanceof IProgramMethod
                && ((IProgramMethod)target).isConstructor()
                && !JMLInfoExtractor.isHelper((IProgramMethod)target)) {
            final Term constructorPre =
                    appendFreePre(res, self, heap, services);
            return new TermAndFunc(constructorPre, freePre.func);
        } else {
            return new TermAndFunc(res, freePre.func);
        }
    }

    /**
     * Gets the full valid post-condition
     * @param post post-condition with original variables
     * @param result the new result variable
     * @param services
     * @return the full valid post-condition
     */
    public final Term getPost(final Condition post, ParsableVariable result,
                              TermServices services) {
        final Term reachable;
        if (result != null) {
            reachable = TB.reachableValue(TB.var(result), origVars.result.getKeYJavaType());
        } else {
            reachable = TB.tt();
        }
        return TB.andSC(reachable, post.implicit, post.explicit);
    }

    /**
     * Gets the necessary updates applicable to the post-condition
     * @param mod the assignable-clause
     * @param heap the current heap variable
     * @param heapAtPre the current variable for the heap of the pre-state
     * @param anonHeap the anonymous heap term
     * @param services
     * @return the applicable update term including an update for
     * old-expressions and the anonymisation update
     */
    public final Term getUpdates(Term mod, LocationVariable heap,
                                 ProgramVariable heapAtPre,
                                 Term anonHeap, TermServices services) {
        assert mod != null;
        assert anonHeap != null || TB.strictlyNothing().equals(mod);
        final Term havocUpd = TB.strictlyNothing().equals(mod) ?
                TB.skip()
                : TB.elementary(heap, TB.anon(TB.var(heap), mod, anonHeap));
        final Term oldUpd = heapAtPre != heap ?
                TB.elementary(TB.var(heapAtPre), TB.var(heap))
                : TB.skip();
        return TB.parallel(oldUpd, havocUpd);
    }

    public final Term replace(Term t, Variables vars) {
		return replace(t, vars.self, vars.result, vars.exception, vars.atPres,
					   vars.params, getOrigVars(), getHeaps());
    }

    public final POTerms replace(POTerms po, Variables vars) {
        final Condition pre = replace(po.pre, vars);
        final Term mod = replace(po.mod, vars);
        final ImmutableList<Term> rest = replace(po.rest, vars);
        final Condition post = replace(po.post, vars);
        return new POTerms(pre, mod, rest, post);
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

    public final Term getAssignable() {
        assert this.assignable != null;
        return this.assignable;
    }

    public final Term getAccessible() {
        return this.accessible;
    }

    public final Condition getEnsures() {
        assert this.ensures != null;
        return this.ensures;
    }

    public final Term getEnsures(LocationVariable heap) {
        return TB.andSC(getEnsures().implicit, getEnsures().explicit);
    }

    public final Term getRepresents() {
        return this.represents;
    }

    public final boolean isConstructor() {
        IObserverFunction target = getTarget();
        return target instanceof IProgramMethod
                && ((IProgramMethod)target).isConstructor();
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
    public final Term getMby() {
        return this.mby;
    }

    @Override
    public final boolean hasMby() {
        return this.mby != null;
    }

    @Override
    public final Term getRequires(LocationVariable heap) {
        return TB.andSC(getRequires().implicit, getRequires().explicit);
    }

    public final Term getAssignable(LocationVariable heap) {
        return getAssignable();
    }

    public final Term getAccessible(ProgramVariable heap) {
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
        assert contract instanceof WellDefinednessCheck;
        return new WellDefinednessPO(initConfig, (WellDefinednessCheck) contract);
    }

    @Override
    public final String getDisplayName() {
        String displayName = "Well-Definedness of JML ";
        if (modelField()) {
            displayName = displayName + "model field";
        } else {
            displayName = displayName + typeString();
        }
        if(!modelField() && !type().equals(Type.CLASS_INVARIANT)) {
            displayName = displayName + " " + id;
        }
        if(!getBehaviour().equals("")) {
            displayName = displayName + " (" + getBehaviour() + ")";
        }
        return displayName;
    }

    @Override
    public final boolean toBeSaved() {
        return false;
    }

    public final boolean hasSelfVar() {
        return origVars.self != null;
    }

    @Override
    public final OriginalVariables getOrigVars() {
        return this.origVars;
    }

    @Override
    public final boolean equals(Object o) {
        if (!(o instanceof WellDefinednessCheck)
                || !((WellDefinednessCheck)o).getKJT().equals(getKJT())) {
            return false;
        }
        WellDefinednessCheck wd = (WellDefinednessCheck)o;
        return wd.getName().equals(this.name);
    }

    @Override
    public final int hashCode() {
        return this.name.hashCode();
    }

    @Deprecated
    public final Term getPre(LocationVariable heap, ProgramVariable selfVar,
                             ImmutableList<ProgramVariable> paramVars,
                             Map<LocationVariable, ? extends ProgramVariable> atPreVars,
                             Services services) throws UnsupportedOperationException {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Deprecated
    public final Term getPre(List<LocationVariable> heapContext,
                             ProgramVariable selfVar, ImmutableList<ProgramVariable> paramVars,
                             Map<LocationVariable, ? extends ProgramVariable> atPreVars,
                             Services services) throws UnsupportedOperationException {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Deprecated
    public final Term getPre(LocationVariable heap, Term heapTerm, Term selfTerm,
                             ImmutableList<Term> paramTerms, Map<LocationVariable, Term> atPres,
                             Services services) throws UnsupportedOperationException {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Deprecated
    public final Term getPre(List<LocationVariable> heapContext,
                             Map<LocationVariable, Term> heapTerms, Term selfTerm,
                             ImmutableList<Term> paramTerms, Map<LocationVariable, Term> atPres,
                             Services services) throws UnsupportedOperationException {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Deprecated
    public final Term getDep(LocationVariable heap, boolean atPre,
                             ProgramVariable selfVar, ImmutableList<ProgramVariable> paramVars,
                             Map<LocationVariable, ? extends ProgramVariable> atPreVars,
                             Services services) {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Deprecated
    public final Term getDep(LocationVariable heap, boolean atPre, Term heapTerm,
                             Term selfTerm, ImmutableList<Term> paramTerms,
                             Map<LocationVariable, Term> atPres, Services services) {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Deprecated
    public final Term getGlobalDefs(LocationVariable heap, Term heapTerm, Term selfTerm,
                                    ImmutableList<Term> paramTerms, Services services) {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Deprecated
    public final Term getMby(ProgramVariable selfVar,
                             ImmutableList<ProgramVariable> paramVars,
                             Services services) throws UnsupportedOperationException {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Deprecated
    public final Term getMby(Map<LocationVariable,Term> heapTerms, Term selfTerm,
                             ImmutableList<Term> paramTerms, Map<LocationVariable, Term> atPres,
                             Services services) throws UnsupportedOperationException {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    /**
     * A static data structure for passing a term list with a function.
     *
     * @author Michael Kirsten
     */
    private final static class TermListAndFunc {
        private final ImmutableList<Term> terms;
        private final Function func;

        private TermListAndFunc(ImmutableList<Term> ts, Function f) {
            this.terms = ts;
            this.func = f;
        }
    }

    /**
     * A static data structure for storing and passing two terms, denoting the implicit
     * and the explicit part of a pre- or post-condition.
     *
     * @author Michael Kirsten
     */
    final static class Condition {
        final Term implicit;
        final Term explicit;

        Condition(Term implicit, Term explicit) {
            this.implicit = implicit;
            this.explicit = explicit;
        }
    }

    /**
     * A static data structure for passing a term with a function.
     *
     * @author Michael Kirsten
     */
    public final static class TermAndFunc {
        public final Term term;
        public final Function func;

        TermAndFunc(Term t, Function f) {
            this.term = t;
            this.func = f;
        }
    }

    /**
     * A data structure for storing and passing all specifications of a
     * specification element includinf pre- and post-condition, an
     * assignable-clause and a list of all other clauses specified.
     *
     * @author Michael Kirsten
     */
    public final static class POTerms {
        public final Condition pre;
        public final Term mod;
        public final ImmutableList<Term> rest;
        public final Condition post;

        POTerms(Condition pre, Term mod,
                ImmutableList<Term> rest, Condition post) {
            this.pre = pre;
            this.mod = mod;
            this.rest = rest;
            this.post = post;
        }
    }
}