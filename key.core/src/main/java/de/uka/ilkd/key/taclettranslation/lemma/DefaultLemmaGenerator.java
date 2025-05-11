/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.taclettranslation.lemma;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;

import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.taclettranslation.IllegalTacletException;
import de.uka.ilkd.key.taclettranslation.SkeletonGenerator;
import de.uka.ilkd.key.taclettranslation.TacletFormula;
import de.uka.ilkd.key.taclettranslation.TacletVisitor;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSet;

/**
 * The default lemma generator: Supports only certain types of taclets. If a taclet is not
 * supported, the generator throws an exception.
 */
class DefaultLemmaGenerator implements LemmaGenerator {

    // Describes how a schema variable is mapped to another operator, e.g.
    // logical variable.
    private final HashMap<SchemaVariable, Term> mapping = new LinkedHashMap<>();

    @Override
    public @NonNull TacletFormula translate(@NonNull Taclet taclet, @NonNull TermServices services) {
        String result = checkTaclet(taclet);
        if (result != null) {
            throw new IllegalTacletException(result);
        }
        Term formula = SkeletonGenerator.DEFAULT_TACLET_TRANSLATOR.translate(taclet, services);
        formula = rebuild(taclet, formula, services, new LinkedHashSet<>());
        result = checkForIllegalOps(formula, taclet, false);
        if (result != null) {
            throw new IllegalTacletException(result);
        }
        return new LemmaFormula(taclet, formula);
    }

    private @NonNull Term replace(@NonNull Taclet taclet, @NonNull Term term, @NonNull TermServices services) {
        if (term.op() instanceof SchemaVariable) {
            return getInstantiation(taclet, (SchemaVariable) term.op(), services);
        }

        return term;
    }

    public static String checkTaclet(final @NonNull Taclet taclet) {
        String result = checkForIllegalConditions(taclet);
        if (result != null) {
            return result;
        }
        TacletVisitor visitor = new TacletVisitor() {

            @Override
            public void visit(@NonNull Term visited) {
                String res = checkForIllegalOps(visited, taclet, true);
                if (res != null) {
                    failureOccurred(res);
                }
            }

            @Override
            public String visit(Taclet taclet, boolean visitAddrules) {

                if (taclet instanceof RewriteTaclet rwTaclet) {
                    Sequent assumptions = rwTaclet.ifSequent();
                    int appRestr = rwTaclet.getApplicationRestriction();
                    if (!assumptions.isEmpty() && appRestr == 0) {
                        // any restriction is fine. The polarity switches are equiv
                        // to"inSequentState" in this respect.
                        failureOccurred("The given taclet " + taclet.name()
                            + " is neither \\sameUpdateLevel nor \\inSequentState.");
                    }
                }

                return super.visit(taclet, visitAddrules);
            }
        };

        return visitor.visit(taclet, true);

    }

    public static @Nullable String checkForIllegalConditions(@NonNull Taclet taclet) {
        if (!taclet.getVariableConditions().isEmpty()) {
            return "The given taclet " + taclet.name()
                + " contains variable conditions that are not supported.";
        }
        return null;
    }

    public static @Nullable String checkForIllegalOps(@NonNull Term formula, @NonNull Taclet owner,
                                                      boolean schemaVarsAreAllowed) {
        if ((!schemaVarsAreAllowed && formula.op() instanceof SchemaVariable)
                || formula.op() instanceof Modality
                || formula.op() instanceof ProgramSV || formula.op() instanceof SkolemTermSV
                || formula.op() instanceof UpdateSV) {
            return "The given taclet " + owner.name()
                + " contains a operator that is not allowed:\n" + formula.op().name();
        }
        for (Term sub : formula.subs()) {
            String s = checkForIllegalOps(sub, owner, schemaVarsAreAllowed);
            if (s != null) {
                return s;
            }
        }
        return null;
    }

    /**
     * Returns the instantiation for a certain schema variable, i.e. the skolem term that is used
     * for the instantiation.
     *
     * @param owner The taclet the schema variable belongs to.
     * @param var The variable to be instantiated.
     * @param services
     * @return instantiation of the schema variable <code>var</code>.
     */
    protected final @NonNull Term getInstantiation(@NonNull Taclet owner, SchemaVariable var, @NonNull TermServices services) {
        Term instantiation = mapping.get(var);
        if (instantiation == null) {
            instantiation = createInstantiation(owner, var, services);
            mapping.put(var, instantiation);


        }
        return instantiation;
    }

    /**
     * Returns the instantiation of <code>var</code>. In the case that an instantiation does not
     * exist it is created.
     *
     * @param owner
     * @param var
     * @param services
     *
     */
    private @NonNull Term getInstantation(Taclet owner, @NonNull VariableSV var, @NonNull TermServices services) {
        Term instantiation = mapping.get(var);
        if (instantiation == null) {
            instantiation = createInstantiation(owner, var, services);
            mapping.put(var, instantiation);
        }
        return instantiation;
    }

    private @NonNull Term createInstantiation(@NonNull Taclet owner, SchemaVariable sv, @NonNull TermServices services) {
        if (sv instanceof VariableSV) {
            return createInstantiation(owner, (VariableSV) sv, services);
        }
        if (sv instanceof TermSV) {
            return createInstantiation(owner, (TermSV) sv, services);
        }
        if (sv instanceof FormulaSV) {
            return createInstantiation(owner, (FormulaSV) sv, services);
        }
        throw new IllegalTacletException("The taclet contains a schema variable which"
            + "is not supported.\n" + "Taclet: " + owner.name().toString() + "\n"
            + "SchemaVariable: " + sv.name().toString() + "\n");
    }

    /**
     * Creates the instantiation for a schema variable of type variable, i.e a new logical variable
     * is returned.
     *
     * @param owner the taclet the schema variable belongs to.
     * @param sv the schema variable to be instantiated.
     * @param services some information about the proof currently considered.
     * @return a term that can be used for instantiating the schema variable.
     */
    private @NonNull Term createInstantiation(Taclet owner, @NonNull VariableSV sv, @NonNull TermServices services) {
        Name name = createUniqueName(services, "v_" + sv.name().toString());
        Sort sort = replaceSort(sv.sort(), services);
        LogicVariable variable = new LogicVariable(name, sort);
        return services.getTermFactory().createTerm(variable);
    }

    /**
     * Creates the instantiation for a schema variable of type term. Mainly a skolem function is
     * returned that depends on the prefix of <code>sv</code>.
     */
    private @NonNull Term createInstantiation(@NonNull Taclet owner, @NonNull TermSV sv, @NonNull TermServices services) {
        return createSimpleInstantiation(owner, sv, services);
    }

    /**
     * Creates the instantiation for a schema variable of type term. Mainly a skolem function is
     * returned that depends on the prefix of <code>sv</code>.
     */
    private @NonNull Term createInstantiation(@NonNull Taclet owner, @NonNull FormulaSV sv, @NonNull TermServices services) {
        return createSimpleInstantiation(owner, sv, services);
    }

    /**
     * Since only taclets are supported that contain only FOL-constituents, there is no need to make
     * it also dependend on program variables. (See: Ensuring the Correctness of Lightweight Tactics
     * for JavaCard Dynamic Logic.) This method is used for both Formula schema variables and Term
     * schema variables.
     */
    private @NonNull Term createSimpleInstantiation(@NonNull Taclet owner, @NonNull OperatorSV sv, @NonNull TermServices services) {
        ImmutableSet<SchemaVariable> prefix = owner.getPrefix(sv).prefix();

        Sort[] argSorts = computeArgSorts(prefix, services);
        Term[] args = computeArgs(owner, prefix, services);
        Name name = createUniqueName(services, "f_" + sv.name().toString());

        JFunction function =
            new JFunction(name, replaceSort(sv.sort(), services), argSorts);
        return services.getTermBuilder().func(function, args);
    }

    private @NonNull Name createUniqueName(@NonNull TermServices services, @NonNull String baseName) {
        return new Name(services.getTermBuilder().newName(baseName));
    }

    private Sort @NonNull [] computeArgSorts(@NonNull ImmutableSet<SchemaVariable> svSet, TermServices services) {
        Sort[] argSorts = new Sort[svSet.size()];
        int i = 0;
        for (var sv : svSet) {
            if (sv instanceof OperatorSV asv)
                argSorts[i] = replaceSort(asv.sort(), services);
            i++;
        }
        return argSorts;
    }

    private Term @NonNull [] computeArgs(@NonNull Taclet owner, @NonNull ImmutableSet<SchemaVariable> svSet,
                                         @NonNull TermServices services) {
        Term[] args = new Term[svSet.size()];
        int i = 0;
        for (var sv : svSet) {
            args[i] = getInstantiation(owner, sv, services);
            i++;
        }
        return args;
    }

    /**
     * Rebuilds a term recursively and replaces all schema variables with skolem terms/variables.
     */
    private @NonNull Term rebuild(@NonNull Taclet taclet, @NonNull Term term, @NonNull TermServices services,
                                  @NonNull HashSet<QuantifiableVariable> boundedVariables) {
        Term[] newSubs = new Term[term.arity()];
        int i = 0;
        LinkedList<QuantifiableVariable> qvars = new LinkedList<>();
        for (QuantifiableVariable qvar : term.boundVars()) {
            boundedVariables.add(qvar);
            if (qvar instanceof VariableSV) {
                qvars.add(
                    (QuantifiableVariable) getInstantation(taclet, (VariableSV) qvar, services)
                            .op());
            }
        }

        for (Term sub : term.subs()) {
            newSubs[i] = replace(taclet, sub, services);
            // if(newSubs[i] == null){
            // newSubs[i] = rebuild(taclet,sub,services);
            newSubs[i] = rebuild(taclet, newSubs[i], services, boundedVariables);
            // }
            i++;
        }

        Operator newOp = replaceOp(term.op(), services);

        return services.getTermFactory().createTerm(newOp, newSubs,
            new ImmutableArray<>(qvars), null);
    }

    /**
     * Sometimes operators must be replaced during lemma generation. Override this method to
     * accomplish this in a subclass.
     *
     * <p>
     * By default, this method returns the argument <tt>op</tt>.
     *
     * @param op the operator to be replaced, not <code>null</code>
     * @param services A services object for lookups
     * @return the replacement operator, not <code>null</code>
     */
    protected Operator replaceOp(Operator op, TermServices services) {
        return op;
    }

    /**
     * Sometimes sorts must be replaced during lemma generation. Override this method to accomplish
     * this in a subclass.
     *
     * <p>
     * By default, this method returns the argument <tt>sort</tt>.
     *
     * @param sort the sort to be replaced, not <code>null</code>
     * @param services A services object for lookups
     * @return the replacement sort, not <code>null</code>
     */
    protected Sort replaceSort(Sort sort, TermServices services) {
        return sort;
    }
}
