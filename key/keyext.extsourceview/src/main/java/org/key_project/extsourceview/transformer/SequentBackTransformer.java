package org.key_project.extsourceview.transformer;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.origin.OriginRef;
import de.uka.ilkd.key.logic.origin.OriginRefType;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import org.key_project.util.collection.ImmutableList;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

import static org.key_project.extsourceview.Utils.getSubOriginRefs;

/**
 * Implements the logic of extracting (to-be-displayed) Terms from the sequent
 * and categorizing them
 */
public class SequentBackTransformer {

    private final Services svc;
    private final Proof proof;
    private final Sequent sequent;

    private final boolean continueOnError;
    private final boolean recursiveOriginLookup;
    private final boolean allowNoOriginFormulas;
    private final boolean allowDisjunctAssertions;

    public SequentBackTransformer(Services svc, Proof proof, Node node, boolean continueOnError, boolean recursiveOriginLookup, boolean allowNoOriginFormulas, boolean allowDisjunct) {
        this.svc = svc;
        this.proof = proof;
        this.sequent = node.sequent();

        this.continueOnError = continueOnError;
        this.recursiveOriginLookup = recursiveOriginLookup;
        this.allowNoOriginFormulas = allowNoOriginFormulas;
        this.allowDisjunctAssertions = allowDisjunct;
    }

    public InsertionSet extract() throws TransformException, InternTransformException {
        return new InsertionSet(ImmutableList.fromList(extractTerms()));

    }

    private List<InsertionTerm> extractTerms() throws TransformException, InternTransformException {

        List<InsertionTerm>       resultAssume = new ArrayList<>();
        List<List<InsertionTerm>> resultAssert = new ArrayList<>();
        List<InsertionTerm>       resultAssignable = new ArrayList<>();

        for (SequentFormula sf : sequent.antecedent()) {

            var nr = sequent.formulaNumberInSequent(true, sf);
            var rootPIO = PosInOccurrence.findInSequent(sequent, nr, PosInTerm.getTopLevel());

            List<PosInOccurrence> split = splitFormula(rootPIO, Junctor.AND);

            List<InsertionTerm> addTermsAssume     = new ArrayList<>();
            List<InsertionTerm> addTermsAssert     = new ArrayList<>();
            List<InsertionTerm> addTermsAssignable = new ArrayList<>();

            for (var pio : split) {
                var term = pio.subTerm();
                try {
                    InsertionTerm insterm = categorizeTerm(term, pio, true);
                    switch (insterm.Type) {
                        case ASSUME:
                        case ASSUME_ERROR:
                            addTermsAssume.add(insterm);
                            break;
                        case ASSERT:
                        case ASSERT_ERROR:
                            addTermsAssert.add(insterm);
                            break;
                        case ASSIGNABLE:
                            addTermsAssignable.add(insterm);
                            break;
                        default:
                            throw new InternTransformException("Unknown InsertionType");
                    }
                } catch (TransformException e) {
                    if (continueOnError) {
                        addTermsAssume.add(new InsertionTerm(InsertionType.ASSUME_ERROR, term, pio));
                        continue;
                    }
                    throw e;
                }
            }

            resultAssume.addAll(addTermsAssume);
            resultAssert.add(addTermsAssert);
            resultAssignable.addAll(addTermsAssignable);
        }

        for (SequentFormula sf : sequent.succedent()) {

            var nr = sequent.formulaNumberInSequent(false, sf);
            var rootPIO = PosInOccurrence.findInSequent(sequent, nr, PosInTerm.getTopLevel());

            List<PosInOccurrence> split = splitFormula(rootPIO, Junctor.AND);

            ArrayList<InsertionTerm> addTermsAssume = new ArrayList<>();
            ArrayList<InsertionTerm> addTermsAssert = new ArrayList<>();
            ArrayList<InsertionTerm> addTermsAssignable = new ArrayList<>();

            for (var pio : split) {
                var term = pio.subTerm();
                try {
                    InsertionTerm insterm = categorizeTerm(term, pio, false);
                    switch (insterm.Type) {
                        case ASSUME:
                        case ASSUME_ERROR:
                            addTermsAssume.add(insterm);
                            break;
                        case ASSERT:
                        case ASSERT_ERROR:
                            addTermsAssert.add(insterm);
                            break;
                        case ASSIGNABLE:
                            addTermsAssignable.add(insterm);
                            break;
                        default:
                            throw new InternTransformException("Unknown InsertionType");
                    }
                } catch (TransformException e) {
                    if (continueOnError) {
                        addTermsAssert.add(new InsertionTerm(InsertionType.ASSERT_ERROR, term, pio));
                        continue;
                    }
                    throw e;
                }
            }

            resultAssume.addAll(addTermsAssume);
            resultAssert.add(addTermsAssert);
            resultAssignable.addAll(addTermsAssignable);
        }

        resultAssert = resultAssert.stream().filter(p -> p.size() > 0).collect(Collectors.toList());

        if (resultAssert.size() <= 1) {
            // default/easy case - we have one set if assert terms
            // we can simply return them
            ArrayList<InsertionTerm> res = new ArrayList<>();
            res.addAll(resultAssume);
            for (var r: resultAssert) res.addAll(r);
            res.addAll(resultAssignable);
            return res;
        } else {
            // annoying case - we have multiple sets of (disjunct) assert terms
            // our InsTerms are joined with AND's, but the individual blocks need to be joined with OR...
            // Let's see if we can move some terms to the assume part

            List<List<InsertionTerm>> originless = new ArrayList<>();
            List<List<InsertionTerm>> originfull = new ArrayList<>();
            List<List<InsertionTerm>> originsome = new ArrayList<>();

            for (var pb: resultAssert) {

                if (pb.stream().allMatch(t -> getRelevantOrigins(t.Term).isEmpty())) {
                    originless.add(pb);
                } else if (pb.stream().noneMatch(t -> getRelevantOrigins(t.Term).isEmpty())) {
                    originfull.add(pb);
                } else {
                    // if we are here we can not translate them (normally) - we have multiple disjunct assertions
                    originsome.add(pb);
                }

            }

            if (originfull.size() == 1 && originsome.size() == 0) {

                // only 1 "assert-block" has actually relevant origins, we can move the other blocks to the assume part

                List<InsertionTerm> res = new ArrayList<>();

                // add (normal) @assume's
                res.addAll(resultAssume);

                // the term where all origins are relevant gets to be the @assert
                for (var r: originfull) res.addAll(r);

                // the other terms (where not all origins are relevant) get demoted to @assumes
                for (var r: originless) for (var t: r) res.add(new InsertionTerm(InsertionType.ASSUME, termNot(t.Term), t.PIO));

                // also there are the @assignable's
                res.addAll(resultAssignable);

                return res;

            } else {

                // we have "multiple disjunct assertions" - do the fallback
                // we merge them all together into a single big term
                // not pretty, but you gotta do what you gotta do

                if (!allowDisjunctAssertions) {
                    throw new TransformException("Cannot transform sequent with multiple disjunct assertions");
                }

                ArrayList<InsertionTerm> res = new ArrayList<>();

                res.addAll(resultAssume);

                PosInOccurrence topLevel = new PosInOccurrence(sequent.getFormulabyNr(1), PosInTerm.getTopLevel(), false);

                TermBuilder tb = svc.getTermBuilder();

                Term joinedAssert = tb.or(resultAssert.stream().map(p -> tb.and(p.stream().map(q->q.Term).collect(Collectors.toList()))).collect(Collectors.toList()));

                res.add(new InsertionTerm(InsertionType.ASSERT, joinedAssert, topLevel));

                return res;
            }

        }
    }

    private InsertionTerm categorizeTerm(Term term, PosInOccurrence pio, boolean ante) throws TransformException {

        if (term.containsJavaBlockRecursive()) {
            throw new TransformException("Cannot transform antecedent formula with modularities");
        }

        if (isRequires(term)) {
            return createAssume(ante, term, pio);
        }

        if (isType(term, OriginRefType.USER_INTERACTION)) {
            return createAssume(ante, term, pio);
        }

        if (isType(term, OriginRefType.LOOP_BODYPRESERVEDINV_WELLFORMED)) {
            return createAssume(ante, term, pio);
        }

        if (isType(term, OriginRefType.LOOP_BODYPRESERVEDINV_GUARD)) {
            return createAssume(ante, term, pio);
        }

        if (isType(term, OriginRefType.LOOP_BODYPRESERVEDINV_INVARIANT_BEFORE)) {
            return createAssume(ante, term, pio);
        }

        if (isType(term, OriginRefType.LOOP_USECASE_WELLFORMED)) {
            return createAssume(ante, term, pio);
        }

        if (isType(term, OriginRefType.LOOP_USECASE_INVARIANT)) {
            return createAssume(ante, term, pio);
        }

        if (isType(term, OriginRefType.LOOP_USECASE_GUARD)) {
            return createAssume(ante, term, pio);
        }

        if (isType(term, OriginRefType.OPERATION_POSTCONDITION, OriginRefType.OPERATION_POST_WELLFORMED, OriginRefType.OPERATION_EXC_WELLFORMED)) {
            return createAssume(ante, term, pio);
        }

        if (isType(term, OriginRefType.OPERATION_POST_SELFINVARIANT, OriginRefType.OPERATION_EXC_SELFINVARIANT)) {
            return createAssert(ante, term, pio);
        }

        if (isEnsures(term)) {
            return createAssert(ante, term, pio);
        }

        if (isAssignable(term)) {
            return createAssignable(ante, term, pio);
        }

        if (isType(term, OriginRefType.LOOP_INITIALLYVALID_INVARIANT, OriginRefType.LOOP_INITIALLYVALID_WELLFORMED)) {
            return createAssert(ante, term, pio);
        }

        if (isType(term, OriginRefType.LOOP_BODYPRESERVEDINV_VARIANT, OriginRefType.LOOP_BODYPRESERVEDINV_INVARIANT_AFTER)) {
            return createAssert(ante, term, pio);
        }

        if (isType(term, OriginRefType.OPERATION_PRE_PRECONDITION, OriginRefType.OPERATION_PRE_WELLFORMED)) {
            return createAssert(ante, term, pio);
        }

        if (allowNoOriginFormulas && getRelevantOrigins(term).isEmpty()) {
            if (ante) {
                return createAssume(true, term, pio);
            } else {
                return createAssert(false, term, pio);
            }
        }

        throw new TermTransformException(term, "Failed to categorize term '" + term + "'");
    }

    private InsertionTerm createAssume(boolean ante, Term term, PosInOccurrence pio) {
        if (ante) {
            return new InsertionTerm(InsertionType.ASSUME, term, pio);
        } else {
            // special-case, this should be an [assume] (but is in the antecedent)
            return new InsertionTerm(InsertionType.ASSUME, termNot(term), pio);
        }
    }

    private InsertionTerm createAssert(boolean ante, Term term, PosInOccurrence pio) {
        if (ante) {
            // special-case, this should be an [assert] (but is in the antecedent)
            return new InsertionTerm(InsertionType.ASSERT, termNot(term), pio);
        } else {
            return new InsertionTerm(InsertionType.ASSERT, term, pio);
        }
    }

    private InsertionTerm createAssignable(boolean ante, Term term, PosInOccurrence pio) throws TermTransformException {
        if (ante) {
            throw new TermTransformException(term, "Cannot transform assignbale term in the antecedent");
        }

        return new InsertionTerm(InsertionType.ASSIGNABLE, term, pio);
    }

    private Term termNot(Term term) {
        Term result = svc.getTermBuilder().not(term);

        result = svc.getTermFactory().addOriginRef(result, term.getOriginRef());

        return result;
    }

    private boolean isRequires(Term term) {
        return isType(term,
                OriginRefType.JML_REQUIRES,
                OriginRefType.JML_REQUIRES_FREE,
                OriginRefType.IMPLICIT_REQUIRES_SELFINVARIANT,
                OriginRefType.IMPLICIT_REQUIRES_PARAMSOK,
                OriginRefType.IMPLICIT_REQUIRES_SELFEXACTINSTANCE,
                OriginRefType.IMPLICIT_REQUIRES_WELLFORMEDHEAP,
                OriginRefType.IMPLICIT_REQUIRES_SELFCREATED,
                OriginRefType.IMPLICIT_REQUIRES_MEASUREDBY_INITIAL,
                OriginRefType.IMPLICIT_REQUIRES_SELFNOTNULL,
                OriginRefType.IMPLICIT_REQUIRES_PARAM_NON_NULL);
    }

    private boolean isEnsures(Term term) {
        return isType(term,
                OriginRefType.JML_ENSURES,
                OriginRefType.JML_ENSURES_FREE,
                OriginRefType.IMPLICIT_ENSURES_SELFINVARIANT,
                OriginRefType.IMPLICIT_ENSURES_ASSIGNABLE,
                OriginRefType.IMPLICIT_ENSURES_EXCNULL);
    }

    private boolean isAssignable(Term term) {
        return isType(term, OriginRefType.JML_ASSIGNABLE, OriginRefType.IMPLICIT_ENSURES_ASSIGNABLE, OriginRefType.LOOP_BODYPRESERVEDINV_ASSIGNABLE);
    }

    private boolean isType(Term term, OriginRefType... filter) {
        if (term.containsJavaBlockRecursive())
            return false;

        var origins = getRelevantOrigins(term);
        if (origins.size() == 0)
            return false;

        return origins.stream().allMatch(p -> Arrays.stream(filter).anyMatch(q -> p.Type == q) || InsertionTerm.isIrrelevantOriginRefType(p.Type));

    }

    private List<OriginRef> getRelevantOrigins(Term term) {
        if (recursiveOriginLookup) {
            return getSubOriginRefs(term, true, false).stream()
                    .filter(p -> p.Type != OriginRefType.UNKNOWN)
                    .filter(p -> p.Type != OriginRefType.JAVA_STMT)
                    .collect(Collectors.toList());
        } else {
            return term.getOriginRef().stream()
                    .filter(p -> p.Type != OriginRefType.UNKNOWN)
                    .filter(p -> p.Type != OriginRefType.JAVA_STMT)
                    .collect(Collectors.toList());
        }
    }

    private List<PosInOccurrence> splitFormula(PosInOccurrence pio, Operator j) {
        var r = new ArrayList<PosInOccurrence>();

        var f = pio.subTerm();

        if (f.op() == j) {
            r.addAll(splitFormula(pio.down(0), j));
            r.addAll(splitFormula(pio.down(1), j));
        } else {
            r.add(pio);
        }

        return r;
    }
}
