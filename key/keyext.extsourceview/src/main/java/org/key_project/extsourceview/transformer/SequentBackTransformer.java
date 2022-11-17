package org.key_project.extsourceview.transformer;

import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.origin.OriginRef;
import de.uka.ilkd.key.logic.origin.OriginRefType;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import org.key_project.util.collection.ImmutableList;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

import static org.key_project.extsourceview.Utils.getSubOriginRefs;

public class SequentBackTransformer {

    private final Services svc;
    private final Proof proof;
    private final Sequent sequent;

    private final boolean continueOnError;
    private final boolean recursiveOriginLookup;
    private final boolean allowNoOriginFormulas;

    public SequentBackTransformer(Services svc, Proof proof, Node node, boolean continueOnError, boolean recursiveOriginLookup, boolean allowNoOriginFormulas) {
        this.svc = svc;
        this.proof = proof;
        this.sequent = node.sequent();

        this.continueOnError = continueOnError;
        this.recursiveOriginLookup = recursiveOriginLookup;
        this.allowNoOriginFormulas = allowNoOriginFormulas;
    }

    public InsertionSet extract() throws TransformException {
        return new InsertionSet(ImmutableList.fromList(extractTerms()));

    }

    public PositionMap generatePositionMap() throws TransformException {

        ContractPO contractPO = svc.getSpecificationRepository().getPOForProof(proof);

        if (!(contractPO instanceof FunctionalOperationContractPO)) {
            throw new TransformException("Can only work on functional contracts");
        }

        FunctionalOperationContractPO funContractPO = (FunctionalOperationContractPO) contractPO;

        FunctionalOperationContract contract = funContractPO.getContract();

        IProgramMethod progrMethod = contract.getTarget();

        PositionInfo pos = progrMethod.getPositionInfo();

        return new PositionMap(pos);
    }

    private ArrayList<InsertionTerm> extractTerms() throws TransformException {

        ArrayList<InsertionTerm> result = new ArrayList<>();

        boolean completeAssertSetInResult = false;

        for (SequentFormula sf : sequent.antecedent()) {
            List<Term> split = splitFormula(sf.formula(), Junctor.AND);

            for (var term : split) {
                try {
                    InsertionTerm insterm = categorizeTerm(term, true);
                    if (completeAssertSetInResult && insterm.Type == InsertionType.ASSERT) {
                        throw new TransformException("Cannot transform sequent with multiple disjunct assertions");
                    }
                    result.add(insterm);
                } catch (TransformException e) {
                    if (continueOnError) {
                        result.add(new InsertionTerm(InsertionType.ASSUME_ERROR, term));
                        continue;
                    }
                    throw e;
                }
            }
            if (result.stream().anyMatch(p -> p.Type == InsertionType.ASSERT)) completeAssertSetInResult = true;

        }

        for (SequentFormula sf : sequent.succedent()) {
            List<Term> split = splitFormula(sf.formula(), Junctor.AND);

            for (var term : split) {
                try {
                    InsertionTerm insterm = categorizeTerm(term, false);
                    if (completeAssertSetInResult && insterm.Type == InsertionType.ASSERT) {
                        throw new TransformException("Cannot transform sequent with multiple disjunct assertions");
                    }
                    result.add(insterm);
                } catch (TransformException e) {
                    if (continueOnError) {
                        result.add(new InsertionTerm(InsertionType.ASSERT_ERROR, term));
                        continue;
                    }
                    throw e;
                }
            }
            if (result.stream().anyMatch(p -> p.Type == InsertionType.ASSERT)) completeAssertSetInResult = true;
        }

        return result;
    }

    private InsertionTerm categorizeTerm(Term term, boolean ante) throws TransformException {

        boolean succ = !ante;

        if (term.containsJavaBlockRecursive()) {
            throw new TransformException("Cannot transform antecedent formula with modularities");
        }

        if (ante && isRequires(term)) {
            return new InsertionTerm(InsertionType.ASSUME, term);
        }

        if (ante && isType(term, OriginRefType.USER_INTERACTION)) {
            return new InsertionTerm(InsertionType.ASSUME, term);
        }

        if (ante && isType(term, OriginRefType.LOOP_BODYPRESERVEDINV_WELLFORMED)) {
            return new InsertionTerm(InsertionType.ASSUME, term);
        }

        if (ante && isType(term, OriginRefType.LOOP_BODYPRESERVEDINV_GUARD)) {
            return new InsertionTerm(InsertionType.ASSUME, term);
        }

        if (ante && isType(term, OriginRefType.LOOP_BODYPRESERVEDINV_INVARIANT_BEFORE)) {
            return new InsertionTerm(InsertionType.ASSUME, term);
        }

        if (ante && isType(term, OriginRefType.LOOP_USECASE_WELLFORMED)) {
            return new InsertionTerm(InsertionType.ASSUME, term);
        }

        if (ante && isType(term, OriginRefType.LOOP_USECASE_INVARIANT)) {
            return new InsertionTerm(InsertionType.ASSUME, term);
        }

        if (ante && isType(term, OriginRefType.LOOP_USECASE_GUARD)) {
            return new InsertionTerm(InsertionType.ASSUME, term);
        }

        if (succ && isRequires(term)) {
            // special-case, an [assume] in the succedent (e.g. by applying teh notLeft taclet)
            return new InsertionTerm(InsertionType.ASSUME, termNot(term));
        }

        if (succ && isType(term, OriginRefType.LOOP_USECASE_GUARD)) {
            // special-case, this should be an [assume] (int the antecedent)
            return new InsertionTerm(InsertionType.ASSUME, termNot(term));
        }

        if (succ && isEnsures(term)) {
            return new InsertionTerm(InsertionType.ASSERT, term);
        }

        if (succ && isAssignable(term)) {
            return new InsertionTerm(InsertionType.ASSIGNABLE, term);
        }

        if (succ && isType(term, OriginRefType.USER_INTERACTION)) {
            // special-case, an [user_interaction] in the succedent (probably cut)
            return new InsertionTerm(InsertionType.ASSUME, termNot(term));
        }

        if (succ && isType(term, OriginRefType.LOOP_INITIALLYVALID_INVARIANT, OriginRefType.LOOP_INITIALLYVALID_WELLFORMED)) {
            return new InsertionTerm(InsertionType.ASSERT, term);
        }

        if (succ && isType(term, OriginRefType.LOOP_BODYPRESERVEDINV_VARIANT, OriginRefType.LOOP_BODYPRESERVEDINV_INVARIANT_AFTER)) {
            return new InsertionTerm(InsertionType.ASSERT, term);
        }

        if (allowNoOriginFormulas && getRelevantOrigins(term).isEmpty()) {
            if (ante) {
                return new InsertionTerm(InsertionType.ASSUME, term);
            } else {
                return new InsertionTerm(InsertionType.ASSERT, term);
            }
        }

        throw new TransformException("Failed to categorize term '" + term + "'");
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

        return origins.stream().allMatch(p -> Arrays.stream(filter).anyMatch(q -> p.Type == q));

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

    private List<Term> splitFormula(Term f, Operator j) {
        var r = new ArrayList<Term>();

        if (f.op() == j) {
            r.addAll(splitFormula(f.sub(0), j));
            r.addAll(splitFormula(f.sub(1), j));
        } else {
            r.add(f);
        }

        return r;
    }

}
