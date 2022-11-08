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
import java.util.List;
import java.util.stream.Collectors;

public class SequentBackTransformer {

    private final Services svc;
    private final Proof proof;
    private final Node node;
    private final Sequent sequent;

    public SequentBackTransformer(Services svc, Proof proof, Node node) {
        this.svc = svc;
        this.proof = proof;
        this.node = node;
        this.sequent = node.sequent();
    }

    public InsertionSet extract(boolean continueOnError) throws TransformException {
        return new InsertionSet(ImmutableList.fromList(extractTerms(continueOnError)));

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

    private ArrayList<InsertionTerm> extractTerms(boolean continueOnError) throws TransformException {

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

        if (ante && isUserInteraction(term)) {
            return new InsertionTerm(InsertionType.ASSUME, term);
        }

        if (succ && isRequires(term)) {
            // special-case, an [assume] in the succedent (e.g. by applying teh notLeft taclet)
            return new InsertionTerm(InsertionType.ASSUME, termNot(term));
        }

        if (succ && isEnsures(term)) {
            // special-case, an [assume] in the succedent (e.g. by applying teh notLeft taclet)
            return new InsertionTerm(InsertionType.ASSERT, term);
        }

        if (succ && isAssignable(term)) {
            return new InsertionTerm(InsertionType.ASSIGNABLE, term);
        }

        if (succ && isUserInteraction(term)) {
            // special-case, an [user_interaction] in the succedent (probably cut)
            return new InsertionTerm(InsertionType.ASSUME, termNot(term));
        }

        if (succ && isLoopInitiallyValid(term)) {
            // special-case, an [user_interaction] in the succedent (probably cut)
            return new InsertionTerm(InsertionType.ASSERT, term);
        }

        throw new TransformException("Failed to categorize term '" + term + "'");
    }

    private Term termNot(Term term) {
        Term result = svc.getTermBuilder().not(term);

        if (term.getOriginRef() != null && result.getOriginRef() == null) {
            result = svc.getTermFactory().setOriginRef(result,
                term.getOriginRef().WithMetadata(false, true));
        }

        return result;
    }

    private boolean isRequires(Term term) {
        if (term.containsJavaBlockRecursive())
            return false;

        var origins = getSubOriginRefs(term, true).stream()
                .filter(p -> p.IsAtom && p.Type != OriginRefType.UNKNOWN)
                .collect(Collectors.toList());
        if (origins.size() == 0)
            return false;

        return origins.stream().allMatch(p -> p.Type.isRequires());
    }

    private boolean isEnsures(Term term) {
        if (term.containsJavaBlockRecursive())
            return false;

        var origins = getSubOriginRefs(term, true).stream()
                .filter(p -> p.IsAtom && p.Type != OriginRefType.UNKNOWN)
                .collect(Collectors.toList());
        if (origins.size() == 0)
            return false;

        return origins.stream().allMatch(p -> p.Type.isEnsures());
    }

    private boolean isUserInteraction(Term term) {
        if (term.containsJavaBlockRecursive())
            return false;

        var origins = getSubOriginRefs(term, true).stream()
                .filter(p -> p.IsAtom && p.Type != OriginRefType.UNKNOWN)
                .collect(Collectors.toList());
        if (origins.size() == 0)
            return false;

        return origins.stream().allMatch(p -> p.Type.isUserInteraction());
    }

    private boolean isAssignable(Term term) {
        if (term.containsJavaBlockRecursive())
            return false;

        var origin = term.getOriginRef();
        if (origin == null)
            return false;
        if (origin.Type != OriginRefType.JML_ASSIGNABLE
                && origin.Type != OriginRefType.IMPLICIT_ENSURES_ASSIGNABLE)
            return false;

        if (term.op() != Quantifier.ALL)
            return false;
        if (term.sub(0).op() != Quantifier.ALL)
            return false;

        return true;
    }

    private boolean isLoopInitiallyValid(Term term) {
        if (term.containsJavaBlockRecursive())
            return false;

        var origins = getSubOriginRefs(term, true).stream()
                .filter(p -> p.IsAtom && p.Type != OriginRefType.UNKNOWN)
                .collect(Collectors.toList());
        if (origins.size() == 0)
            return false;

        return origins.stream().allMatch(p -> p.Type == OriginRefType.LOOP_INITIALLYVALID_INVARIANT || p.Type == OriginRefType.LOOP_INITIALLYVALID_WELLFORMED);
    }

    private ArrayList<OriginRef> getSubOriginRefs(Term term, boolean includeSelf) {
        ArrayList<OriginRef> r = new ArrayList<>();

        if (includeSelf) {
            if (term.getOriginRef() != null)
                r.add(term.getOriginRef());
        }

        for (Term t : term.subs()) {
            if (t instanceof TermImpl) {
                if (t.getOriginRef() != null)
                    r.add(t.getOriginRef());
                r.addAll(getSubOriginRefs(t, false));
            }
        }

        return r;
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
