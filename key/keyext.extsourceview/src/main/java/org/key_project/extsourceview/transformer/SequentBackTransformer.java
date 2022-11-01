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
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import org.key_project.util.collection.ImmutableList;

import java.sql.Array;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

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

    public InsertionSet extract() throws TransformException {
        var ante = extractAntecedentTerms();
        var succ = extractSuccedentTerms();

        var result = new ArrayList<InsertionTerm>();
        result.addAll(ante);
        result.addAll(succ);

        return new InsertionSet(ImmutableList.fromList(result));

    }

    public PositionMap generatePositionMap() throws TransformException {

        ContractPO contractPO = svc.getSpecificationRepository().getPOForProof(proof);

        if (!(contractPO instanceof FunctionalOperationContractPO)) {
            throw new TransformException("Can only work on functional contracts");
        }

        FunctionalOperationContractPO funContractPO = (FunctionalOperationContractPO)contractPO;

        FunctionalOperationContract contract = funContractPO.getContract();

        IProgramMethod progrMethod = contract.getTarget();

        PositionInfo pos = progrMethod.getPositionInfo();

        return new PositionMap(pos);
    }

    private ArrayList<InsertionTerm> extractAntecedentTerms() throws TransformException {
        ArrayList<InsertionTerm> result = new ArrayList<InsertionTerm>();

        for (SequentFormula sf: sequent.antecedent()) {

            Term topTerm = sf.formula();

            if (topTerm.containsJavaBlockRecursive()) throw new TransformException("Cannot transform antecedent formula with modularities");

            var split = splitFormula(topTerm, Junctor.AND);

            for (var term: split) {
                if (isRequires(term)) {
                    result.add(new InsertionTerm(InsertionType.REQUIRES, term));
                } else {
                    throw new TransformException("Failed to categorize antecedent-term '"+term+"'");
                }
            }
        }

        return result;
    }

    private ArrayList<InsertionTerm> extractSuccedentTerms() throws TransformException {
        ArrayList<InsertionTerm> result = new ArrayList<InsertionTerm>();

        TermBuilder tb = svc.getTermBuilder();

        boolean ensuresInResult = false;
        for (SequentFormula sf: sequent.succedent()) {

            Term topTerm = sf.formula();

            if (topTerm.containsJavaBlockRecursive()) throw new TransformException("Cannot transform succedent formula with modularities");

            var split = splitFormula(topTerm, Junctor.AND);

            boolean ensuresInSplit = false;
            for (var term: split) {
                if (isRequires(term)) {
                    result.add(new InsertionTerm(InsertionType.REQUIRES, tb.not(term)));
                } else if (isEnsures(term)) {
                    if (ensuresInResult) {
                        throw new TransformException("Cannot transform sequent with multiple 'real' succedents"); //TODO how to display?
                    }
                    result.add(new InsertionTerm(InsertionType.ENSURES, term));
                    ensuresInSplit = true;
                } else if (isAssignable(term)) {
                    if (ensuresInResult) {
                        throw new TransformException("Cannot transform sequent with multiple 'real' succedents"); //TODO how to display?
                    }
                    result.add(new InsertionTerm(InsertionType.ASSIGNABLE, term));
                    ensuresInSplit = true;
                } else {
                    throw new TransformException("Failed to categorize succedent-term '"+term+"'");
                }
            }
            if (ensuresInSplit) {
                ensuresInResult = true;
            }
        }

        return result;
    }

    private boolean isRequires(Term term) {
        if (term.containsJavaBlockRecursive()) return false;

        var origins = getSubOriginRefs(term, true);
        if (origins.size() == 0) return false;

        return origins.stream().allMatch(p -> p.Type.isRequires());
    }

    private boolean isEnsures(Term term) {
        if (term.containsJavaBlockRecursive()) return false;

        var origins = getSubOriginRefs(term, true);
        if (origins.size() == 0) return false;

        return origins.stream().allMatch(p -> p.Type.isEnsures());
    }

    private boolean isAssignable(Term term) {
        if (term.containsJavaBlockRecursive()) return false;

        var origin = term.getOriginRef();
        if (origin == null) return false;
        if (origin.Type != OriginRefType.JML_ASSIGNABLE && origin.Type != OriginRefType.IMPLICIT_ENSURES_ASSIGNABLE) return false;

        if (term.op() != Quantifier.ALL) return false;
        if (term.sub(0).op() != Quantifier.ALL) return false;

        return true;
    }

    private ArrayList<OriginRef> getSubOriginRefs(Term term, boolean includeSelf) {
        ArrayList<OriginRef> r = new ArrayList<>();

        if (includeSelf) {
            if (term.getOriginRef() != null) r.add(term.getOriginRef());
        }

        for (Term t : term.subs()) {
            if (t instanceof TermImpl) {
                if (t.getOriginRef() != null) r.add(t.getOriginRef());
                r.addAll(getSubOriginRefs(t, false));
            }
        }

        return r;
    }

    private List<Term> splitFormula(Term f, Operator j)  {
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
