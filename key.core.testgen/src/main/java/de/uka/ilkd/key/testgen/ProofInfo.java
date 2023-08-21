/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen;

import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.PosTableLayouter;
import de.uka.ilkd.key.pp.PrettyPrinter;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.Contract.OriginalVariables;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class ProofInfo {
    private static final Logger LOGGER = LoggerFactory.getLogger(ProofInfo.class);

    private final Proof proof;

    private final Services services;

    public ProofInfo(Proof proof) {
        this.proof = proof;
        this.services = proof.getServices();
    }

    public IProgramMethod getMUT() {
        SpecificationRepository spec = services.getSpecificationRepository();
        IObserverFunction f = spec.getTargetOfProof(proof);
        if (f instanceof IProgramMethod) {
            return (IProgramMethod) f;
        } else {
            return null;
        }
    }

    public KeYJavaType getTypeOfClassUnderTest() {
        if (getMUT() == null) {
            return null;
        }
        return getMUT().getContainerType();
    }

    public KeYJavaType getReturnType() {
        return getMUT().getType();
    }

    public Contract getContract() {
        ContractPO po = services.getSpecificationRepository().getPOForProof(proof);
        return po.getContract();
    }

    public Term getPostCondition() {
        Term t = getPO();
        Term post = services.getTermBuilder().tt();
        try {
            post = t.sub(1).sub(1).sub(0);
        } catch (Exception e) {
            LOGGER.warn("Could not get PostCondition", e);
        }

        return post;
    }

    public Term getPreConTerm() {
        Contract c = getContract();
        if (c instanceof FunctionalOperationContract) {
            FunctionalOperationContract t = (FunctionalOperationContract) c;
            OriginalVariables orig = t.getOrigVars();
            Term post = t.getPre(services.getTypeConverter().getHeapLDT().getHeap(), orig.self,
                orig.params, orig.atPres, services);
            return post;
        }
        // no pre <==> false
        return services.getTermBuilder().ff();
    }

    public Term getAssignable() {
        Contract c = getContract();
        return c.getAssignable(services.getTypeConverter().getHeapLDT().getHeap());
    }

    public String getCode() {
        Term f = getPO();
        JavaBlock block = getJavaBlock(f);

        PosTableLayouter l = PosTableLayouter.pure();
        l.beginC(0);
        l.print(" ").print(getUpdate(f)).nl();
        PrettyPrinter p = new PrettyPrinter(l);
        block.program().visit(p);
        l.end();
        return p.result();
    }

    public void getProgramVariables(Term t, Set<Term> vars) {
        if (t.op() instanceof ProgramVariable && isRelevantConstant(t)) {
            vars.add(TermLabel.removeIrrelevantLabels(t, services));
        }

        for (Term sub : t.subs()) {
            getProgramVariables(sub, vars);
        }
    }

    private boolean isRelevantConstant(Term c) {
        Operator op = c.op();

        if (isTrueConstant(op) || isFalseConstant(op)) {
            return false;
        }

        Sort s = c.sort();

        Sort nullSort = services.getJavaInfo().getNullType().getSort();
        Sort objSort = services.getJavaInfo().getJavaLangObject().getSort();
        Sort intSort = services.getTypeConverter().getIntegerLDT().targetSort();
        Sort boolSort = services.getTypeConverter().getBooleanLDT().targetSort();

        if (s.equals(nullSort)) {
            return false;
        }

        return s.extendsTrans(objSort) || s.equals(intSort) || s.equals(boolSort);

    }

    private boolean isTrueConstant(Operator o) {
        return o.equals(services.getTypeConverter().getBooleanLDT().getTrueConst());
    }

    private boolean isFalseConstant(Operator o) {
        return o.equals(services.getTypeConverter().getBooleanLDT().getFalseConst());
    }

    public Term getPO() {
        return proof.root().sequent().succedent().get(0).formula();
    }


    public String getUpdate(Term t) {
        if (t.op() instanceof UpdateApplication) {
            return processUpdate(UpdateApplication.getUpdate(t));
        } else {
            StringBuilder result = new StringBuilder();
            for (Term s : t.subs()) {
                result.append(getUpdate(s));
            }
            return result.toString();
        }

    }


    private String processUpdate(Term update) {
        if (update.op() instanceof ElementaryUpdate) {
            ElementaryUpdate up = (ElementaryUpdate) update.op();
            if (up.lhs().sort()
                    .extendsTrans(services.getTypeConverter().getHeapLDT().targetSort())) {
                return "";
            }
            return "   \n" + up.lhs().sort() + " " + up.lhs().toString() + " = " + update.sub(0)
                + ";";
        }
        StringBuilder result = new StringBuilder();
        for (Term sub : update.subs()) {
            result.append(processUpdate(sub));
        }
        return result.toString();
    }

    public JavaBlock getJavaBlock(Term t) {
        if (t.containsJavaBlockRecursive()) {
            if (!t.javaBlock().isEmpty()) {
                return t.javaBlock();
            } else {
                for (Term s : t.subs()) {
                    if (s.containsJavaBlockRecursive()) {
                        return getJavaBlock(s);
                    }
                }
            }
        }
        return null;
    }
}
