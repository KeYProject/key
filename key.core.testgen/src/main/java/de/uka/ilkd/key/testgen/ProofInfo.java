/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.testgen;

import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.ast.declaration.VariableSpecification;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.pp.PosTableLayouter;
import de.uka.ilkd.key.pp.PrettyPrinter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.Contract.OriginalVariables;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;

import org.key_project.logic.op.Operator;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public record ProofInfo(Proof proof, Services services) {
    private static final Logger LOGGER = LoggerFactory.getLogger(ProofInfo.class);

    public ProofInfo(Proof proof) {
        this(proof, proof.getServices());
    }


    public @Nullable IProgramMethod getMUT() {
        SpecificationRepository spec = services.getSpecificationRepository();
        IObserverFunction f = spec.getTargetOfProof(proof);
        if (f instanceof IProgramMethod pm) {
            return pm;
        } else {
            return null;
        }
    }

    public @Nullable String getMUTCall() {
        var m = getMUT();
        if (m == null)
            return null;

        var name = m.getFullName();
        if (name == null)
            return null;

        StringBuilder params = new StringBuilder();
        ImmutableArray<ParameterDeclaration> paramDecls = m.getParameters();
        if (paramDecls == null) {
            throw new NullPointerException("Method under test has no parameter list.");
        }
        for (ParameterDeclaration p : paramDecls) {
            for (VariableSpecification v : p.getVariables()) {
                IProgramVariable pvar = v.getProgramVariable();
                params.append(",").append(pvar.name());
            }
        }
        if (!params.isEmpty()) {
            params = new StringBuilder(params.substring(1));
        }

        String caller;
        if (m.isStatic()) {
            KeYJavaType classUnderTest = getTypeOfClassUnderTest();
            if (classUnderTest == null) {
                throw new NullPointerException("No type of class under test.");
            }
            caller = classUnderTest.getName();
        } else {
            caller = "self";
        }

        KeYJavaType returnType = m.getReturnType();
        if (returnType == null) {
            throw new NullPointerException("Method under test has no return type.");
        }
        if (returnType.equals(KeYJavaType.VOID_TYPE)) {
            return caller + "." + name + "(" + params + ");";
        } else {
            String returnTypeName = returnType.getFullName();
            return returnTypeName + " result = " + caller + "." + name + "(" + params + ");";
        }
    }

    public @Nullable KeYJavaType getTypeOfClassUnderTest() {
        IProgramMethod mut = getMUT();
        if (mut == null) {
            return null;
        }
        return mut.getContainerType();
    }

    public @Nullable KeYJavaType getReturnType() {
        var mut = getMUT();
        return mut != null ? mut.getType() : null;
    }

    public Contract getContract() {
        ContractPO po = services.getSpecificationRepository().getPOForProof(proof);
        if (po == null) {
            throw new NullPointerException("No proof obligation available for the proof.");
        }
        return po.getContract();
    }

    public JTerm getPostCondition() {
        JTerm t = getPO();
        JTerm post = services.getTermBuilder().tt();
        try {
            post = t.sub(1).sub(1).sub(0);
        } catch (Exception e) {
            LOGGER.warn("Could not get PostCondition", e);
        }

        return post;
    }

    public JTerm getPreConTerm() {
        Contract c = getContract();
        if (c instanceof FunctionalOperationContract t) {
            OriginalVariables orig = t.getOrigVars();
            HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
            if (heapLDT == null) {
                throw new NullPointerException(
                    "No heap type defined in the services type converter.");
            }
            JTerm pre = t.getPre(heapLDT.getHeap(), orig.self, orig.params, orig.atPres, services);
            if (pre == null) {
                throw new NullPointerException("No precondition available for the contract.");
            }
            return pre;
        }
        // no pre <==> false
        return services.getTermBuilder().ff();
    }

    public JTerm getModifiable() {
        Contract c = getContract();
        HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        if (heapLDT == null) {
            throw new NullPointerException("No heap type defined in the services type converter.");
        }
        JTerm modifiable = c.getModifiable(heapLDT.getHeap());
        if (modifiable == null) {
            throw new NullPointerException("No modifies clause available for the contract.");
        }
        return modifiable;
    }

    public String getCode() {
        JTerm f = getPO();
        JavaBlock block = getJavaBlock(f);
        if (block == null) {
            throw new NullPointerException("No Java block found in the proof obligation.");
        }

        PosTableLayouter l = PosTableLayouter.pure();
        l.beginC(0);
        l.print(" ").print(getUpdate(f)).nl();
        PrettyPrinter p = new PrettyPrinter(l);
        block.program().visit(p);
        l.end();
        return p.result();
    }

    public void getProgramVariables(JTerm t, Set<JTerm> vars) {
        if (t.op() instanceof ProgramVariable && isRelevantConstant(t)) {
            vars.add(TermLabelManager.removeIrrelevantLabels(t, services));
        }

        for (JTerm sub : t.subs()) {
            getProgramVariables(sub, vars);
        }
    }

    private boolean isRelevantConstant(JTerm c) {
        Operator op = c.op();

        if (isTrueConstant(op) || isFalseConstant(op)) {
            return false;
        }

        Sort s = c.sort();

        Sort nullSort = services.getJavaInfo().getNullType().getSort();
        Sort objSort = services.getJavaInfo().getJavaLangObject().getSort();
        if (objSort == null) {
            throw new NullPointerException("No sort for java.lang.Object.");
        }
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

    public JTerm getPO() {
        Node root = proof.root();
        if (root == null) {
            throw new NullPointerException("Proof has no root node.");
        }
        return (JTerm) root.sequent().succedent().get(0).formula();
    }


    public String getUpdate(JTerm t) {
        if (t.op() instanceof UpdateApplication) {
            return processUpdate(UpdateApplication.getUpdate(t));
        } else {
            StringBuilder result = new StringBuilder();
            for (JTerm s : t.subs()) {
                result.append(getUpdate(s));
            }
            return result.toString();
        }

    }


    private String processUpdate(JTerm update) {
        if (update.op() instanceof ElementaryUpdate up) {
            HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
            if (heapLDT == null) {
                throw new NullPointerException(
                    "No heap type defined in the services type converter.");
            }
            if (up.lhs().sort().extendsTrans(heapLDT.targetSort())) {
                return "";
            }
            return "   \n" + up.lhs().sort() + " " + up.lhs().toString() + " = " + update.sub(0)
                + ";";
        }
        StringBuilder result = new StringBuilder();
        for (JTerm sub : update.subs()) {
            result.append(processUpdate(sub));
        }
        return result.toString();
    }

    public @Nullable JavaBlock getJavaBlock(JTerm t) {
        if (t.containsJavaBlockRecursive()) {
            if (!t.javaBlock().isEmpty()) {
                return t.javaBlock();
            } else {
                for (JTerm s : t.subs()) {
                    if (s.containsJavaBlockRecursive()) {
                        return getJavaBlock(s);
                    }
                }
            }
        }
        return null;
    }
}
