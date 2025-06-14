/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.dl.translation;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.declaration.modifier.Private;
import de.uka.ilkd.key.java.statement.CatchAllStatement;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.JModality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.ClassInvariantImpl;
import de.uka.ilkd.key.speclang.ContractFactory;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;


/**
 * A factory for creating class invariants and operation contracts from DL specifications. For an
 * example, see java_dl/DLContractChooser.
 */
public final class DLSpecFactory {
    private final Services services;


    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public DLSpecFactory(Services services) {
        assert services != null;
        this.services = services;
    }



    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    private JTerm extractPre(JTerm fma) throws ProofInputException {
        if (!fma.op().equals(Junctor.IMP)) {
            throw new ProofInputException("Implication expected");
        } else {
            return fma.sub(0);
        }
    }


    private LocationVariable extractHeapAtPre(JTerm fma) throws ProofInputException {
        if (fma.sub(1).op() instanceof UpdateApplication) {
            final JTerm update = fma.sub(1).sub(0);
            assert update.sort() == JavaDLTheory.UPDATE;
            if (!(update.op() instanceof ElementaryUpdate eu)) {
                throw new ProofInputException(
                    "Elementary update expected, " + "but found: " + update);
            }
            if (!(eu.lhs() instanceof ProgramVariable)) {
                throw new ProofInputException(
                    "Program variable expected, " + "but found: " + eu.lhs());
            } else if (!update.sub(0).equals(services.getTermBuilder().getBaseHeap())) {
                throw new ProofInputException("heap expected, " + "but found: " + update.sub(0));
            } else {
                return (LocationVariable) eu.lhs();
            }
        } else {
            return null;
        }
    }


    private LocationVariable extractExcVar(JTerm fma) {
        final JTerm modFma =
            fma.sub(1).op() instanceof UpdateApplication ? fma.sub(1).sub(1) : fma.sub(1);

        final SourceElement se = modFma.javaBlock().program().getFirstElement();
        if (se instanceof CatchAllStatement) {
            return ((CatchAllStatement) se).getParam();
        } else {
            return null;
        }
    }


    private UseOperationContractRule.Instantiation extractInst(JTerm fma)
            throws ProofInputException {
        final UseOperationContractRule.Instantiation result =
            UseOperationContractRule.computeInstantiation(fma.sub(1), services);
        if (result == null) {
            throw new ProofInputException("Contract formula of wrong shape: " + fma.sub(1));
        }

        return result;
    }


    private IProgramMethod extractProgramMethod(UseOperationContractRule.Instantiation inst)
            throws ProofInputException {
        return inst.pm;
    }


    private JModality.JavaModalityKind extractModalityKind(
            UseOperationContractRule.Instantiation inst)
            throws ProofInputException {
        return inst.modality.kind();
    }


    private LocationVariable extractSelfVar(UseOperationContractRule.Instantiation inst)
            throws ProofInputException {
        if (inst.actualSelf == null) {
            assert inst.pm.isStatic();
            return null;
        } else if (inst.actualSelf.op() instanceof LocationVariable lv) {
            return lv;
        } else {
            throw new ProofInputException(
                "Program variable expected, " + "but found: " + inst.actualSelf);
        }
    }


    private ImmutableList<LocationVariable> extractParamVars(
            UseOperationContractRule.Instantiation inst) throws ProofInputException {
        ImmutableList<LocationVariable> result = ImmutableSLList.nil();
        for (JTerm param : inst.actualParams) {
            if (param.op() instanceof LocationVariable lv) {
                result = result.append(lv);
            } else {
                throw new ProofInputException(
                    "Program variable expected, " + "but found: " + param);
            }
        }
        return result;
    }


    private LocationVariable extractResultVar(UseOperationContractRule.Instantiation inst)
            throws ProofInputException {
        if (inst.actualResult == null) {
            return null;
        } else if (inst.actualResult instanceof LocationVariable lv) {
            return lv;
        } else {
            throw new ProofInputException(
                "Program variable expected, " + "but found: " + inst.actualResult);
        }
    }


    private JTerm extractPost(JTerm fma) {
        final JTerm modFma =
            fma.sub(1).op() instanceof UpdateApplication ? fma.sub(1).sub(1) : fma.sub(1);
        return modFma.sub(0);
    }



    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    /**
     * Creates a class invariant from a formula and a designated "self".
     */
    public ClassInvariant createDLClassInvariant(String name, String displayName,
            LocationVariable selfVar, JTerm inv) throws ProofInputException {
        assert name != null;
        if (displayName == null) {
            displayName = name;
        }
        assert selfVar != null;
        assert inv != null;

        final KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(selfVar.sort());
        assert kjt != null;

        return new ClassInvariantImpl(name, displayName, kjt, new Private(), inv, selfVar);
    }


    /**
     * Creates an operation contract from an implication formula of the form "pre -> {heapAtPre :=
     * heap} [#catchAll(java.lang.Throwable exc){m();}]post", (where the update and/or the #catchAll
     * may be omitted) and a modifiable clause.
     */
    public FunctionalOperationContract createDLOperationContract(String name, JTerm fma,
            JTerm modifiable) throws ProofInputException {
        assert name != null;
        assert fma != null;
        assert modifiable != null;

        final ContractFactory cf = new ContractFactory(services);

        // extract parts of fma
        final JTerm pre = extractPre(fma);
        LocationVariable heapAtPreVar = extractHeapAtPre(fma);
        LocationVariable excVar = extractExcVar(fma);
        final UseOperationContractRule.Instantiation inst = extractInst(fma);
        final IProgramMethod pm = extractProgramMethod(inst);
        final JModality.JavaModalityKind modalityKind = extractModalityKind(inst);
        final LocationVariable selfVar =
            pm.isConstructor() ? extractResultVar(inst) : extractSelfVar(inst);
        final ImmutableList<LocationVariable> paramVars = extractParamVars(inst);
        LocationVariable resultVar = pm.isConstructor() ? null : extractResultVar(inst);
        JTerm post = extractPost(fma);

        // heapAtPre must not occur in precondition or in modifiables clause
        if (heapAtPreVar != null) {
            final OpCollector oc = new OpCollector();
            pre.execPostOrder(oc);

            modifiable.execPostOrder(oc);

            if (oc.contains(heapAtPreVar)) {
                throw new ProofInputException(
                    "variable \"" + heapAtPreVar + "\" used for pre-state heap"
                        + " must not occur in precondition or in modifiable clause");
            }
        }

        HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        // heapAtPre variable may be omitted
        TermBuilder tb = services.getTermBuilder();
        if (heapAtPreVar == null) {
            heapAtPreVar =
                tb.atPreVar(heapLDT.getHeap().toString(), heapLDT.getHeap().sort(), false);
        }
        Map<LocationVariable, LocationVariable> atPreVars =
            new LinkedHashMap<>();
        atPreVars.put(heapLDT.getHeap(), heapAtPreVar);
        Map<LocationVariable, JTerm> modifiables = new LinkedHashMap<>();
        modifiables.put(heapLDT.getHeap(), modifiable);

        // result variable may be omitted
        if (resultVar == null && !pm.isVoid()) {
            resultVar = tb.resultVar(pm, false);
        }

        // exception variable may be omitted
        if (excVar == null) {
            excVar = tb.excVar(pm, false);
            JTerm excNullTerm = tb.equals(tb.var(excVar), tb.NULL());
            if (modalityKind == JModality.JavaModalityKind.DIA) {
                post = tb.and(post, excNullTerm);
            } else if (modalityKind == JModality.JavaModalityKind.BOX) {
                post = tb.or(post, tb.not(excNullTerm));
            } else {
                throw new ProofInputException("unknown semantics for exceptional termination: "
                    + modalityKind.name() + "; please use #catchAll block");
            }
        }

        Map<LocationVariable, JTerm> pres = new LinkedHashMap<>();
        pres.put(heapLDT.getHeap(), pre);

        Map<LocationVariable, JTerm> posts = new LinkedHashMap<>();
        posts.put(heapLDT.getHeap(), post);

        Map<LocationVariable, Boolean> hasModifiable = new LinkedHashMap<>();
        hasModifiable.put(heapLDT.getHeap(), modifiable.op() != tb.ff().op());
        for (LocationVariable h : heapLDT.getAllHeaps()) {
            if (h != heapLDT.getHeap()) {
                hasModifiable.put(heapLDT.getSavedHeap(), true); // different heaps not supported
                                                                 // yet in DL contracts
            }
        }

        final boolean isLibraryClass =
            ((TypeDeclaration) pm.getContainerType().getJavaType()).isLibraryClass();
        return cf.func(name, pm.getContainerType(), pm, modalityKind, pres,
            new LinkedHashMap<>(), null, // TODO measured_by in DL contracts
                                         // not supported yet
            posts, new LinkedHashMap<>(), null, // TODO no model methods in DL
                                                // contracts
            modifiables, new LinkedHashMap<>(),
            new LinkedHashMap<>(),
            hasModifiable, new LinkedHashMap<>(), // TODO strictly pure in DL
            // contracts not supported yet
            selfVar, paramVars, resultVar, excVar, atPreVars, !isLibraryClass);
    }
}
