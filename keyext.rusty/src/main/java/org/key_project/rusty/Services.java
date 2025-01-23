/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty;


import java.util.HashMap;
import java.util.LinkedHashMap;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.ast.expr.BinaryExpression;
import org.key_project.rusty.ast.expr.LiteralExpression;
import org.key_project.rusty.ldt.LDT;
import org.key_project.rusty.ldt.LDTs;
import org.key_project.rusty.logic.*;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.proof.Counter;
import org.key_project.rusty.proof.NameRecorder;
import org.key_project.rusty.proof.Proof;
import org.key_project.rusty.proof.RustModel;
import org.key_project.rusty.proof.init.Profile;
import org.key_project.rusty.proof.mgt.SpecificationRepository;

public class Services implements LogicServices {
    /**
     * proof specific namespaces (functions, predicates, sorts, variables)
     */
    private NamespaceSet namespaces = new NamespaceSet();
    private LDTs ldts;
    private RefSortManager mRefManager;
    private RustInfo rustInfo;
    private NameRecorder nameRecorder;

    private final TermFactory tf;
    private final TermBuilder tb;

    private Proof proof;
    private Profile profile;

    private final ServiceCaches caches;
    /**
     * specification repository
     */
    private SpecificationRepository specRepos;

    /**
     * variable namer for inner renaming
     */
    private final VariableNamer innerVarNamer = new InnerVariableNamer(this);

    /**
     * map of names to counters
     */
    private final HashMap<String, Counter> counters;
    private RustModel rustModel;

    public Services() {
        this.tf = new TermFactory();
        this.tb = new TermBuilder(tf, this);
        this.specRepos = new SpecificationRepository(this);
        this.caches = new ServiceCaches();
        counters = new LinkedHashMap<>();
        mRefManager = new RefSortManager(this);
        rustInfo = new RustInfo(this);
        nameRecorder = new NameRecorder();
    }

    public Services(Profile profile) {
        this();
        assert profile != null;
        this.profile = profile;
    }

    public Services(Services services) {
        this.namespaces = services.namespaces;
        this.ldts = services.ldts;
        this.tf = services.tf;
        this.tb = services.tb;
        this.proof = services.proof;
        this.profile = services.profile;
        this.counters = services.counters;
        this.mRefManager = services.mRefManager;
        this.caches = services.caches;
        this.specRepos = services.specRepos;
        this.rustModel = services.rustModel;
        rustInfo = services.rustInfo;
        nameRecorder = services.nameRecorder;
    }

    public NamespaceSet getNamespaces() {
        return namespaces;
    }

    public void setNamespaces(NamespaceSet namespaces) {
        this.namespaces = namespaces;
    }

    public TermBuilder getTermBuilder() {
        return tb;
    }

    public TermFactory getTermFactory() {
        return tf;
    }

    public RefSortManager getMRefManager() {
        return mRefManager;
    }

    public void initLDTs() {
        ldts = new LDTs(this);
    }

    public LDTs getLDTs() {
        return ldts;
    }

    public void setLDTs(LDTs ldts) {
        this.ldts = ldts;
    }

    public Proof getProof() {
        return proof;
    }

    public void setProof(Proof proof) {
        this.proof = proof;
    }

    public Profile getProfile() {
        return profile;
    }

    /**
     * returns an existing named counter, creates a new one otherwise
     */
    public Counter getCounter(String name) {
        Counter c = counters.get(name);
        if (c != null) {
            return c;
        }
        c = new Counter(name);
        counters.put(name, c);
        return c;
    }

    /**
     * Reset all counters associated with this service.
     * Only use this method if the proof is empty!
     */
    public void resetCounters() {
        if (proof.root().childrenCount() > 0) {
            throw new IllegalStateException("tried to reset counters on non-empty proof");
        }
        counters.clear();
    }

    /**
     * creates a new service object with the same ldt information as the actual one
     */
    public Services copyPreservesLDTInformation() {
        Services s = new Services(getProfile());
        s.setLDTs(getLDTs());
        s.setNamespaces(namespaces.copy());
        return s;
    }

    public Services getOverlay(NamespaceSet namespaces) {
        Services result = new Services(this);
        result.setNamespaces(namespaces);
        return result;
    }

    public VariableNamer getVariableNamer() {
        return innerVarNamer;
    }

    public void addNameProposal(Name name) {
        // TODO @ DD
    }

    public RustInfo getRustInfo() {
        return rustInfo;
    }

    public ServiceCaches getCaches() {
        return caches;
    }

    public SpecificationRepository getSpecificationRepository() {
        return specRepos;
    }

    public Term convertToLogicElement(RustyProgramElement pe) {
        return convertToLogicElement(pe, this);
    }

    public static Term convertToLogicElement(RustyProgramElement pe, Services services) {
        var tb = services.getTermBuilder();
        if (pe instanceof ProgramVariable pv) {
            return tb.var(pv);
        }
        if (pe instanceof LiteralExpression lit) {
            return convertLiteralExpression(lit, services);
        }
        if (pe instanceof BinaryExpression ale) {
            return convertBinaryExpression(ale, services);
        }
        throw new IllegalArgumentException(
            "Unknown or not convertible ProgramElement " + pe + " of type "
                + pe.getClass());
    }

    public static Term convertBinaryExpression(BinaryExpression ale,
            Services services) {
        var tb = services.getTermBuilder();
        final var subs = new Term[] { convertToLogicElement(ale.left(), services),
            convertToLogicElement(ale.right(), services) };

        var op = ale.op();
        var responsibleLDT = getResponsibleLDT(op, subs, services);
        if (responsibleLDT != null) {
            return tb.func(responsibleLDT.getFunctionFor(op, services), subs);
        }
        throw new IllegalArgumentException(
            "could not handle" + " this operator: " + op);
    }

    public static LDT getResponsibleLDT(BinaryExpression.Operator op, Term[] subs,
            Services services) {
        for (LDT ldt : services.getLDTs()) {
            if (ldt.isResponsible(op, subs, services)) {
                return ldt;
            }
        }
        return null;
    }

    public static Term convertLiteralExpression(LiteralExpression lit, Services services) {
        LDT ldt = services.getLDTs().get(lit.getLDTName());
        if (ldt != null) {
            return ldt.translateLiteral(lit, services);
        } else {
            return null;
        }
    }

    public NameRecorder getNameRecorder() {
        return nameRecorder;
    }

    public Services copy() {
        return copy(getProfile());
    }

    public Services copy(Profile profile) {
        var s = new Services(profile);
        s.specRepos = specRepos;
        s.setLDTs(getLDTs());
        s.setNamespaces(namespaces.copy());
        s.setRustModel(getRustModel());
        nameRecorder = nameRecorder.copy();
        return s;
    }

    public RustModel getRustModel() {
        return rustModel;
    }

    public void setRustModel(RustModel rustModel) {
        this.rustModel = rustModel;
    }
}
