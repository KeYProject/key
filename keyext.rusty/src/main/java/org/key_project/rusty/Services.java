/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty;


import java.util.HashMap;
import java.util.LinkedHashMap;

import org.key_project.logic.LogicServices;
import org.key_project.rusty.ldt.LDTs;
import org.key_project.rusty.logic.NamespaceSet;
import org.key_project.rusty.logic.TermBuilder;
import org.key_project.rusty.logic.TermFactory;
import org.key_project.rusty.proof.Counter;
import org.key_project.rusty.proof.Proof;
import org.key_project.rusty.proof.init.Profile;

public class Services implements LogicServices {
    /**
     * proof specific namespaces (functions, predicates, sorts, variables)
     */
    private NamespaceSet namespaces = new NamespaceSet(); // TODO ask Daniel; was final before
    private LDTs ldts;

    private final TermFactory tf;
    private final TermBuilder tb;

    private Proof proof;
    private Profile profile;

    /**
     * map of names to counters
     */
    private final HashMap<String, Counter> counters;

    public Services() {
        this.tf = new TermFactory();
        this.tb = new TermBuilder(tf, this);
        counters = new LinkedHashMap<>();
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

    public Services getOverlay(NamespaceSet localNamespaces) {
        Services result = new Services(this);
        result.setNamespaces(namespaces);
        return result;
    }
}
