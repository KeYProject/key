/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty;


import org.key_project.rusty.ldt.LDTs;
import org.key_project.rusty.logic.NamespaceSet;
import org.key_project.rusty.logic.TermBuilder;
import org.key_project.rusty.logic.TermFactory;
import org.key_project.rusty.proof.Proof;
import org.key_project.rusty.proof.init.Profile;

public class Services {
    /**
     * proof specific namespaces (functions, predicates, sorts, variables)
     */
    private final NamespaceSet namespaces = new NamespaceSet();
    private LDTs ldts;

    private final TermFactory tf;
    private final TermBuilder tb;

    private Proof proof;
    private Profile profile;

    public Services() {
        this.tf = new TermFactory();
        this.tb = new TermBuilder(tf, this);
    }

    public Services(Profile profile) {
        this();
        this.profile = profile;
    }

    public NamespaceSet getNamespaces() {
        return namespaces;
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

    public Proof getProof() {
        return proof;
    }

    public void setProof(Proof proof) {
        this.proof = proof;
    }

    public Profile getProfile() {
        return profile;
    }
}
