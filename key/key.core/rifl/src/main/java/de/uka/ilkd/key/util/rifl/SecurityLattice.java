package de.uka.ilkd.key.util.rifl;

import java.util.Set;
import java.util.HashSet;

/**
 * A lattice of security domains in RIFL.
 * While the lattice is not necessarily complete, there are distinct top and bottom elements.
 * Instances of this class are mutable; new domains can be added and put into a hierarchy.
 * However, in any state the integrity is checked (top/bottom, acyclicity).
 */
public class SecurityLattice {

    private static final String TOP = "top";
    private static final String BOTTOM = "bottom";

    private final SecurityDomain top;
    private final SecurityDomain bottom;
    private final Set<SecurityDomain> hash = new HashSet<SecurityDomain>();

    /**
     * Creates a two-element lattice.
     */
    public SecurityLattice () {
        top = new SecurityDomain(TOP);
        bottom = new SecurityDomain(BOTTOM);
        top.putSubDomain(bottom);
        hash.add(top);
        hash.add(bottom);
    }

    /**
     * Creates a new security domain and adds it to the lattice.
     * The new domain is a direct subdomain of top and direct super-domain of bottom.
     * @param name name of the new domain (must not be "top" or "bottom")
     * @return the new domain
     */
    SecurityDomain addDomain(String name) {
        SecurityDomain d = new SecurityDomain(name.intern());
        if (hash.contains(d))
            throw new IllegalArgumentException("Domain already in lattice (names must be unique)");
        d.putSubDomain(bottom);
        top.putSubDomain(d);
        hash.add(d);
        return d;
    }

    /**
     * Refine the lattice by declaring a sub-domain relation between two domains.
     * This checks whether the domains are already in the lattice and that the lattice is still acyclic.
     */
    void putSubDomain(SecurityDomain sup, SecurityDomain sub) {
        if (sup == top || sub == bottom) return; // safely ignore this
        if ( ! hash.contains(sup))
            throw new IllegalArgumentException("Security domain "+sup+" must be added to the lattice first.");
        if ( ! hash.contains(sub))
            throw new IllegalArgumentException("Security domain "+sub+" must be added to the lattice first.");
        if (sup == sub || sub.isSuperDomain(sup))
            throw new IllegalArgumentException("Security lattice must be acyclic.");
        sup.putSubDomain(sub);
    }

    public SecurityDomain top() { return top; }
    public SecurityDomain bottom() { return bottom; }
    public boolean contains(SecurityDomain d) { return hash.contains(d); }


    /**
     * The kind of elements to the security lattice.
     * Keeps track of <i>direct</i> super- and sub-elements.
     * Instances are mutable, but only by the lattice owning it.
     */
    public final class SecurityDomain {

        private final String name;
        private Set<SecurityDomain> superDomains;
        private Set<SecurityDomain> subDomains;

        private SecurityDomain(String name) {
            this.name = name;
            superDomains = new HashSet<SecurityDomain>();
            subDomains = new HashSet<SecurityDomain>();
        }

        private void putSubDomain(SecurityDomain sub) {
            subDomains.add(sub);
            sub.superDomains.add(this);
        }

        /**
         * Returns whether this domain is strictly higher in the hierarchy than the other one.
         */
        // TODO: do we really want strict super-elements??
        public boolean isSuperDomain(SecurityDomain other) {
            if (other == this) return false;
            for (SecurityDomain sub: subDomains) {
                if (sub == other || sub.isSuperDomain(other)) return true;
            }
            return false;
        }

        /**
         * Returns whether this domain is strictly lower in the hierarchy than the other one.
         */
        public boolean isSubDomain(SecurityDomain other) {
            if (other == this) return false;
            for (SecurityDomain sup: superDomains) {
                if (sup == other || sup.isSubDomain(other)) return true;
            }
            return false;
        }

        @Override
        public String toString () { return name; }

        // ensures unique names
        @Override
        public int hashCode () { return name.hashCode(); }
    }
}