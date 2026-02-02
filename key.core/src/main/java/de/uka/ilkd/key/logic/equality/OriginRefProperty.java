package de.uka.ilkd.key.logic.equality;

import de.uka.ilkd.key.logic.JTerm;
import org.key_project.logic.Property;
import org.key_project.util.collection.ImmutableArray;

/**
 * Equality comparison without originRefs (aka "equalsModOrigins").
 */
public class OriginRefProperty implements Property<JTerm>  {
    /**
     * The single instance of this property.
     */
    public static final OriginRefProperty ORIGIN_REF_PROPERTY =
        new OriginRefProperty();

    private OriginRefProperty() {
    }

    @Override
    public <V> boolean equalsModThisProperty(JTerm term1, JTerm term2, V... v) {
        if (term2 == term1) {
            return true;
        }

        if (term1 == null || term2 == null || term1.getClass() != term2.getClass()) {
            return false;
        }

        if (!(term1.op().equals(term2.op()) && term1.boundVars().equals(term2.boundVars())
            && term1.javaBlock().equals(term2.javaBlock()))) {
            return false;
        }

        // Note: everything regarding origin refs is ignored for comparison

        final ImmutableArray<JTerm> termSubs = term1.subs();
        final ImmutableArray<JTerm> term2Subs = term2.subs();
        final int numOfSubs = termSubs.size();
        for (int i = 0; i < numOfSubs; ++i) {
            if (!termSubs.get(i).equalsModProperty(term2Subs.get(i),
                ORIGIN_REF_PROPERTY)) {
                return false;
            }
        }

        return true;
    }

    @Override
    public int hashCodeModThisProperty(JTerm jTerm) {
        int hashcode = 5;
        hashcode = hashcode * 17 + jTerm.op().hashCode();
        hashcode = hashcode * 17 + jTerm.subs().hashCode();
        hashcode = hashcode * 17 + jTerm.boundVars().hashCode();
        hashcode = hashcode * 17 + jTerm.javaBlock().hashCode();

        // ignore originRefs
        //hashcode = hashcode * 7 + ((jTerm.getOriginRef() != null) ? jTerm.getOriginRef().hashCode() : 0);

        if (hashcode == -1) {
            hashcode = 0;
        }
        return hashcode;
    }
}
