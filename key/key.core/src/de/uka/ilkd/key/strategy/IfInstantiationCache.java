package de.uka.ilkd.key.strategy;

import java.util.HashMap;
import java.util.LinkedHashMap;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;

/**
 * Direct-mapped cache of lists of formulas (potential instantiations of
 * if-formulas of taclets) that were modified after a certain point of time
 * 
 * Hashmaps of the particular lists of formulas; the keys of the maps is the
 * point of time that separates old from new (modified) formulas
 *
 * Keys: Long Values: IList<IfFormulaInstantiation>
 */
class IfInstantiationCache {
    public Node cacheKey = null;

    public final HashMap<Long, ImmutableList<IfFormulaInstantiation>> antecCache = new LinkedHashMap<>();
    public final HashMap<Long, ImmutableList<IfFormulaInstantiation>> succCache = new LinkedHashMap<>();

    /**This field causes a memory leak (that is ad-hoc-ly fixed in
     * QueueRuleApplicationManager.clearCache()) because it is static and it
     * has a reference to node which has again a reference to proof.
     * Can this field be made non-static by putting it in some other class?
     * This field was private before the fix*/
    public static final IfInstantiationCache ifInstCache = new IfInstantiationCache ();

    public void reset(Node n) {
        cacheKey = n;
        antecCache.clear();
        succCache.clear();
    }
}