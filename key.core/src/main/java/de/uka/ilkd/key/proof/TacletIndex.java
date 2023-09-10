/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import java.util.*;
import javax.annotation.Nullable;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.proof.rulefilter.RuleFilter;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

/**
 * manages all applicable Taclets (more precisely: Taclets with instantiations but without position
 * information, the NoPosTacletApps) at one node. It is a persistent implementation. Taclets can be
 * added because the Taclets allow to introduce new rules during runtime. It offers selective get
 * methods for different kinds of rules.
 */
public abstract class TacletIndex {

    private static final Object DEFAULT_SV_KEY = new Object();
    private static final Object DEFAULT_PROGSV_KEY = new Object();

    /** contains rewrite Taclets */
    protected HashMap<Object, ImmutableList<NoPosTacletApp>> rwList = new LinkedHashMap<>();

    /** contains antecedent Taclets */
    protected HashMap<Object, ImmutableList<NoPosTacletApp>> antecList = new LinkedHashMap<>();

    /** contains succedent Taclets */
    protected HashMap<Object, ImmutableList<NoPosTacletApp>> succList = new LinkedHashMap<>();

    /** contains NoFind-Taclets */
    protected ImmutableList<NoPosTacletApp> noFindList = ImmutableSLList.nil();

    /**
     * keeps track of no pos taclet apps with partial instantiations
     */
    protected HashSet<NoPosTacletApp> partialInstantiatedRuleApps = new LinkedHashSet<>();


    /** constructs empty rule index */
    TacletIndex() {
    }

    /**
     * creates a new TacletIndex with the given Taclets as initial contents.
     */
    TacletIndex(Iterable<Taclet> tacletSet) {
        rwList = new LinkedHashMap<>();
        antecList = new LinkedHashMap<>();
        succList = new LinkedHashMap<>();
        noFindList = ImmutableSLList.nil();
        addTaclets(toNoPosTacletApp(tacletSet));
    }

    protected TacletIndex(HashMap<Object, ImmutableList<NoPosTacletApp>> rwList,
            HashMap<Object, ImmutableList<NoPosTacletApp>> antecList,
            HashMap<Object, ImmutableList<NoPosTacletApp>> succList,
            ImmutableList<NoPosTacletApp> noFindList,
            HashSet<NoPosTacletApp> partialInstantiatedRuleApps) {
        this.rwList = rwList;
        this.antecList = antecList;
        this.succList = succList;
        this.noFindList = noFindList;
        this.partialInstantiatedRuleApps = partialInstantiatedRuleApps;
    }


    private static Object getIndexObj(FindTaclet tac) {
        Object indexObj;
        final Term indexTerm = tac.find();
        if (!indexTerm.javaBlock().isEmpty()) {
            final JavaProgramElement prg = indexTerm.javaBlock().program();
            indexObj = ((StatementBlock) prg).getStatementAt(0);
            if (!(indexObj instanceof SchemaVariable)) {
                indexObj = indexObj.getClass();
            }
        } else {
            indexObj = indexTerm.op();
            if (indexObj instanceof SortDependingFunction) {
                // indexed independently of sort
                indexObj = ((SortDependingFunction) indexObj).getKind();
            } else if (indexObj instanceof ElementaryUpdate) {
                indexObj = ElementaryUpdate.class;
            }
        }

        if (indexObj instanceof SchemaVariable) {
            if ((indexObj instanceof TermSV && ((TermSV) indexObj).isStrict())
                    || indexObj instanceof FormulaSV || indexObj instanceof UpdateSV) {

                indexObj = ((SchemaVariable) indexObj).sort();

                if (indexObj instanceof GenericSort) {
                    indexObj = GenericSort.class;
                }
            } else if (indexObj instanceof ProgramSV) {
                indexObj = DEFAULT_PROGSV_KEY;
            } else {
                indexObj = DEFAULT_SV_KEY;
            }
        }
        return indexObj;
    }


    private void insertToMap(NoPosTacletApp tacletApp,
            HashMap<Object, ImmutableList<NoPosTacletApp>> map) {
        Object indexObj = getIndexObj((FindTaclet) tacletApp.taclet());
        ImmutableList<NoPosTacletApp> opList = map.get(indexObj);
        if (opList == null) {
            opList = ImmutableSLList.<NoPosTacletApp>nil().prepend(tacletApp);
        } else {
            opList = opList.prepend(tacletApp);
        }
        map.put(indexObj, opList);
    }


    private void removeFromMap(NoPosTacletApp tacletApp,
            HashMap<Object, ImmutableList<NoPosTacletApp>> map) {
        Object op = getIndexObj((FindTaclet) tacletApp.taclet());
        ImmutableList<NoPosTacletApp> opList = map.get(op);
        if (opList != null) {
            opList = opList.removeAll(tacletApp);
            if (opList.isEmpty()) {
                map.remove(op);
            } else {
                map.put(op, opList);
            }
        }
    }

    /**
     * adds a set of NoPosTacletApp to this index
     *
     * @param tacletAppList the NoPosTacletApps to be added
     */
    public void addTaclets(Iterable<NoPosTacletApp> tacletAppList) {
        for (NoPosTacletApp taclet : tacletAppList) {
            add(taclet);
        }
    }

    public static ImmutableSet<NoPosTacletApp> toNoPosTacletApp(Iterable<Taclet> rule) {
        ImmutableList<NoPosTacletApp> result = ImmutableSLList.nil();
        for (Taclet t : rule) {
            result = result.prepend(NoPosTacletApp.createNoPosTacletApp(t));
        }
        return DefaultImmutableSet.fromImmutableList(result);
    }

    /**
     * adds a new Taclet with instantiation information to this index. If rule instance is not known
     * rule is not added
     *
     * @param taclet the Taclet and its instantiation info to be added
     */
    public void add(Taclet taclet) {
        add(NoPosTacletApp.createNoPosTacletApp(taclet));
    }

    /**
     * adds a new Taclet with instantiation information to this index. If rule instance is not known
     * rule is not added
     *
     * @param tacletApp the Taclet and its instantiation info to be added
     */
    public void add(NoPosTacletApp tacletApp) {
        Taclet taclet = tacletApp.taclet();
        if (taclet instanceof RewriteTaclet) {
            insertToMap(tacletApp, rwList);
        } else if (taclet instanceof AntecTaclet) {
            insertToMap(tacletApp, antecList);
        } else if (taclet instanceof SuccTaclet) {
            insertToMap(tacletApp, succList);
        } else if (taclet instanceof NoFindTaclet) {
            noFindList = noFindList.prepend(tacletApp);
        } else {
            // should never be reached
            Debug.fail("Tried to add an unknown type of Taclet");
        }

        if (tacletApp.instantiations() != SVInstantiations.EMPTY_SVINSTANTIATIONS) {
            partialInstantiatedRuleApps.add(tacletApp);
        }
    }

    /**
     * removes the given NoPosTacletApps from this index
     *
     * @param tacletAppList the NoPosTacletApps to be removed
     */
    public void removeTaclets(Iterable<NoPosTacletApp> tacletAppList) {
        for (final NoPosTacletApp tacletApp : tacletAppList) {
            remove(tacletApp);
        }
    }


    /**
     * removes a Taclet with the given instantiation information from this index.
     *
     * @param tacletApp the Taclet and its instantiation info to be removed
     */
    public void remove(NoPosTacletApp tacletApp) {
        Taclet rule = tacletApp.taclet();
        if (rule instanceof RewriteTaclet) {
            removeFromMap(tacletApp, rwList);
        } else if (rule instanceof AntecTaclet) {
            removeFromMap(tacletApp, antecList);
        } else if (rule instanceof SuccTaclet) {
            removeFromMap(tacletApp, succList);
        } else if (rule instanceof NoFindTaclet) {
            noFindList = noFindList.removeAll(tacletApp);
        } else {
            // should never be reached
            Debug.fail("Tried to remove an unknown type of Taclet");
        }

        if (tacletApp.instantiations() != SVInstantiations.EMPTY_SVINSTANTIATIONS) {
            // Debug.assertTrue(partialInstantiatedRuleApps.contains(tacletApp));
            partialInstantiatedRuleApps.remove(tacletApp);
        }
    }

    /** copies the index */
    public abstract TacletIndex copy();

    /** clones the index */
    @Override
    public Object clone() {
        return this.copy();
    }

    private void addToSet(ImmutableList<NoPosTacletApp> list, Set<NoPosTacletApp> result) {
        for (NoPosTacletApp tacletApp : list) {
            result.add(tacletApp);
        }
    }



    public Set<NoPosTacletApp> allNoPosTacletApps() {
        Set<NoPosTacletApp> result = new LinkedHashSet<>();
        for (ImmutableList<NoPosTacletApp> tacletApps : rwList.values()) {
            addToSet(tacletApps, result);
        }

        for (ImmutableList<NoPosTacletApp> tacletApps : antecList.values()) {
            addToSet(tacletApps, result);
        }

        for (ImmutableList<NoPosTacletApp> tacletApps : succList.values()) {
            addToSet(tacletApps, result);
        }

        addToSet(noFindList, result);

        return result;
    }

    /**
     * returns a list of Taclets and instantiations from the given list of taclets with respect to
     * term and the filter object.
     *
     * @param services the Services object encapsulating information about the java datastructures
     *        like (static)types etc.
     */
    private ImmutableList<NoPosTacletApp> getFindTaclet(ImmutableList<NoPosTacletApp> taclets,
            RuleFilter filter, PosInOccurrence pos, Services services) {
        return matchTaclets(taclets, filter, pos, services);
    }

    /**
     * Filter the given list of taclet apps, and match their find parts at the given position of the
     * sequent
     */
    protected abstract ImmutableList<NoPosTacletApp> matchTaclets(
            ImmutableList<NoPosTacletApp> tacletApps, final RuleFilter p_filter,
            final PosInOccurrence pos, final Services services);

    /**
     * returns a selection from the given map with NoPosTacletApps relevant for the given program
     * element. Occurring prefix elements are tracked and taclet applications for them are added.
     *
     * @param map the map to select the NoPosTacletApps from
     * @param pe the program element that is used to retrieve the taclets
     * @param prefixOcc the PrefixOccurrence object used to keep track of the occuring prefix
     *        elements
     */
    private ImmutableList<NoPosTacletApp> getJavaTacletList(
            HashMap<Object, ImmutableList<NoPosTacletApp>> map, ProgramElement pe,
            PrefixOccurrences prefixOccurrences) {
        ImmutableList<NoPosTacletApp> res = ImmutableSLList.nil();
        if (pe instanceof ProgramPrefix) {
            int next = prefixOccurrences.occurred(pe);
            NonTerminalProgramElement nt = (NonTerminalProgramElement) pe;
            if (next < nt.getChildCount()) {
                return getJavaTacletList(map, nt.getChildAt(next), prefixOccurrences);
            }
        } else {
            final ImmutableList<NoPosTacletApp> apps = map.get(pe.getClass());
            if (apps != null) {
                res = apps;
            }
        }
        return merge(res, prefixOccurrences.getList(map));
    }

    @SuppressWarnings("deprecation")
    private ImmutableList<NoPosTacletApp> getListHelp(
            final HashMap<Object, ImmutableList<NoPosTacletApp>> map, final Term term,
            final boolean ignoreUpdates, final PrefixOccurrences prefixOccurrences) {

        ImmutableList<NoPosTacletApp> res = ImmutableSLList.nil();
        final Operator op = term.op();

        assert !(op instanceof de.uka.ilkd.key.strategy.quantifierHeuristics.Metavariable)
                : "metavariables are disabled";

        if (!term.javaBlock().isEmpty()) {
            prefixOccurrences.reset();
            final StatementBlock sb = (StatementBlock) term.javaBlock().program();
            res = getJavaTacletList(map, sb.getStatementAt(0), prefixOccurrences);
        }

        if (!term.javaBlock().isEmpty() || op instanceof ProgramVariable) {
            res = merge(res, map.get(DEFAULT_PROGSV_KEY));
        }

        final ImmutableList<NoPosTacletApp> inMap;

        if (op instanceof SortDependingFunction) {
            inMap = map.get(((SortDependingFunction) op).getKind());
        } else if (op instanceof ElementaryUpdate) {
            inMap = map.get(ElementaryUpdate.class);
        } else {
            inMap = map.get(op);
        }

        res = merge(res, inMap);

        // collect taclets for target term, if updates shall be ignored
        if (ignoreUpdates && op instanceof UpdateApplication) {
            final Term target = UpdateApplication.getTarget(term);
            if (!(target.op() instanceof UpdateApplication)) {
                final ImmutableList<NoPosTacletApp> targetIndexed =
                    getListHelp(map, target, false, prefixOccurrences);
                return merge(res, targetIndexed);// otherwise only duplicates are added
            }
        }

        res = merge(res, map.get(term.sort()));
        res = merge(res, map.get(DEFAULT_SV_KEY));

        return merge(res, map.get(GenericSort.class));
    }

    /**
     * merges the two list in an execution time optimal manner
     *
     * @param first the first list
     * @param second the second list
     * @return the merged list
     */
    private final ImmutableList<NoPosTacletApp> merge(ImmutableList<NoPosTacletApp> first,
            final ImmutableList<NoPosTacletApp> second) {
        if (second == null) {
            return first;
        } else if (first == null) {
            return second;
        } else {
            if (second.size() < first.size()) {
                return first.prependReverse(second);
            } else {
                return second.prependReverse(first);
            }
        }
    }

    /**
     * creates and returns a selection from the given map of NoPosTacletApps that are compatible
     * with the given term. It is assumed that the map (key -> value mapping) (1) contains keys with
     * the top operator of its value, if no java block is involved on top level of the value and no
     * update is on top level (2) contains keys with the class of its top Java operator of its
     * value's java block, if a java block is involved on the top level (3) contains keys with the
     * special 'operators' PROGSVOP and DEFAULTSVOP if the top Java operator or top operator (resp.)
     * of the value is a program (or variable, resp.) schema variable. (4) contains keys with the
     * sort of the value if this is an other schema variable. If updates are on top level, they are
     * ignored; and indexing starts on the first level beneath updates.
     *
     * @param map the map from where to select the taclets
     * @param term the term that is used to find the selection
     */
    private ImmutableList<NoPosTacletApp> getList(
            HashMap<Object, ImmutableList<NoPosTacletApp>> map, Term term, boolean ignoreUpdates) {
        return getListHelp(map, term, ignoreUpdates, new PrefixOccurrences());
    }

    /**
     * get all Taclets for the antecedent.
     *
     * @param pos the PosOfOccurrence describing the formula for which to look for top level taclets
     * @param filter Only return taclets the filter selects
     * @param services the Services object encapsulating information about the java datastructures
     *        like (static)types etc.
     * @return IList<NoPosTacletApp> containing all applicable rules and the corresponding
     *         instantiations to get the rule fit.
     */
    public ImmutableList<NoPosTacletApp> getAntecedentTaclet(PosInOccurrence pos, RuleFilter filter,
            Services services) {
        return getTopLevelTaclets(antecList, filter, pos, services);
    }

    /**
     * get all Taclets for the succedent.
     *
     * @param pos the PosOfOccurrence describing the formula for which to look for top level taclets
     * @param filter Only return taclets the filter selects
     * @param services the Services object encapsulating information about the java datastructures
     *        like (static)types etc.
     * @return IList<NoPosTacletApp> containing all applicable rules and the corresponding
     *         instantiations to get the rule fit.
     */
    public ImmutableList<NoPosTacletApp> getSuccedentTaclet(PosInOccurrence pos, RuleFilter filter,
            Services services) {

        return getTopLevelTaclets(succList, filter, pos, services);
    }

    private ImmutableList<NoPosTacletApp> getTopLevelTaclets(
            HashMap<Object, ImmutableList<NoPosTacletApp>> findTaclets, RuleFilter filter,
            PosInOccurrence pos, Services services) {

        assert pos.isTopLevel();

        final ImmutableList<NoPosTacletApp> rwTaclets =
            getFindTaclet(getList(rwList, pos.subTerm(), true), filter, pos, services);
        final ImmutableList<NoPosTacletApp> seqTaclets =
            getFindTaclet(getList(findTaclets, pos.subTerm(), true), filter, pos, services);
        return rwTaclets.size() > 0 ? rwTaclets.prependReverse(seqTaclets)
                : seqTaclets.prependReverse(rwTaclets);
    }


    /**
     * get all Rewrite-Taclets.
     *
     * @param filter Only return taclets the filter selects
     * @param services the Services object encapsulating information about the java datastructures
     *        like (static)types etc.
     * @return IList<NoPosTacletApp> containing all applicable rules and the corresponding
     *         instantiations to get the rule fit.
     */
    public ImmutableList<NoPosTacletApp> getRewriteTaclet(PosInOccurrence pos, RuleFilter filter,
            Services services) {
        ImmutableList<NoPosTacletApp> result =
            matchTaclets(getList(rwList, pos.subTerm(), false), filter, pos, services);
        return result;
    }


    /**
     * get all Taclets having no find expression.
     *
     * @param filter Only return taclets the filter selects
     * @param services the Services object encapsulating information about the java datastructures
     *        like (static)types etc.
     * @return IList<NoPosTacletApp> containing all applicable rules and an empty part for the
     *         instantiations because no instantiations are necessary.
     */
    public ImmutableList<NoPosTacletApp> getNoFindTaclet(RuleFilter filter, Services services) {
        return matchTaclets(noFindList, filter, null, services);
    }


    /**
     * returns a NoPosTacletApp whose Taclet has a name that equals the given name. If more Taclets
     * have the same name an arbitrary Taclet with that name is returned.
     *
     * @param name the name to lookup
     * @return the found NoPosTacletApp or null if no matching Taclet is there
     */
    public NoPosTacletApp lookup(Name name) {
        for (NoPosTacletApp tacletApp : allNoPosTacletApps()) {
            if (tacletApp.taclet().name().equals(name)) {
                return tacletApp;
            }
        }
        return null;
    }


    /**
     * returns a NoPosTacletApp whose Taclet has a name that equals the given name. If more Taclets
     * have the same name an arbitrary Taclet with that name is returned.
     *
     * @param name the name to lookup
     * @return the found NoPosTacletApp or null if no matching Taclet is there
     */
    public @Nullable NoPosTacletApp lookup(String name) {
        return lookup(new Name(name));
    }

    /**
     * returns a list with all partial instantiated no pos taclet apps
     *
     * @return list with all partial instantiated NoPosTacletApps
     */
    public ImmutableList<NoPosTacletApp> getPartialInstantiatedApps() {
        ImmutableList<NoPosTacletApp> result = ImmutableSLList.nil();
        for (NoPosTacletApp partialInstantiatedRuleApp : partialInstantiatedRuleApps) {
            result = result.prepend(partialInstantiatedRuleApp);
        }
        return result;
    }


    @Override
    public String toString() {
        String sb = "TacletIndex with applicable rules: " +
            "ANTEC\n " + antecList +
            "\nSUCC\n " + succList +
            "\nREWRITE\n " + rwList +
            "\nNOFIND\n " + noFindList;
        return sb;
    }


    /**
     * Inner class to track the occurrences of prefix elements in java blocks
     */
    private static class PrefixOccurrences {

        /**
         * the classes that represent prefix elements of a java block
         */
        static final Class<?>[] prefixClasses =
            new Class<?>[] { StatementBlock.class, LabeledStatement.class, Try.class,
                MethodFrame.class, SynchronizedBlock.class, LoopScopeBlock.class, Exec.class };

        /**
         * number of prefix types
         */
        static final int PREFIXTYPES = prefixClasses.length;

        /**
         * field that marks iff the prefix elements have already occurred
         */
        private final boolean[] occurred = new boolean[PREFIXTYPES];

        /**
         * fields to indicate the position of the next relevant child (the next possible prefix
         * element or real statement
         */
        static final int[] nextChild = new int[] { 0, 1, 0, 1, 1, 1, 0 };

        PrefixOccurrences() {
            reset();
        }

        /**
         * resets the occurred field to 'nothing has occurred'
         */
        public void reset() {
            for (int i = 0; i < PREFIXTYPES; i++) {
                occurred[i] = false;
            }
        }

        /**
         * notification that the given program element has occurred. The occurred fields are
         * subsequently set.
         *
         * @param pe the occurred program element
         * @return the number of the next possible prefix element
         */
        public int occurred(ProgramElement pe) {
            for (int i = 0; i < PREFIXTYPES; i++) {
                if (prefixClasses[i].isInstance(pe)) {
                    occurred[i] = true;
                    if (pe instanceof MethodFrame) {
                        return (((MethodFrame) pe).getProgramVariable() == null) ? 1 : 2;
                    } else {
                        return nextChild[i];
                    }
                }
            }
            return -1;
        }

        /**
         * creates a selection of the given NoPosTacletApp map that comply with the occurred prefix
         * elements
         *
         * @param map a map to select from
         */
        public ImmutableList<NoPosTacletApp> getList(
                HashMap<Object, ImmutableList<NoPosTacletApp>> map) {
            ImmutableList<NoPosTacletApp> result = ImmutableSLList.nil();
            for (int i = 0; i < PREFIXTYPES; i++) {
                if (occurred[i]) {
                    ImmutableList<NoPosTacletApp> inMap = map.get(prefixClasses[i]);
                    if (inMap != null) {
                        result = result.prepend(inMap);
                    }
                }
            }
            return result;
        }
    }
}
