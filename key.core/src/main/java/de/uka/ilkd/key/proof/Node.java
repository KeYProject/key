/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import java.util.*;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;

import de.uka.ilkd.key.logic.RenamingTable;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentChangeInfo;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.proof.reference.ClosedBy;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.merge.MergeRule;
import de.uka.ilkd.key.util.Pair;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.lookup.Lookup;

public class Node implements Iterable<Node> {
    private static final String RULE_WITHOUT_NAME = "rule without name";

    private static final String RULE_APPLICATION_WITHOUT_RULE = "rule application without rule";

    private static final String INTERACTIVE_GOAL = "INTERACTIVE GOAL";

    private static final String LINKED_GOAL = "LINKED GOAL";

    private static final String OPEN_GOAL = "OPEN GOAL";

    private static final String CLOSED_GOAL = "Closed goal";
    private static final String CACHED_GOAL = "Closed goal (via cache)";

    private static final String NODES = "nodes";

    /** the proof the node belongs to */
    private final Proof proof;

    /** The parent node. **/
    private Node parent = null;
    /**
     * The branch location of this proof node.
     */
    private BranchLocation branchLocation = null;

    private Sequent seq = Sequent.EMPTY_SEQUENT;

    private final ArrayList<Node> children = new ArrayList<>(1);

    private RuleApp appliedRuleApp;

    private NameRecorder nameRecorder;

    /**
     * a linked list of the locally generated program variables. It extends the list of the parent
     * node.
     */
    private ImmutableList<IProgramVariable> localProgVars = ImmutableSLList.nil();

    /**
     * a linked list of the locally generated function symbols. It extends the list of the parent
     * node.
     */
    private ImmutableList<Function> localFunctions = ImmutableSLList.nil();

    private boolean closed = false;

    /** contains non-logical content, used for user feedback */
    private NodeInfo nodeInfo;

    /**
     * Serial number of this proof node.
     * For each proof, serial numbers are assigned to nodes as they are created:
     * the first step is assigned number 0, the next step number 1, and so on.
     */
    private final int serialNr;

    /**
     * Step index of this proof node.
     * Unlike serial numbers, the step index increases by one for each node in the proof tree
     * when visited in a depth-first order.
     * Only valid after {@link Proof#setStepIndices()} is called!
     */
    private int stepIndex = 0;

    /**
     * Sibling number of this proof node.
     * If the {@link #parent()} proof node has more than one child node,
     * each child node receives an index (starting at 0, incrementing by 1 for each sibling).
     */
    private int siblingNr = -1;

    private ImmutableList<RenamingTable> renamings;

    private String cachedName = null;

    @Nullable
    private Lookup userData = null;


    /**
     * If the rule base has been extended e.g. by loading a new taclet as lemma or by applying a
     * taclet with an addrule section on this node, then these taclets are stored in this list
     */
    private ImmutableSet<NoPosTacletApp> localIntroducedRules =
        DefaultImmutableSet.nil();

    /**
     * Holds the undo methods for the information added by rules to the {@link Goal#strategyInfos}.
     */
    private final List<StrategyInfoUndoMethod> undoInfoForStrategyInfo = new ArrayList<>();


    /**
     * creates an empty node that is root and leaf.
     */
    public Node(Proof proof) {
        this.proof = proof;
        serialNr = proof.getServices().getCounter(NODES).getCountPlusPlus();
        nodeInfo = new NodeInfo(this);
    }

    /**
     * creates a node with the given contents and associated proof
     */
    public Node(Proof proof, Sequent seq) {
        this(proof);
        this.seq = seq;
    }

    /**
     * creates a node with the given contents, the given collection of children (all elements must
     * be of class Node) and the given parent node.
     */
    public Node(Proof proof, Sequent seq, Node parent) {
        this(proof, seq);
        this.parent = parent;
        this.localFunctions = parent.localFunctions;
        this.localProgVars = parent.localProgVars;
    }

    /**
     * sets the sequent at this node
     */
    public void setSequent(Sequent seq) {
        this.seq = seq;
    }

    /** returns the sequent of this node */
    public Sequent sequent() {
        return seq;
    }

    /**
     * the node information object encapsulates non-logical information of the node, e.g.
     *
     * @return the NodeInfo containing non-logical information
     */
    public NodeInfo getNodeInfo() {
        return nodeInfo;
    }

    /** returns the proof the Node belongs to */
    public Proof proof() {
        return proof;
    }

    public void setAppliedRuleApp(RuleApp ruleApp) {
        this.nodeInfo.updateNoteInfo();
        this.appliedRuleApp = ruleApp;
        clearNameCache();
    }

    public void clearNameCache() {
        cachedName = null;
    }

    /**
     * When pruning, data referring to future nodes has to be cleared; however, the sequent change
     * info and the relevant files are related to the parent node, and have to be preserved.
     */
    void clearNodeInfo() {
        if (this.nodeInfo != null) {
            SequentChangeInfo oldSeqChangeInfo = this.nodeInfo.getSequentChangeInfo();
            this.nodeInfo = new NodeInfo(this);
            this.nodeInfo.setSequentChangeInfo(oldSeqChangeInfo);
        } else {
            this.nodeInfo = new NodeInfo(this);
        }
    }

    public NameRecorder getNameRecorder() {
        return nameRecorder;
    }

    public void setNameRecorder(NameRecorder rec) {
        nameRecorder = rec;
    }

    public void setRenamings(ImmutableList<RenamingTable> list) {
        renamings = list;
    }

    public ImmutableList<RenamingTable> getRenamingTable() {
        return renamings;
    }

    public RuleApp getAppliedRuleApp() {
        return appliedRuleApp;
    }

    /** Returns the set of NoPosTacletApps at this node */
    public Iterable<NoPosTacletApp> getLocalIntroducedRules() {
        return localIntroducedRules;
    }

    /**
     * Returns the set of created program variables known in this node.
     *
     * In the resulting list, the newest additions come first.
     *
     * @returns a non-null immutable list of program variables.
     */
    public ImmutableList<IProgramVariable> getLocalProgVars() {
        return localProgVars;
    }

    public void addLocalProgVars(Iterable<? extends IProgramVariable> elements) {
        for (IProgramVariable pv : elements) {
            localProgVars = localProgVars.prepend(pv);
        }
    }

    /**
     * Returns the set of freshly created function symbols known to this node.
     *
     * In the resulting list, the newest additions come first.
     *
     * @return a non-null immutable list of function symbols.
     */
    public Iterable<Function> getLocalFunctions() {
        return localFunctions;
    }

    public void addLocalFunctions(Collection<? extends Function> elements) {
        for (Function op : elements) {
            localFunctions = localFunctions.prepend(op);
        }
    }

    /**
     * adds a new NoPosTacletApp to the set of available NoPosTacletApps at this node
     *
     * @param s the app to add.
     */
    public void addNoPosTacletApp(NoPosTacletApp s) {
        localIntroducedRules = localIntroducedRules.add(s);
    }

    /**
     * @return the parent node of this node.
     */
    public Node parent() {
        return parent;
    }

    /**
     * @return true iff this node is a leaf, i.e., has no children.
     */
    public boolean leaf() {
        return children.isEmpty();
    }

    /**
     * Searches for a given node in the subtree starting with this node.
     *
     * @return {@code true} iff the node was found.
     */
    public boolean find(Node node) {
        // we assume that the proof tree node is part of has proper
        // links

        while (node != this) {
            if (node.root()) {
                return false;
            }
            node = node.parent();
        }

        return true;
    }

    /**
     * Search for the root of the smallest subtree containing <code>this</code> and
     * <code>other</code>; we assume that the two nodes are part of the same proof tree
     *
     * @param other a node.
     * @return the most recent common ancestor of {@code this} and the specified node.
     */
    public Node commonAncestor(Node other) {
        if (root()) {
            return this;
        }
        if (other.root()) {
            return other;
        }

        HashSet<Node> paths = new LinkedHashSet<>();
        Node n = this;

        while (true) {
            if (!paths.add(n)) {
                return n;
            }
            if (n.root()) {
                break;
            }
            n = n.parent();

            if (!paths.add(other)) {
                return other;
            }
            if (other.root()) {
                other = n;
                break;
            }
            other = other.parent();
        }

        while (!paths.contains(other)) {
            other = other.parent();
        }

        return other;
    }

    /**
     * @return true iff this node is the root, i.e., has no parents.
     */
    public boolean root() {
        return parent == null;
    }

    public Statistics statistics() {
        return new Statistics(this);
    }

    /**
     * Makes the given node a child of this node.
     *
     * @param newChild the node to make a child of this node.
     */
    public void add(Node newChild) {
        newChild.siblingNr = children.size();
        children.add(newChild);
        newChild.parent = this;
        proof().fireProofExpanded(this);
    }

    /**
     * Makes the given node children of this node.
     *
     * @param newChildren the node to make into children of this node.
     */
    public void addAll(Node[] newChildren) {
        final int size = children.size();
        for (int i = 0; i < newChildren.length; i++) {
            newChildren[i].siblingNr = i + size;
            newChildren[i].parent = this;
        }

        Collections.addAll(children, newChildren);
        children.trimToSize();

        proof().fireProofExpanded(this);
    }

    /**
     * Removes child/parent relationship between this node and its parent; if this node is root
     * nothing happens. This is only used for testing purposes.
     */
    void remove() {
        if (parent != null) {
            parent.remove(this);
        }
    }

    /**
     * Removes child/parent relationship between the given node and this node; if the given node is
     * not child of this node, nothing happens and then and only then false is returned.
     *
     * @param child the child to remove.
     * @return false iff the given node was not child of this node and nothing has been done.
     */
    boolean remove(Node child) {
        if (children.remove(child)) {
            child.parent = null;
            final ListIterator<Node> it = children.listIterator(child.siblingNr);
            while (it.hasNext()) {
                it.next().siblingNr--;
            }
            child.siblingNr = -1;
            return true;
        } else {
            return false;
        }
    }

    /**
     * Computes the leaves of the current subtree and returns them.
     *
     * @return the leaves of the current subtree.
     */
    List<Node> getLeaves() {
        final List<Node> leaves = new LinkedList<>();
        final LinkedList<Node> nodesToCheck = new LinkedList<>();
        nodesToCheck.add(this);
        do {
            final Node n = nodesToCheck.poll();
            if (n.leaf()) {
                leaves.add(n);
            } else {
                nodesToCheck.addAll(0, n.children);
            }
        } while (!nodesToCheck.isEmpty());
        return leaves;
    }

    /**
     * @return an iterator for the leaves of the subtree below this node. The computation is called
     *         at every call!
     */
    public Iterator<Node> leavesIterator() {
        return new NodeIterator(getLeaves().iterator());
    }

    /**
     * @return an iterator for the direct children of this node.
     */
    public Iterator<Node> childrenIterator() {
        return new NodeIterator(children.iterator());
    }

    /**
     * @return an iterator for all nodes in the subtree.
     */
    public Iterator<Node> subtreeIterator() {
        return new SubtreeIterator(this);
    }


    /**
     * @return an iterator for all nodes in the subtree.
     */
    public Stream<Node> subtreeStream() {
        var children = StreamSupport.stream(
            Spliterators.spliteratorUnknownSize(subtreeIterator(), Spliterator.ORDERED), false);
        return Stream.concat(Stream.of(this), children);
    }


    /** @return number of children */
    public int childrenCount() {
        return children.size();
    }

    /**
     *
     * @param i an index (starting at 0).
     * @return the i-th child of this node.
     */
    public Node child(int i) {
        return children.get(i);
    }

    /**
     * @param child a child of this node.
     * @return the number of the node <code>child</code>, if it is a child of this node (starting
     *         with <code>0</code>), <code>-1</code> otherwise
     */
    public int getChildNr(Node child) {
        int res = 0;
        final Iterator<Node> it = childrenIterator();

        while (it.hasNext()) {
            if (it.next() == child) {
                return res;
            }
            ++res;
        }

        return -1;
    }

    public StringBuffer getUniqueTacletId() {
        StringBuffer id = new StringBuffer();
        int c = 0;
        Node n = this;

        while (n != null) {
            c += n.localIntroducedRules.size();

            if (n.parent != null && n.parent.childrenCount() > 1) {
                id.append(n.siblingNr);
            }

            n = n.parent;
        }

        id.append("_").append(c);

        return id;
    }

    /**
     * Helper for {@link #toString()}
     *
     * @param prefix needed to keep track if a line has to be printed
     * @param tree the tree representation we want to add this subtree " @param preEnumeration the
     *        enumeration of the parent without the last number
     * @param postNr the last number of the parents enumeration
     * @param maxNr the number of nodes at this level
     * @param ownNr the place of this node at this level
     * @return the string representation of this node.
     */

    private StringBuffer toString(String prefix, StringBuffer tree, String preEnumeration,
            int postNr, int maxNr, int ownNr) {
        Iterator<Node> childrenIt = childrenIterator();
        // Some constants
        String frontIndent = (maxNr > 1 ? " " : "");
        String backFill = "   "; // same length as connectNode without
        // frontIndent
        String connectNode = (maxNr > 1 ? frontIndent + "+--" : "");
        String verticalLine = (maxNr > 1 ? frontIndent + "|" + backFill : " |");

        // get enumeration
        String newEnumeration = preEnumeration;
        int newPostNr = 0;
        if (maxNr > 1) {
            newEnumeration += postNr + "." + ownNr + ".";
            newPostNr = 1;
        } else {
            newPostNr = postNr + ownNr;
        }

        // node is printed

        if (postNr != 0) { // not starting node (usually not root)
            // prefix is appended twice in order to get an
            // empty line between two nodes
            tree.append(prefix);
            tree.append(verticalLine);
            tree.append("\n");
            tree.append(prefix);
            // indent node
            tree.append(connectNode);
        }

        tree.append("(").append(newEnumeration).append(newPostNr).append(") ")
                .append(sequent().toString()).append("\n");

        // create new prefix
        if (ownNr < maxNr) {
            // connect node with next node of same level
            prefix += verticalLine;
        } else if (ownNr == maxNr && maxNr > 1) {
            // last node of level no further connection
            prefix += frontIndent + " " + backFill;
        } else if (ownNr != maxNr && maxNr <= 1) {
            prefix = "";
        }

        // print subtrees
        int childId = 0;
        while (childrenIt.hasNext()) {
            childId++;
            childrenIt.next().toString(prefix, tree, newEnumeration, newPostNr, children.size(),
                childId);
        }

        return tree;
    }

    @Override
    public String toString() {
        StringBuffer tree = new StringBuffer();
        return "\n" + toString("", tree, "", 0, 0, 1);
    }

    public String name() {
        if (cachedName == null) {

            RuleApp rap = getAppliedRuleApp();
            if (rap == null) {
                final Goal goal = proof().getOpenGoal(this);
                if (this.isClosed() && lookup(ClosedBy.class) != null) {
                    cachedName = CACHED_GOAL;
                } else if (this.isClosed()) {
                    return CLOSED_GOAL; // don't cache this
                } else if (goal == null) {
                    // should never happen (please check)
                    return "UNKNOWN GOAL KIND (Probably a bug)";
                } else if (goal.isLinked()) {
                    cachedName = LINKED_GOAL;
                } else if (goal.isAutomatic()) {
                    cachedName = OPEN_GOAL;
                } else {
                    cachedName = INTERACTIVE_GOAL;
                }
                return cachedName;
            }

            if (rap.rule() == null) {
                cachedName = RULE_APPLICATION_WITHOUT_RULE;
                return cachedName;
            }

            if (nodeInfo.getFirstStatementString() != null) {
                return nodeInfo.getFirstStatementString();
            }

            cachedName = rap.displayName();
            if (cachedName == null) {
                cachedName = RULE_WITHOUT_NAME;
            }
        }
        return cachedName;
    }

    /**
     * Checks if the parent has this node as child and continues recursively with the children of
     * this node.
     *
     * @return true iff the parent of this node has this node as child and this condition holds also
     *         for the own children.
     */
    public boolean sanityCheckDoubleLinks() {
        if (!root()) {
            if (!parent().children.contains(this)) {
                return false;
            }
            if (parent.proof() != proof()) {
                return false;
            }
        }
        if (!leaf()) {
            final Iterator<Node> it = childrenIterator();
            while (it.hasNext()) {
                if (!it.next().sanityCheckDoubleLinks()) {
                    return false;
                }
            }
        }
        return true;
    }

    /** marks a node as closed */
    Node close() {
        closed = true;
        Node tmp = parent;
        Node result = this;
        while (tmp != null && tmp.isCloseable()) {
            tmp.closed = true;
            result = tmp;
            tmp = tmp.parent();
        }
        clearNameCache();
        return result;
    }

    /**
     * Opens a previously closed node and all its closed parents.
     * <p>
     *
     * This is, for instance, needed for the {@link MergeRule}: In a situation where a merge node
     * and its associated partners have been closed and the merge node is then pruned away, the
     * partners have to be reopened again. Otherwise, we have a soundness issue.
     */
    void reopen() {
        closed = false;
        Node tmp = parent;
        while (tmp != null && tmp.isClosed()) {
            tmp.closed = false;
            tmp = tmp.parent();
        }
        clearNameCache();
    }

    /** @return true iff this inner node is closeable */
    private boolean isCloseable() {
        assert childrenCount() > 0;
        for (Node child : children) {
            if (!child.isClosed()) {
                return false;
            }
        }
        return true;
    }

    public boolean isClosed() {
        return closed;
    }

    /**
     * @return number of nodes in the subtree below this node.
     */
    public int countNodes() {
        Iterator<Node> it = subtreeIterator();
        int res = 0;
        for (; it.hasNext(); it.next()) {
            res++;
        }
        return res;
    }

    /**
     * @return number of branches in the subtree below this node.
     */
    public int countBranches() {
        return getLeaves().size();
    }

    public int serialNr() {
        return serialNr;
    }

    /**
     * Returns the sibling number of this node or <tt>-1</tt> if it is the root node
     *
     * @return the sibling number of this node or <tt>-1</tt> if it is the root node
     */
    public int siblingNr() {
        return siblingNr;
    }

    public List<StrategyInfoUndoMethod> getStrategyInfoUndoMethods() {
        return undoInfoForStrategyInfo;
    }

    public void addStrategyInfoUndoMethod(StrategyInfoUndoMethod undoMethod) {
        undoInfoForStrategyInfo.add(undoMethod);
    }

    /**
     * Returns an iterator over this node's children. Use {@link #leavesIterator()} if you need to
     * iterate over leaves instead.
     *
     * @return iterator over children.
     */
    public Iterator<Node> iterator() {
        return childrenIterator();
    }

    /**
     * Retrieves a user-defined data.
     *
     * @param service the class for which the data were registered
     * @param <T> any class
     * @return null or the previous data
     * @see #register(Object, Class)
     */
    public <T> T lookup(Class<T> service) {
        try {
            if (userData == null) {
                return null;
            }
            return userData.get(service);
        } catch (IllegalStateException ignored) {
            return null;
        }
    }

    /**
     * Register a user-defined data in this node info.
     *
     * @param obj an object to be registered
     * @param service the key under it should be registered
     * @param <T>
     */
    public <T> void register(T obj, Class<T> service) {
        getUserData().register(obj, service);
    }

    /**
     * Remove a previous registered user-defined data.
     *
     * @param obj registered object
     * @param service the key under which the data was registered
     * @param <T> arbitray object
     */
    public <T> void deregister(T obj, Class<T> service) {
        if (userData != null) {
            userData.deregister(obj, service);
        }
    }

    /**
     * Get the assocated lookup of user-defined data.
     *
     * @return
     */
    public @Nonnull Lookup getUserData() {
        if (userData == null) {
            userData = new Lookup();
        }
        return userData;
    }

    public BranchLocation getBranchLocation() {
        if (branchLocation == null) {
            BranchLocation prev = parent != null ? parent.getBranchLocation() : BranchLocation.ROOT;
            if (parent != null && parent.children.size() > 1) {
                prev = prev.append(new Pair<>(parent, siblingNr));
            }
            this.branchLocation = prev;
        }
        return branchLocation;
    }

    public int getStepIndex() {
        return stepIndex;
    }

    void setStepIndex(int stepIndex) {
        this.stepIndex = stepIndex;
    }

    /**
     * Returns a stream over all direct children (excluding this node) using the
     * {@link #spliterator()}.
     */
    public Stream<Node> stream() {
        return StreamSupport.stream(spliterator(), false);
    }
}
