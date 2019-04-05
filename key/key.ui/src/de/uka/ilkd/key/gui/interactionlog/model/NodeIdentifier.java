package de.uka.ilkd.key.gui.interactionlog.model;

import de.uka.ilkd.key.gui.interactionlog.algo.LogPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import javax.xml.bind.annotation.*;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (06.12.18)
 */
@XmlRootElement
@XmlAccessorType(XmlAccessType.FIELD)
public class NodeIdentifier implements Serializable {
    @XmlElement(required = true, name = "select")
    private List<Integer> list = new ArrayList<>();

    @XmlAttribute
    private String branchLabel;

    @XmlTransient
    private int serialNr;

    public NodeIdentifier() {
    }

    public NodeIdentifier(List<Integer> seq) {
        this.list.addAll(seq);
    }

    public static NodeIdentifier get(Goal g) {
        return get(g.node());
    }

    public static NodeIdentifier get(Node node) {
        LinkedList<Integer> list = new LinkedList<>();
        do {
            Node parent = node.parent();
            if (parent != null) {
                list.add(0, parent.getChildNr(node));
            }
            node = parent;
        } while (node != null);
        NodeIdentifier ni = new NodeIdentifier(list);
        ni.setBranchLabel(LogPrinter.getBranchingLabel(node));
        return ni;
    }

    @Override
    public String toString() {
        return list.stream()
                .map(Object::toString)
                .collect(Collectors.joining(".")) + " => " + serialNr;
    }


    public List<Integer> getList() {
        return list;
    }

    public void setList(List<Integer> list) {
        this.list = list;
    }

    public Optional<Node> findNode(Proof proof) {
        return findNode(proof.root());
    }

    public Optional<Node> findNode(Node node) {
        for (int child : list) {
            if (child <= node.childrenCount()) {
                node = node.child(child);
            } else {
                return Optional.empty();
            }
        }
        return Optional.of(node);
    }

    public int getSerialNr() {
        return serialNr;
    }

    public void setSerialNr(int serialNr) {
        this.serialNr = serialNr;
    }

    public String getBranchLabel() {
        return branchLabel;
    }

    public void setBranchLabel(String branchLabel) {
        this.branchLabel = branchLabel;
    }
}
