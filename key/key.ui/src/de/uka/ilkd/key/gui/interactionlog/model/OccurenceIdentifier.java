package de.uka.ilkd.key.gui.interactionlog.model;

import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.proof.Goal;

import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlRootElement;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (09.12.18)
 */
@XmlRootElement
@XmlAccessorType(XmlAccessType.FIELD)
public class OccurenceIdentifier {
    @XmlAttribute
    private Integer[] path;
    @XmlAttribute
    private String subTerm;
    @XmlAttribute
    private String toplevelTerm;
    @XmlAttribute
    private int termHash;
    @XmlAttribute
    private boolean antec;

    public OccurenceIdentifier() {
    }

    public static OccurenceIdentifier get(PosInOccurrence p) {
        if (p == null)
            return new OccurenceIdentifier();

        List<Integer> indices = new ArrayList<>();
        PIOPathIterator iter = p.iterator();
        while (iter.next() != -1) {
            indices.add(iter.getChild());
        }

        OccurenceIdentifier occ = new OccurenceIdentifier();
        occ.path = indices.toArray(new Integer[0]);
        occ.subTerm = iter.getSubTerm().toString();
        occ.termHash = iter.getSubTerm().hashCode();
        occ.toplevelTerm = p.topLevel().subTerm().toString();
        occ.antec = p.isInAntec();
        return occ;
    }

    public Integer[] getPath() {
        return path;
    }

    public void setPath(Integer[] path) {
        this.path = path;
    }

    public String getTerm() {
        return subTerm;
    }

    public void setTerm(String term) {
        this.subTerm = term;
    }

    public int getTermHash() {
        return termHash;
    }

    public void setTermHash(int termHash) {
        this.termHash = termHash;
    }

    public boolean isAntec() {
        return antec;
    }

    public void setAntec(boolean antec) {
        this.antec = antec;
    }

    public String getToplevelTerm() {
        return toplevelTerm;
    }

    public void setToplevelTerm(String toplevelTerm) {
        this.toplevelTerm = toplevelTerm;
    }

    @Override
    public String toString() {
        if (path == null) {
            return " @toplevel";
        }
        if (path.length != 0) {
            return getTerm() + " under " + getToplevelTerm() + "(Path: " + Arrays.toString(path) + ")";
        } else {
            return getTerm() + " @toplevel";
        }
    }

    public PosInOccurrence rebuildOn(Goal goal) {
        Sequent seq = goal.node().sequent();
        return rebuildOn(seq);
    }

    private PosInOccurrence rebuildOn(Sequent seq) {
        //TODO
        return null;
    }
}
