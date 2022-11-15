package org.key_project.slicing.graph;

import de.uka.ilkd.key.proof.Node;
import org.jgrapht.graph.DefaultEdge;

import java.util.Objects;

/**
 * An edge of the dependency graph. Stores additional metadata.
 *
 * @author Arne Keller
 */
public class AnnotatedEdge extends DefaultEdge {
    /**
     * The node that added this edge to the dependency graph.
     */
    private final transient Node proofStep;
    /**
     * Whether the proof step consumes (replaces) the input formula.
     */
    private final boolean consumesInput;
    /**
     * Serial number used to differentiate annotated edges if the hyperedge has to be split up
     * into multiple instances of this class.
     */
    private final int serialNr;

    public AnnotatedEdge(Node proofStep, boolean consumesInput, int serialNr) {
        this.proofStep = proofStep;
        this.consumesInput = consumesInput;
        this.serialNr = serialNr;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }

        AnnotatedEdge that = (AnnotatedEdge) o;

        if (consumesInput != that.consumesInput || serialNr != that.serialNr) {
            return false;
        }
        return proofStep.equals(that.proofStep);
    }

    @Override
    public int hashCode() {
        int result = Objects.hash(proofStep, serialNr);
        result = 31 * result + (consumesInput ? 1 : 0);
        return result;
    }

    /**
     * The node that added this edge to the dependency graph.
     */
    public Node getProofStep() {
        return proofStep;
    }

    /**
     * Whether the proof step consumes (replaces) the input formula.
     */
    public boolean replacesInputNode() {
        return consumesInput;
    }
}
