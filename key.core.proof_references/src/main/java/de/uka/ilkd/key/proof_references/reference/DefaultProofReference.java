/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof_references.reference;

import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.Objects;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

/**
 * Default implementation of {@link IProofReference}.
 *
 * @author Martin Hentschel
 */
public class DefaultProofReference<T> implements IProofReference<T> {
    /**
     * The reference kind as human readable {@link String}.
     */
    private final String kind;

    /**
     * The source {@link Proof}.
     */
    private final Proof source;

    /**
     * The target source member.
     */
    private final T target;

    /**
     * The {@link Node} in which the reference was found.
     */
    private final LinkedHashSet<Node> nodes = new LinkedHashSet<>();

    /**
     * Constructor
     *
     * @param kind The reference kind as human readable {@link String}.
     * @param source The source {@link Proof}.
     * @param target The target source member.
     */
    public DefaultProofReference(String kind, Node node, T target) {
        this.kind = kind;
        this.source = node != null ? node.proof() : null;
        this.target = target;
        this.nodes.add(node);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T getTarget() {
        return target;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public LinkedHashSet<Node> getNodes() {
        return nodes;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void addNodes(Collection<Node> nodes) {
        this.nodes.addAll(nodes);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getKind() {
        return kind;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Proof getSource() {
        return source;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean equals(Object obj) {
        if (obj instanceof IProofReference<?>) {
            IProofReference<?> other = (IProofReference<?>) obj;
            return Objects.equals(getKind(), other.getKind())
                    && Objects.equals(getSource(), other.getSource())
                    && Objects.equals(getTarget(), other.getTarget());
        } else {
            return false;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        int result = 17;
        result = 31 * result + (getKind() != null ? getKind().hashCode() : 0);
        result = 31 * result + (getSource() != null ? getSource().hashCode() : 0);
        result = 31 * result + (getTarget() != null ? getTarget().hashCode() : 0);
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(getKind());
        sb.append(" Proof Reference to \"");
        sb.append(getTarget());
        sb.append("\"");
        if (!getNodes().isEmpty()) {
            sb.append(" at node(s) ");
            boolean afterFirst = false;
            for (Node node : getNodes()) {
                if (afterFirst) {
                    sb.append(", ");
                } else {
                    afterFirst = true;
                }
                sb.append(node.serialNr());
            }
        }
        if (getSource() != null) {
            sb.append(" of proof \"");
            sb.append(getSource());
            sb.append("\"");
        }
        return sb.toString();
    }
}
