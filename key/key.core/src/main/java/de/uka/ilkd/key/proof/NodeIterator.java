package de.uka.ilkd.key.proof;

import java.util.Iterator;

class NodeIterator implements Iterator<Node> {

    private final Iterator<Node> it;

    NodeIterator(Iterator<Node> it) {
        this.it = it;
    }

    @Override
    public boolean hasNext() {
        return it.hasNext();
    }

    @Override
    public Node next() {
        return it.next();
    }

    @Override
    public void remove() {
        throw new UnsupportedOperationException("Changing the proof tree "
                + "structure this way is not allowed.");
    }
}
