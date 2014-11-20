package org.key_project.jmlediting.core.profile.persistence.impl;

import java.util.Iterator;

import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

public class NodeListIterable implements Iterable<Node> {

   private final NodeList list;

   private class NodeListIterator implements Iterator<Node> {

      private int index = 0;

      @Override
      public boolean hasNext() {
         return this.index < list.getLength();
      }

      @Override
      public Node next() {
         Node node = list.item(this.index);
         this.index++;
         return node;
      }

      @Override
      public void remove() {
         throw new UnsupportedOperationException(
               "Cannot remove node from NodeList");
      }

   }

   public NodeListIterable(final NodeList list) {
      if (list == null) {
         throw new NullPointerException("Cannot iterate over a null list");
      }
      this.list = list;
   }

   @Override
   public Iterator<Node> iterator() {
      return new NodeListIterator();
   }

}
