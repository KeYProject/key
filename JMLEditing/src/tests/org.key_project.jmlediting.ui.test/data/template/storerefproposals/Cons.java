package org.key_project.jmlediting.ui.test.completion;

public class Cons<T> {
   
   public T elem;
   public Cons<T> next;
   protected int id;
   private int privateId;
   
   public Cons(T elem, Cons<T> next) {
      this.elem = elem;
      this.next = next;
   }
   
   public Cons(T elem) {
      this.elem = elem;
      this.next = null;
   }

}
