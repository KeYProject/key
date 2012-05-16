package de.uka.ilkd.key.symbolic_execution.util;

import java.util.Map.Entry;

public class DefaultEntry<K, V> implements Entry<K, V> {
   private K key;
   
   private V value;

   public DefaultEntry(K key, V value) {
      super();
      this.key = key;
      this.value = value;
   }

   @Override
   public K getKey() {
      return key;
   }

   @Override
   public V getValue() {
      return value;
   }

   @Override
   public V setValue(V value) {
      V oldValue = this.value;
      this.value = value;
      return oldValue;
   }
}
